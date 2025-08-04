const std = @import("std");

/// FwdFn: fat function pointer with optional owned storage (SBO).
/// Sig: exact function signature (no varargs).
/// MaxInline / MaxAlign: inline storage budget for functors.
pub fn FwdFn(comptime Sig: type, comptime MaxInline: usize, comptime MaxAlign: usize) type {
    const ArgsTuple = std.meta.ArgsTuple(Sig);
    const Ret = blk: {
        const TI = @typeInfo(Sig);
        if (TI == .Function) break :blk TI.Function.return_type.?;
        if (TI == .Fn)       break :blk TI.Fn.return_type.?;
        @compileError("FwdFn: Sig must be a function type");
    };
    const Invoker = fn (*anyopaque, ArgsTuple) Ret;

    const Storage = union(enum) {
        none,
        inline: struct { bytes: [MaxInline]u8 align(MaxAlign) },
        heap: *anyopaque,
    };

    return struct {
        pub const Self = @This();

        // -- dynamic call surface --
        invoker: *const Invoker = undefined,
        ctx: *anyopaque = undefined,

        // -- ownership / clone info (shallow copy) --
        storage: Storage = .none,
        size: usize = 0,
        align: u32 = 0,
        is_inline: bool = true,
        heap_alloc: ?std.mem.Allocator = null,

        // optional destructor specialized for the functor type
        dtor: ?*const fn (*anyopaque) void = null,

        // ================= lifecycle =================
        pub fn initNull() Self { return .{ .invoker = undefined, .ctx = undefined, .storage = .none }; }

        /// Idempotent. If heap-backed, uses captured allocator unless one is provided.
        pub fn deinit(self: *Self, maybe_alloc: ?std.mem.Allocator) void {
            switch (self.storage) {
                .none => {},
                .inline => {
                    if (self.dtor) |d| d(self.ctx);
                },
                .heap => |ptr| {
                    if (self.dtor) |d| d(self.ctx);
                    const alloc = self.heap_alloc orelse maybe_alloc orelse
                        @panic("FwdFn.deinit: missing allocator for heap functor");
                    const base: [*]align(@alignCast(self.align)) u8 =
                        @ptrCast([*]align(@as(u29, self.align)) u8, ptr);
                    alloc.free(base[0..self.size]);
                },
            }
            self.* = Self.initNull();
        }

        /// Move (leaves self null).
        pub fn move(self: *Self) Self {
            const out = self.*;
            self.* = Self.initNull();
            return out;
        }

        /// Clone shallowly. Heap-backed copies allocate a new buffer with the same bytes.
        pub fn clone(self: *const Self, alloc: std.mem.Allocator) !Self {
            var out = Self.initNull();
            out.invoker = self.invoker;
            out.dtor = self.dtor;
            out.size = self.size;
            out.align = self.align;
            out.is_inline = self.is_inline;

            switch (self.storage) {
                .none => {
                    out.storage = .none;
                    out.ctx = @ptrFromInt(0);
                    out.heap_alloc = null;
                },
                .inline => |*src| {
                    var s: Storage = .{ .inline = .{ .bytes = undefined } };
                    const dp = &s.inline.bytes;
                    const sp = &src.bytes;
                    @memcpy(dp[0..self.size], sp[0..self.size]);
                    out.storage = s;
                    out.ctx = @ptrCast(*anyopaque, @ptrFromInt(@intFromPtr(&out.storage.inline.bytes)));
                    out.heap_alloc = null;
                },
                .heap => |p| {
                    const np = try alloc.alignedAlloc(u8, self.align, self.size);
                    const dstp = np.ptr;
                    const srcp: [*]align(@alignCast(self.align)) u8 =
                        @ptrCast([*]align(@as(u29, self.align)) u8, p);
                    @memcpy(dstp[0..self.size], srcp[0..self.size]);
                    out.storage = .{ .heap = @ptrCast(*anyopaque, dstp) };
                    out.ctx = @ptrCast(*anyopaque, dstp);
                    out.heap_alloc = alloc;
                },
            }
            return out;
        }

        // ================= invocation =================
        pub fn apply(self: *const Self, args: ArgsTuple) Ret {
            return self.invoker(self.ctx, args);
        }

        /// Ergonomic wrapper with compile-time args type check.
        pub fn call(self: *const Self, args: anytype) Ret {
            comptime {
                if (@TypeOf(args) != ArgsTuple)
                    @compileError("FwdFn.call: expected ArgsTuple for Sig");
            }
            return self.apply(args);
        }

        // ================= constructors =================

        /// Store a function pointer inline and call it via a tiny invoker.
        pub fn fromFn(fp: Sig) Self {
            comptime {
                if (@sizeOf(Sig) > MaxInline or @alignOf(Sig) > MaxAlign)
                    @compileError("FwdFn.fromFn: MaxInline/MaxAlign too small for Sig pointer");
            }
            const Inv = struct {
                fn call(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const p = @ptrCast(*Sig, @alignCast(@alignOf(Sig), ctx));
                    return @call(.auto, p.*, args);
                }
            }.call;

            var s: Storage = .{ .inline = .{ .bytes = undefined } };
            const dst = @ptrCast(*Sig, @alignCast(@alignOf(Sig), &s.inline.bytes));
            dst.* = fp;

            return .{
                .invoker = Inv,
                .ctx = @ptrCast(*anyopaque, @alignCast(@alignOf(Sig), &s.inline.bytes)),
                .storage = s,
                .size = @sizeOf(Sig),
                .align = @alignOf(Sig),
                .is_inline = true,
                .heap_alloc = null,
                .dtor = null,
            };
        }

        /// Accept any type `F` that has `pub fn call(self: *F, ...) Sig`.
        /// Stores inline if it fits, else heap with captured allocator.
        pub fn fromCallable(alloc: std.mem.Allocator, f: anytype) !Self {
            const F = @TypeOf(f);

            // The thunk will fail to compile if F.call doesn't match Sig
            const Inv = thunkCall(F);

            const Dtor: ?*const fn (*anyopaque) void = if (@hasDecl(F, "deinit")) struct {
                fn destroy(ctx: *anyopaque) void {
                    const self = @ptrCast(*F, @alignCast(@alignOf(F), ctx));
                    self.deinit();
                }
            }.destroy else null;

            const fits_inline = (@sizeOf(F) <= MaxInline) and (@alignOf(F) <= MaxAlign);

            if (fits_inline) {
                var s: Storage = .{ .inline = .{ .bytes = undefined } };
                const dst = @ptrCast(*F, @alignCast(@alignOf(F), &s.inline.bytes));
                dst.* = f;

                return .{
                    .invoker = Inv,
                    .ctx = @ptrCast(*anyopaque, @alignCast(@alignOf(F), &s.inline.bytes)),
                    .storage = s,
                    .size = @sizeOf(F),
                    .align = @alignOf(F),
                    .is_inline = true,
                    .heap_alloc = null,
                    .dtor = Dtor,
                };
            } else {
                const buf = try alloc.alignedAlloc(u8, @alignOf(F), @sizeOf(F));
                const p = @ptrCast(*F, buf.ptr);
                p.* = f;

                return .{
                    .invoker = Inv,
                    .ctx = @ptrCast(*anyopaque, p),
                    .storage = .{ .heap = @ptrCast(*anyopaque, p) },
                    .size = @sizeOf(F),
                    .align = @alignOf(F),
                    .is_inline = false,
                    .heap_alloc = alloc,
                    .dtor = Dtor,
                };
            }
        }

        // ================ helpers ================
        /// Generate a thunk that calls `F.call(self: *F, ...) Sig`.
        fn thunkCall(comptime F: type) *const Invoker {
            return struct {
                fn call(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const self = @ptrCast(*F, @alignCast(@alignOf(F), ctx));
                    return @call(.auto, F.call, .{ self } ++ args);
                }
            }.call;
        }

        // some light introspection for diagnostics (fast and simple)
        pub fn isSet(self: *const Self) bool {
            return self.storage != .none;
        }
        pub fn isInline(self: *const Self) bool { return self.is_inline; }
        pub fn payloadSize(self: *const Self) usize { return self.size; }
        pub fn payloadAlign(self: *const Self) u32 { return self.align; }
    };
}

/// Chain: singly-linked chain of FwdFn nodes.
/// Provides both recursive `apply` and fast iterative `run` (no recursion).
pub fn Chain(comptime Sig: type, comptime MaxInline: usize, comptime MaxAlign: usize) type {
    const Fn = FwdFn(Sig, MaxInline, MaxAlign);
    return struct {
        pub const Self = @This();
        pub const ArgsTuple = std.meta.ArgsTuple(Sig);
        pub const Ret = blk: {
            const TI = @typeInfo(Sig);
            if (TI == .Function) break :blk TI.Function.return_type.?;
            if (TI == .Fn)       break :blk TI.Fn.return_type.?;
            @compileError("Chain: Sig must be a function type");
        };

        inner: Fn = Fn.initNull(),
        next: ?*const Self = null,

        pub fn initNull() Self { return .{}; }
        pub fn setNext(self: *Self, nxt: *const Self) void { self.next = nxt; }
        pub fn last(self: *const Self) *const Self { var c: *const Self = self; while (c.next) |n| c = n; return c; }
        pub fn append(self: *Self, nxt: *const Self) *const Self { const tail = self.last(); @constCast(tail).next = nxt; return nxt; }

        pub fn deinit(self: *Self, maybe_alloc: ?std.mem.Allocator) void {
            self.inner.deinit(maybe_alloc);
            self.* = .{};
        }

        /// Tail-call style; may recurse through the chain (fine for short chains).
        pub fn apply(self: *const Self, args: ArgsTuple) Ret {
            if (self.next) |n| return n.apply(args);
            return self.inner.apply(args);
        }

        /// Fast iterative runner; executes every node in order; returns last Ret.
        pub fn run(head: *const Self, args: ArgsTuple) Ret {
            var cur: ?*const Self = head;
            var last: Ret = undefined;
            while (cur) |n| {
                last = n.inner.apply(args);
                cur = n.next;
            }
            return last;
        }
    };
}
