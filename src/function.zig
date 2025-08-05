const std = @import("std");

pub fn FwdFn(comptime Sig: type, comptime MaxInline: usize, comptime MaxAlign: usize) type {
    const ArgsTuple = std.meta.ArgsTuple(Sig);
    const Ret = blk: {
        const TI = @typeInfo(Sig);
        if (TI == .Function) break :blk TI.Function.return_type.?;
        if (TI == .Fn) break :blk TI.Fn.return_type.?;
        @compileError("FwdFn: Sig must be a function type");
    };
    const Invoker = fn (*anyopaque, ArgsTuple) Ret;

    const Storage = union(enum) {
        none,
        inline_: struct { bytes: [MaxInline]u8 align(MaxAlign) },
        heap: *anyopaque,
    };

    return struct {
        pub const Self = @This();

        invoker: *const Invoker = undefined,
        ctx: *anyopaque = undefined,
        storage: Storage = .none,
        size: usize = 0,
        align_: u32 = 0,
        is_inline: bool = true,
        heap_alloc: ?std.mem.Allocator = null,
        dtor: ?*const fn (*anyopaque) void = null,

        pub fn initNull() Self {
            return .{ .invoker = undefined, .ctx = undefined, .storage = .none };
        }

        pub fn deinit(self: *Self, maybe_alloc: ?std.mem.Allocator) void {
            switch (self.storage) {
                .none => {},
                .inline_ => {
                    if (self.dtor) |d| d(self.ctx);
                },
                .heap => |ptr| {
                    if (self.dtor) |d| d(self.ctx);
                    const alloc = self.heap_alloc orelse maybe_alloc orelse
                        @panic("FwdFn.deinit: missing allocator for heap functor");

                    // Result type supplied by context; plain byte view is enough for free()
                    const base: [*]u8 = @ptrCast(ptr);
                    alloc.free(base[0..self.size]);
                },
            }
            self.* = Self.initNull();
        }

        pub fn move(self: *Self) Self {
            const out = self.*;
            self.* = Self.initNull();
            return out;
        }

        pub fn clone(self: *const Self, alloc: std.mem.Allocator) !Self {
            var out = Self.initNull();
            out.invoker = self.invoker;
            out.dtor = self.dtor;
            out.size = self.size;
            out.align_ = self.align_;
            out.is_inline = self.is_inline;

            switch (self.storage) {
                .none => {
                    out.storage = .none;
                    out.ctx = @ptrFromInt(0);
                    out.heap_alloc = null;
                },
                .inline_ => |*src| {
                    var s: Storage = .{ .inline_ = .{ .bytes = undefined } };
                    const dp = &s.inline_.bytes;
                    const sp = &src.bytes;
                    @memcpy(dp[0..self.size], sp[0..self.size]);
                    out.storage = s;
                    out.ctx = @ptrFromInt(@intFromPtr(&out.storage.inline_.bytes));
                    out.heap_alloc = null;
                },
                .heap => |p| {
                    const np = try alloc.alignedAlloc(u8, self.align_, self.size);
                    const dstp = np.ptr;

                    // Read source as raw bytes; no dependent alignment needed
                    const srcp: [*]u8 = @ptrCast(p);

                    @memcpy(dstp[0..self.size], srcp[0..self.size]);
                    out.storage = .{ .heap = @as(*anyopaque, @ptrCast(dstp)) };
                    out.ctx = @as(*anyopaque, @ptrCast(dstp));
                    out.heap_alloc = alloc;
                },
            }
            return out;
        }

        pub fn apply(self: *const Self, args: ArgsTuple) Ret {
            return self.invoker(self.ctx, args);
        }

        pub fn call(self: *const Self, args: anytype) Ret {
            comptime {
                if (@TypeOf(args) != ArgsTuple)
                    @compileError("FwdFn.call: expected ArgsTuple for Sig");
            }
            return self.apply(args);
        }

        pub fn fromFn(fp: Sig) Self {
            comptime {
                if (@sizeOf(Sig) > MaxInline or @alignOf(Sig) > MaxAlign)
                    @compileError("FwdFn.fromFn: MaxInline/MaxAlign too small for Sig pointer");
            }
            const Inv = struct {
                fn call(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const p: *Sig = @ptrCast(@alignCast(@alignOf(Sig))(ctx));
                    return @call(.auto, p.*, args);
                }
            }.call;

            var s: Storage = .{ .inline_ = .{ .bytes = undefined } };
            const dst: *Sig = @ptrCast(@alignCast(@alignOf(Sig))(&s.inline_.bytes));
            dst.* = fp;

            return .{
                .invoker = Inv,
                .ctx = @as(*anyopaque, @ptrCast(@alignCast(@alignOf(Sig))(&s.inline_.bytes))),
                .storage = s,
                .size = @sizeOf(Sig),
                .align_ = @alignOf(Sig),
                .is_inline = true,
                .heap_alloc = null,
                .dtor = null,
            };
        }

        pub fn fromCallable(alloc: std.mem.Allocator, f: anytype) !Self {
            const F = @TypeOf(f);
            const Inv = thunkCall(F);

            const Dtor: ?*const fn (*anyopaque) void = if (@hasDecl(F, "deinit")) struct {
                fn destroy(ctx: *anyopaque) void {
                    const self: *F = @ptrCast(@alignCast(@alignOf(F))(ctx));
                    self.deinit();
                }
            }.destroy else null;

            const fits_inline = (@sizeOf(F) <= MaxInline) and (@alignOf(F) <= MaxAlign);

            if (fits_inline) {
                var s: Storage = .{ .inline_ = .{ .bytes = undefined } };
                const dst: *F = @ptrCast(@alignCast(@alignOf(F))(&s.inline_.bytes));
                dst.* = f;

                return .{
                    .invoker = Inv,
                    .ctx = @as(*anyopaque, @ptrCast(@alignCast(@alignOf(F))(&s.inline_.bytes))),
                    .storage = s,
                    .size = @sizeOf(F),
                    .align_ = @alignOf(F),
                    .is_inline = true,
                    .heap_alloc = null,
                    .dtor = Dtor,
                };
            } else {
                const buf = try alloc.alignedAlloc(u8, @alignOf(F), @sizeOf(F));
                const p = @ptrCast(*F)(buf.ptr);
                p.* = f;

                return .{
                    .invoker = Inv,
                    .ctx = @as(*anyopaque, @ptrCast(p)),
                    .storage = .{ .heap = @as(*anyopaque, @ptrCast(p)) },
                    .size = @sizeOf(F),
                    .align_ = @alignOf(F),
                    .is_inline = false,
                    .heap_alloc = alloc,
                    .dtor = Dtor,
                };
            }
        }

        fn thunkCall(comptime F: type) *const Invoker {
            return struct {
                fn call(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const self: *F = @ptrCast(@alignCast(@alignOf(F))(ctx));
                    return @call(.auto, F.call, .{self} ++ args);
                }
            }.call;
        }

        pub fn isSet(self: *const Self) bool {
            return self.storage != .none;
        }
        pub fn isInline(self: *const Self) bool {
            return self.is_inline;
        }
        pub fn payloadSize(self: *const Self) usize {
            return self.size;
        }
        pub fn payloadAlign(self: *const Self) u32 {
            return self.align_;
        }
    };
}

pub fn Chain(comptime Sig: type, comptime MaxInline: usize, comptime MaxAlign: usize) type {
    const Fn = FwdFn(Sig, MaxInline, MaxAlign);
    return struct {
        pub const Self = @This();
        pub const ArgsTuple = std.meta.ArgsTuple(Sig);
        pub const Ret = blk: {
            const TI = @typeInfo(Sig);
            if (TI == .Function) break :blk TI.Function.return_type.?;
            if (TI == .Fn) break :blk TI.Fn.return_type.?;
            @compileError("Chain: Sig must be a function type");
        };

        inner: Fn = Fn.initNull(),
        next: ?*const Self = null,

        pub fn initNull() Self {
            return .{};
        }
        pub fn setNext(self: *Self, nxt: *const Self) void {
            self.next = nxt;
        }
        pub fn last(self: *const Self) *const Self {
            var c: *const Self = self;
            while (c.next) |n| c = n;
            return c;
        }
        pub fn append(self: *Self, nxt: *const Self) *const Self {
            const tail = self.last();
            @constCast(tail).next = nxt;
            return nxt;
        }

        pub fn deinit(self: *Self, maybe_alloc: ?std.mem.Allocator) void {
            self.inner.deinit(maybe_alloc);
            self.* = .{};
        }

        pub fn apply(self: *const Self, args: ArgsTuple) Ret {
            if (self.next) |n| return n.apply(args);
            return self.inner.apply(args);
        }

        pub fn run(head: *const Self, args: ArgsTuple) Ret {
            var cur: ?*const Self = head;
            var last_: Ret = undefined;
            while (cur) |n| {
                last_ = n.inner.apply(args);
                cur = n.next;
            }
            return last_;
        }
    };
}
