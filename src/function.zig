const std = @import("std");

/// A small-buffer-optimized, type-erased callable.
/// - Sig: the exact function signature (no varargs, monomorphic)
/// - MaxSize / MaxAlign: inline storage constraints
pub fn Function(comptime Sig: type, comptime MaxSize: usize, comptime MaxAlign: usize) type {
    const FnInfo = @typeInfo(Sig);
    comptime {
        if (FnInfo != .Fn) @compileError("Function: Sig must be a function type");
        if (FnInfo.Fn.is_var_args) @compileError("Function: varargs not supported");
        if (FnInfo.Fn.return_type == null) @compileError("Function: Sig must have a return type");
        if (MaxAlign == 0 or (MaxAlign & (MaxAlign - 1)) != 0)
            @compileError("Function: MaxAlign must be a non-zero power of two");
    }

    pub const Ret = FnInfo.Fn.return_type.?;
    pub const ArgsTuple = std.meta.ArgsTuple(Sig);

    // Unique type-id token: one address per concrete F.
    inline fn typeIdOf(comptime T: type) *const anyopaque {
        const Tag = struct {
            fn sentinel() void {}
        };
        return @ptrCast(*const anyopaque, &Tag.sentinel);
    }

    const Storage = union(enum) {
        none,
        inline: struct { bytes: [MaxSize]u8 align(MaxAlign) },
        heap: *anyopaque,
    };

    const VTable = struct {
        invoke: *const fn (ctx: *anyopaque, args: ArgsTuple) Ret,
        clone_into: *const fn (dest: *Storage, src: *const Storage, alloc: std.mem.Allocator) anyerror!void,
        destroy: *const fn (src: *Storage, alloc: std.mem.Allocator) void,
        ctx_of: *const fn (s: *Storage) *anyopaque,

        is_inline: bool,
        size: usize,
        align: u32,
        type_id: *const anyopaque,
    };

    return struct {
        pub const Self = @This();

        vtable: ?*const VTable = null,
        storage: Storage = .none,

        // When heap is used, we capture the allocator to make deinit safe.
        heap_alloc: ?std.mem.Allocator = null,

        ctx: ?*anyopaque = null,

        // ========== Lifecycle ==========

        pub fn initNull() Self {
            return .{};
        }

        inline fn setCtxForCurrentStorage(self: *Self) void {
            if (self.vtable == null) { self.ctx = null; return; }
            switch (self.storage) {
                .inline => |*inl| self.ctx = @ptrCast(*anyopaque, &inl.bytes),
                .heap => |p| self.ctx = @ptrCast(*anyopaque, p),
                .none => self.ctx = null,
            }
        }

        /// Idempotent. If heap-backed, it uses the captured allocator by default.
        pub fn deinit(self: *Self, maybe_alloc: ?std.mem.Allocator) void {
            const vt = self.vtable orelse {
                self.* = .{};
                return;
            };
            const used_alloc = if (!vt.is_inline)
                (self.heap_alloc orelse maybe_alloc orelse
                    @panic("Function.deinit: missing allocator for heap storage"))
            else
                // never used by inline destroy, but provide a dummy to match signature
                (maybe_alloc orelse std.heap.page_allocator);

            vt.destroy(&self.storage, used_alloc);
            self.* = .{};
        }

        /// Move out (leaves `self` null).
        pub fn move(self: *Self) Self {
            const out = self.*;
            self.* = .{};
            return out;
        }

        /// Swap two callables.
        pub fn swap(a: *Self, b: *Self) void {
            const tv = a.vtable; const ts = a.storage; const ta = a.heap_alloc;
            a.vtable = b.vtable; a.storage = b.storage; a.heap_alloc = b.heap_alloc;
            b.vtable = tv;       b.storage = ts;       b.heap_alloc = ta;
        }

        /// Clone using given allocator; captures it if the representation is heap.
        pub fn clone(self: *const Self, alloc: std.mem.Allocator) !Self {
            var out: Self = .{};
            if (self.vtable) |vt| {
                try vt.clone_into(&out.storage, &self.storage, alloc);
                out.vtable = vt;
                if (!vt.is_inline) out.heap_alloc = alloc;
            }
            return out;
        }

        // ========== Invocation ==========

        /// Main entry: pass arguments as the exact ArgsTuple (e.g., .{a, b}).
        pub fn apply(self: *const Self, args: ArgsTuple) Ret {
            const vt = self.vtable orelse @panic("Function.apply: not set");
            return vt.invoke(vt.ctx_of(@constCast(&self.storage)), args);
        }

        /// Ergonomic helper: same as `apply`, but validated at comptime.
        pub fn call(self: *const Self, args: anytype) Ret {
            comptime {
                if (@TypeOf(args) != ArgsTuple)
                    @compileError("Function.call expects an ArgsTuple matching Sig");
            }
            return self.apply(args);
        }

        /// Zero-arg convenience when Sig has no params.
        pub fn call0(self: *const Self) Ret {
            comptime {
                if (FnInfo.Fn.params.len != 0)
                    @compileError("Function.call0 only valid for zero-arg signatures");
            }
            return self.apply(.{});
        }

        // ========== Introspection / diagnostics ==========

        pub fn isSet(self: *const Self) bool { return self.vtable != null; }
        pub fn isInline(self: *const Self) bool {
            const vt = self.vtable orelse return false;
            return vt.is_inline;
        }
        pub fn payloadSize(self: *const Self) ?usize {
            return if (self.vtable) |vt| vt.size else null;
        }
        pub fn payloadAlign(self: *const Self) ?u32 {
            return if (self.vtable) |vt| vt.align else null;
        }
        pub fn isType(self: *const Self, comptime F: type) bool {
            if (self.vtable) |vt| return vt.type_id == typeIdOf(F);
            return false;
        }

        /// Returns non-owning pointer to inline payload when it *is* inline of type F.
        /// Useful for diagnostics; do not store beyond lifetime.
        pub fn tryInlineAs(self: *Self, comptime F: type) ?*F {
            const vt = self.vtable orelse return null;
            if (!vt.is_inline or vt.type_id != typeIdOf(F)) return null;
            return @ptrCast(*F, @alignCast(@alignOf(F), &self.storage.inline.bytes));
        }

        // ========== Constructors ==========

        /// From a function pointer exactly matching Sig (stored inline).
        pub fn fromFn(fnptr: Sig) Self {
            comptime {
                if (@sizeOf(Sig) > MaxSize or @alignOf(Sig) > MaxAlign)
                    @compileError("Function.fromFn: MaxSize/MaxAlign too small for function pointer");
            }
            const VT = vtableForFnPtr();
            var s: Storage = .{ .inline = .{ .bytes = undefined } };
            const dst = @ptrCast(*Sig, @alignCast(@alignOf(Sig), &s.inline.bytes));
            dst.* = fnptr;

            const self = .{
                .vtable = &VT,
                .storage = s,
                .heap_alloc = null,
            };
            self.setCtxForCurrentStorage();
            return self;
        }

        /// From a callable `F`:
        ///   - If `F` is `fn` and matches Sig, delegates to fromFn.
        ///   - Else requires `pub fn call(self: *F, ...) Sig`.
        ///   - Inline if fits SBO, else heap-alloc (capturing `alloc`).
        pub fn fromCallable(alloc: std.mem.Allocator, f: anytype) !Self {
            const F = @TypeOf(f);
            const ti = @typeInfo(F);

            if (ti == .Fn) {
                // exact function ptr?
                comptime {
                    if (@TypeOf(f) != Sig)
                        @compileError("fromCallable: function pointer must match Sig exactly");
                }
                return Self.fromFn(f);
            }

            comptime checkCallSignature(F);

            const fits_inline = (@sizeOf(F) <= MaxSize) and (@alignOf(F) <= MaxAlign);

            if (fits_inline) {
                const VT = vtableForInlineFunctor(F);
                var s: Storage = .{ .inline = .{ .bytes = undefined } };
                const dst = @ptrCast(*F, @alignCast(@alignOf(F), &s.inline.bytes));
                dst.* = f;

                const self = .{
                    .vtable = &VT,
                    .storage = s,
                    .heap_alloc = null,
                };
                self.setCtxForCurrentStorage();
                return self;
            } else {
                const VT = vtableForHeapFunctor(F);
                const buf = try alloc.alignedAlloc(u8, @alignOf(F), @sizeOf(F));
                const p = @ptrCast(*F, buf.ptr);
                p.* = f;

                const self = .{
                    .vtable = &VT,
                    .storage = .{ .heap = p },
                    .heap_alloc = alloc,
                };
                self.setCtxForCurrentStorage();
                return self;
            }
        }

        // ========== Compile-time checking ==========

        fn checkCallSignature(comptime F: type) void {
            comptime {
                if (!@hasDecl(F, "call"))
                    @compileError("Callable type must have `pub fn call(self: *F, ...) Sig`");
            }
            const TI = @typeInfo(@TypeOf(F.call));
            if (TI != .Fn) @compileError("F.call must be a function");

            const finfo = TI.Fn;
            if (finfo.params.len == 0) @compileError("F.call must be: fn(self: *F, ...)");
            const self_param = finfo.params[0].type orelse
                @compileError("F.call cannot be generic");
            const self_ti = @typeInfo(self_param);
            if (self_ti != .Pointer or self_ti.Pointer.size != .One or self_ti.Pointer.child != F)
                @compileError("F.call first parameter must be *F or *const F");

            // args
            const SigArgs = FnInfo.Fn.params;
            if (SigArgs.len != finfo.params.len - 1)
                @compileError("F.call argument count mismatch with Sig");
            inline for (SigArgs, 0..) |p, i| {
                const want = p.type orelse @compileError("Sig cannot be generic");
                const got = finfo.params[i + 1].type orelse @compileError("F.call must be monomorphic");
                if (got != want) @compileError("F.call param type mismatch");
            }
            // return type
            const got_ret = finfo.return_type orelse @compileError("F.call must return a value");
            if (got_ret != Ret) @compileError("F.call return type mismatch");
        }

        // ========== VTABLES ==========

        fn vtableForFnPtr() VTable {
            const Invoke = struct {
                fn invoke(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const f = @ptrCast(*Sig, @alignCast(@alignOf(Sig), ctx));
                    return @call(.auto, f.*, args);
                }
            };
            return .{
                .invoke = Invoke.invoke,
                .clone_into = struct {
                    fn clone_into(dest: *Storage, src: *const Storage, _: std.mem.Allocator) !void {
                        dest.* = .{ .inline = .{ .bytes = undefined } };
                        const sp = &src.inline.bytes;
                        const dp = &dest.inline.bytes;
                        const n: usize = @sizeOf(Sig);
                        @memcpy(dp[0..n], sp[0..n]);
                    }
                }.clone_into,
                .destroy = struct {
                    fn destroy(_: *Storage, _: std.mem.Allocator) void {}
                }.destroy,
                .ctx_of = struct {
                    fn ctx_of(s: *Storage) *anyopaque {
                        return @ptrCast(*anyopaque, &s.inline.bytes);
                    }
                }.ctx_of,
                .is_inline = true,
                .size = @sizeOf(Sig),
                .align = @alignOf(Sig),
                .type_id = typeIdOf(Sig),
            };
        }

        fn vtableForInlineFunctor(comptime F: type) VTable {
            const Invoke = struct {
                fn invoke(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const selfp = @ptrCast(*F, @alignCast(@alignOf(F), ctx));
                    return @call(.auto, F.call, .{ selfp } ++ args);
                }
            };
            return .{
                .invoke = Invoke.invoke,
                .clone_into = struct {
                    fn clone_into(dest: *Storage, src: *const Storage, _: std.mem.Allocator) !void {
                        dest.* = .{ .inline = .{ .bytes = undefined } };
                        const sp = &src.inline.bytes;
                        const dp = &dest.inline.bytes;
                        const n: usize = @sizeOf(F);
                        @memcpy(dp[0..n], sp[0..n]);
                    }
                }.clone_into,
                .destroy = struct {
                    fn destroy(src: *Storage, _: std.mem.Allocator) void {
                        if (@hasDecl(F, "deinit")) {
                            const p = @ptrCast(*F, @alignCast(@alignOf(F), &src.inline.bytes));
                            p.deinit();
                        }
                    }
                }.destroy,
                .ctx_of = struct {
                    fn ctx_of(s: *Storage) *anyopaque {
                        return @ptrCast(*anyopaque, &s.inline.bytes);
                    }
                }.ctx_of,
                .is_inline = true,
                .size = @sizeOf(F),
                .align = @alignOf(F),
                .type_id = typeIdOf(F),
            };
        }

        fn vtableForHeapFunctor(comptime F: type) VTable {
            const Invoke = struct {
                fn invoke(ctx: *anyopaque, args: ArgsTuple) Ret {
                    const selfp = @ptrCast(*F, @alignCast(@alignOf(F), ctx));
                    return @call(.auto, F.call, .{ selfp } ++ args);
                }
            };
            return .{
                .invoke = Invoke.invoke,
                .clone_into = struct {
                    fn clone_into(dest: *Storage, src: *const Storage, alloc: std.mem.Allocator) !void {
                        const np = try alloc.alignedAlloc(u8, @alignOf(F), @sizeOf(F));
                        const dstp = @ptrCast(*F, np.ptr);
                        const srcp = @ptrCast(*F, src.heap);
                        dstp.* = srcp.*; // shallow copy
                        dest.* = .{ .heap = dstp };
                    }
                }.clone_into,
                .destroy = struct {
                    fn destroy(src: *Storage, alloc: std.mem.Allocator) void {
                        if (@hasDecl(F, "deinit")) {
                            const p = @ptrCast(*F, src.heap);
                            p.deinit();
                        }
                        const base: [*]align(@alignOf(F)) u8 =
                            @ptrCast([*]align(@alignOf(F)) u8, src.heap);
                        alloc.free(base[0..@sizeOf(F)]);
                    }
                }.destroy,
                .ctx_of = struct {
                    fn ctx_of(s: *Storage) *anyopaque { return @ptrCast(*anyopaque, s.heap); }
                }.ctx_of,
                .is_inline = false,
                .size = @sizeOf(F),
                .align = @alignOf(F),
                .type_id = typeIdOf(F),
            };
        }
    };
}

/// A small wrapper that chains Functions and tail-calls to `next` if set.
/// Usage:
///   var a = ChainedFunction(Sig, ...).initWith(fnA);
///   var b = ChainedFunction(Sig, ...).initWith(fnB);
///   a.setNext(&b);
///   a.apply(args)  // tail-calls b.apply(args)
pub fn ChainedFunction(comptime Sig: type, comptime MaxSize: usize, comptime MaxAlign: usize) type {
    const Fn = Function(Sig, MaxSize, MaxAlign);
    return struct {
        pub const Self = @This();
        pub const Ret = Fn.Ret;
        pub const ArgsTuple = Fn.ArgsTuple;

        inner: Fn = Fn.initNull(),
        next: ?*const Self = null,

        pub fn initNull() Self { return .{}; }

        pub fn initWith(fnptr: Sig) Self {
            return .{ .inner = Fn.fromFn(fnptr), .next = null };
        }

        pub fn fromCallable(alloc: std.mem.Allocator, f: anytype) !Self {
            return .{ .inner = try Fn.fromCallable(alloc, f), .next = null };
        }

        pub fn deinit(self: *Self, maybe_alloc: ?std.mem.Allocator) void {
            self.inner.deinit(maybe_alloc);
            self.* = .{};
        }

        pub fn setNext(self: *Self, nxt: *const Self) void { self.next = nxt; }

        /// Returns the last node following `self` (or self if none).
        pub fn last(self: *const Self) *const Self {
            var cur: *const Self = self;
            while (cur.next) |n| cur = n;
            return cur;
        }

        /// Append `nxt` after the current tail; returns the new tail.
        pub fn append(self: *Self, nxt: *const Self) *const Self {
            const tail = self.last();
            // Cast away const only locally; caller controls lifetimes.
            const mw = @constCast(tail);
            mw.next = nxt;
            return nxt;
        }

        /// Tail-call: if next exists, tail-call it; else call inner.
        pub fn apply(self: *const Self, args: ArgsTuple) Ret {
            // run this node
            const r = self.inner.apply(args);
            // tail-call next if present
            if (self.next) |n| {
                // Optional: force tail call (works when ABI/opt allows)
                return @call(.always_tail, apply, .{ n, args });
                // Or: return n.apply(args);
            }
            return r;
        }

        /// Run inner (discard result) then tail-call next if present; otherwise return inner.
        /// (Useful for logging/metrics middleware.)
        pub fn applyAndThen(self: *const Self, args: ArgsTuple) Ret {
            if (self.next) |n| {
                const _ = self.inner.apply(args);
                return n.apply(args); // <- tail-call
            } else {
                return self.inner.apply(args);
            }
        }

        pub fn isSet(self: *const Self) bool { return self.inner.isSet(); }
    };
}
