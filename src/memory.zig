const std = @import("std");

// =======================
// Config / public counts.
// =======================
pub const GP_REG_COUNT: usize = 256;
pub const THIS_COUNT: usize = 2;
pub const SUPER_COUNT: usize = 2;
pub const ARGUMENTS_COUNT: usize = 16;
pub const RETURN_COUNT: usize = 2;
pub const THROW_COUNT: usize = 2;

// ==================================
// Register descriptor (public API).
// ==================================
pub const RegisterKind = enum(u8) {
    gp, // general purpose
    this_,
    super_,
    arg,
    ret,
    throw_,
};

pub const RegisterRef = struct {
    kind: RegisterKind,
    index: u16,

    pub fn check(self: RegisterRef) !void {
        switch (self.kind) {
            .gp => if (self.index >= GP_REG_COUNT) return error.BadRegisterIndex,
            .this_ => if (self.index >= THIS_COUNT) return error.BadRegisterIndex,
            .super_ => if (self.index >= SUPER_COUNT) return error.BadRegisterIndex,
            .arg => if (self.index >= ARGUMENTS_COUNT) return error.BadRegisterIndex,
            .ret => if (self.index >= RETURN_COUNT) return error.BadRegisterIndex,
            .throw_ => if (self.index >= THROW_COUNT) return error.BadRegisterIndex,
        }
    }
};

// =====================================================
// Generic ValueManager<NameT, ValueT>
//     - layered variables (stack of hash maps)
//     - register files (gp + specials)
//     - read/write by InstructionOperator
// =====================================================
pub fn ValueManager(comptime NameT: type, comptime ValueT: type) type {
    return struct {
        const Self = @This();

        // --------
        // Storage.
        // --------
        gp: [GP_REG_COUNT]ValueT = undefined,
        this_: [THIS_COUNT]ValueT = undefined,
        super_: [SUPER_COUNT]ValueT = undefined,
        args: [ARGUMENTS_COUNT]ValueT = undefined,
        rets: [RETURN_COUNT]ValueT = undefined,
        throws: [THROW_COUNT]ValueT = undefined,

        // Layered maps (top is current scope).
        layers: std.ArrayListUnmanaged(std.AutoHashMapUnmanaged(NameT, ValueT)) = .{},
        alloc: std.mem.Allocator,

        // =======================
        // Lifecycle.
        // =======================
        pub fn init(alloc: std.mem.Allocator, init_value: ValueT) !Self {
            var self: Self = .{
                .alloc = alloc,
            };
            // Initialize register files with a known value.
            @memset(&self.gp, init_value);
            @memset(&self.this_, init_value);
            @memset(&self.super_, init_value);
            @memset(&self.args, init_value);
            @memset(&self.rets, init_value);
            @memset(&self.throws, init_value);

            // Start with one layer (global / function scope).
            try self.pushLayer();
            return self;
        }

        pub fn deinit(self: *Self) void {
            // Pop and free all layers.
            var i: usize = self.layers.items.len;
            while (i > 0) {
                i -= 1;
                self.layers.items[i].deinit(self.alloc);
            }
            self.layers.deinit(self.alloc);
        }

        // =======================
        // Layered map operations.
        // =======================
        pub fn pushLayer(self: *Self) !void {
            var map = std.AutoHashMapUnmanaged(NameT, ValueT){};
            try self.layers.append(self.alloc, map);
        }

        pub fn popLayer(self: *Self) void {
            if (self.layers.items.len == 0) @panic("popLayer underflow");
            const map = self.layers.pop();
            map.deinit(self.alloc);
        }

        /// Define or overwrite in the **current** (top) layer.
        pub fn define(self: *Self, name: NameT, value: ValueT) !void {
            if (self.layers.items.len == 0) try self.pushLayer();
            var top = &self.layers.items[self.layers.items.len - 1];
            var gop = try top.getOrPut(self.alloc, name);
            gop.value_ptr.* = value;
        }

        /// Assign to first visible layer containing `name`.
        /// If not found, falls back to define in current layer when `define_if_missing` is true.
        pub fn assign(self: *Self, name: NameT, value: ValueT, define_if_missing: bool) !void {
            var i: isize = @intCast(self.layers.items.len);
            while (i > 0) {
                i -= 1;
                const idx: usize = @intCast(i);
                if (self.layers.items[idx].getPtr(name)) |p| {
                    p.* = value;
                    return;
                }
            }
            if (!define_if_missing) return error.NameNotFound;
            try self.define(name, value);
        }

        /// Lookup `name` from the current layer outward.
        pub fn lookup(self: *const Self, name: NameT) ?ValueT {
            var i: isize = @intCast(self.layers.items.len);
            while (i > 0) {
                i -= 1;
                const idx: usize = @intCast(i);
                if (self.layers.items[idx].get(name)) |v| return v;
            }
            return null;
        }

        // =======================
        // Register accessors.
        // =======================
        pub fn readRegister(self: *const Self, r: RegisterRef) !ValueT {
            try r.check();
            return switch (r.kind) {
                .gp => self.gp[r.index],
                .this_ => self.this_[r.index],
                .super_ => self.super_[r.index],
                .arg => self.args[r.index],
                .ret => self.rets[r.index],
                .throw_ => self.throws[r.index],
            };
        }

        pub fn writeRegister(self: *Self, r: RegisterRef, v: ValueT) !void {
            try r.check();
            switch (r.kind) {
                .gp => self.gp[r.index] = v,
                .this_ => self.this_[r.index] = v,
                .super_ => self.super_[r.index] = v,
                .arg => self.args[r.index] = v,
                .ret => self.rets[r.index] = v,
                .throw_ => self.throws[r.index] = v,
            }
        }

        /// Returns a pointer to the underlying register slot (for in-place updates).
        pub fn ptrRegister(self: *Self, r: RegisterRef) !*ValueT {
            try r.check();
            return switch (r.kind) {
                .gp => &self.gp[r.index],
                .this_ => &self.this_[r.index],
                .super_ => &self.super_[r.index],
                .arg => &self.args[r.index],
                .ret => &self.rets[r.index],
                .throw_ => &self.throws[r.index],
            };
        }

        // =========================================================
        // Unified read/write using your InstructionOperator shape.
        //
        // Expectation:
        //   pub const InstructionOperator = union(enum(u8)) {
        //       LayeredMap: NameT,
        //       Register: RegisterRef,
        //       ConstantValue: ValueT,
        //   };
        // =========================================================
        pub fn readByOp(self: *const Self, op: anytype) !ValueT {
            // Duck-type against your InstructionOperator.
            switch (op) {
                .LayeredMap => |name| {
                    if (self.lookup(name)) |v| return v;
                    return error.NameNotFound;
                },
                .Register => |r| {
                    return self.readRegister(r);
                },
                .ConstantValue => |cv| {
                    return cv; // pass through immediate
                },
            }
        }

        /// Assign semantics: LayeredMap updates existing or defines at top if `define_if_missing`.
        /// ConstantValue is not assignable.
        pub fn writeByOp(self: *Self, op: anytype, v: ValueT, define_if_missing: bool) !void {
            switch (op) {
                .LayeredMap => |name| {
                    try self.assign(name, v, define_if_missing);
                },
                .Register => |r| {
                    try self.writeRegister(r, v);
                },
                .ConstantValue => {
                    return error.NotAssignable;
                },
            }
        }
    };
}

// ========================
// Tiny self-test (optional)
// ========================
test "ValueManager basic" {
    const NameT = u32;
    const ValueT = i64;
    const VM = ValueManager(NameT, ValueT);

    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const alloc = gpa_state.allocator();

    var vm = try VM.init(alloc, 0);
    defer vm.deinit();

    // Registers
    try vm.writeRegister(.{ .kind = .gp, .index = 1 }, 42);
    try std.testing.expectEqual(@as(ValueT, 42), try vm.readRegister(.{ .kind = .gp, .index = 1 }));

    // Layered map
    try vm.define(10, 7);
    try std.testing.expectEqual(@as(ValueT, 7), vm.lookup(10).?);
    try vm.pushLayer();
    try vm.assign(10, 9, false); // update outer
    try std.testing.expectEqual(@as(ValueT, 9), vm.lookup(10).?);

    // Unified by InstructionOperator-like shape
    const Op = union(enum(u8)) {
        LayeredMap: NameT,
        Register: RegisterRef,
        ConstantValue: ValueT,
    };
    const op_reg = Op{ .Register = .{ .kind = .gp, .index = 1 } };
    const op_name = Op{ .LayeredMap = 10 };
    const op_const = Op{ .ConstantValue = 111 };

    try std.testing.expectEqual(@as(ValueT, 42), try vm.readByOp(op_reg));
    try std.testing.expectEqual(@as(ValueT, 9), try vm.readByOp(op_name));
    try std.testing.expectEqual(@as(ValueT, 111), try vm.readByOp(op_const));

    try vm.writeByOp(op_reg, 5, false);
    try std.testing.expectEqual(@as(ValueT, 5), try vm.readRegister(.{ .kind = .gp, .index = 1 }));

    // Assign to name that doesn't exist in any layer -> define at top
    try vm.writeByOp(Op{ .LayeredMap = 77 }, 1234, true);
    try std.testing.expectEqual(@as(ValueT, 1234), vm.lookup(77).?);
}
