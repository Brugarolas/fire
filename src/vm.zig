const std = @import("std");
const ir = @import("ir");
const mem = @import("memory");
const fnkit = @import("function"); // exposes Function / ChainedFunction

// ---- Short aliases from IR ----
const Value = ir.ValueMHIR;
const ValueType = ir.ValueType;
const UnaryOp = ir.UnaryOperator;
const BinaryOp = ir.BinaryOperator;
const Instruction = ir.InstructionMHIR;
const VariableId = ir.VariableId;

pub const Alloc = std.mem.Allocator;

// =====================================
// VM: uses ValueManager for storage
// =====================================
pub const VM = struct {
    const Self = @This();

    alloc: Alloc,
    vals: ValueStore, // registers + layered maps
    out: std.io.AnyWriter, // where Print writes

    pub fn init(alloc: Alloc, writer: anytype) !Self {
        return .{
            .alloc = alloc,
            .vals = try ValueStore.init(alloc, .Undefined),
            .out = std.io.anyWriter(writer),
        };
    }

    pub fn deinit(self: *Self) void {
        self.vals.deinit();
    }

    // Scope handling maps to ValueManager layers
    pub fn enterScope(self: *Self) !void {
        try self.vals.pushLayer();
    }
    pub fn exitScope(self: *Self) void {
        self.vals.popLayer();
    }
};

// We key layered variables by VariableId (u32) for this first slice.
const ValueStore = mem.ValueManager(VariableId, Value);

// =====================================
// Value helpers (same as before)
// =====================================
fn defaultForType(t: ValueType) Value {
    return switch (t) {
        .any, .object, .function => .Undefined,
        .bool => .{ .Boolean = false },
        .number => .{ .Number = 0 },
        .string => .{ .String = "" },
        .null_ => .Null,
        .undefined => .Undefined,
    };
}

fn truthy(v: Value) bool {
    return switch (v) {
        .Undefined => false,
        .Null => false,
        .Boolean => |b| b,
        .Number => |n| n != 0 and !std.math.isNan(n),
        .String => |s| s.len != 0,
    };
}

fn unaryApply(op: UnaryOp, a: Value) Value {
    return switch (op) {
        .Neg => switch (a) {
            .Number => |n| .{ .Number = -n },
            else => .Undefined,
        },
        .Pos => switch (a) {
            .Number => |n| .{ .Number = n },
            else => .Undefined,
        },
        .Inc => switch (a) {
            .Number => |n| .{ .Number = n + 1 },
            else => .Undefined,
        },
        .Dec => switch (a) {
            .Number => |n| .{ .Number = n - 1 },
            else => .Undefined,
        },
        .LogicalNot => .{ .Boolean = !truthy(a) },
        .ToBoolean => .{ .Boolean = truthy(a) },
        .BitwiseNot => switch (a) {
            .Number => |n| .{ .Number = @as(f64, @floatFromInt(~@as(i64, @intFromFloat(n)))) },
            else => .Undefined,
        },
        .Rol => switch (a) {
            .Number => |n| .{ .Number = @as(f64, @floatFromInt(std.math.rotl(u64, @as(u64, @bitCast(i64, @intFromFloat(n))), 1))) },
            else => .Undefined,
        },
        .Ror => switch (a) {
            .Number => |n| .{ .Number = @as(f64, @floatFromInt(std.math.rotr(u64, @as(u64, @bitCast(i64, @intFromFloat(n))), 1))) },
            else => .Undefined,
        },
        .Await => a, // placeholder
    };
}

fn valueEq(a: Value, b: Value) bool {
    return switch (a) {
        .Undefined => b == .Undefined,
        .Null => b == .Null,
        .Boolean => |av| b == .Boolean and av == b.Boolean,
        .Number => |an| b == .Number and an == b.Number,
        .String => |as| b == .String and std.mem.eql(u8, as, b.String),
    };
}
fn valueIdentical(a: Value, b: Value) bool {
    return valueEq(a, b);
}

fn binaryApply(op: BinaryOp, a: Value, b: Value) Value {
    switch (op) {
        .Add => if (a == .Number and b == .Number) return .{ .Number = a.Number + b.Number } else return .Undefined,
        .Sub => if (a == .Number and b == .Number) return .{ .Number = a.Number - b.Number } else return .Undefined,
        .Mul => if (a == .Number and b == .Number) return .{ .Number = a.Number * b.Number } else return .Undefined,
        .Div => if (a == .Number and b == .Number) return .{ .Number = a.Number / b.Number } else return .Undefined,
        .Mod => if (a == .Number and b == .Number) return .{ .Number = @mod(a.Number, b.Number) } else return .Undefined,
        .Pow => if (a == .Number and b == .Number) return .{ .Number = std.math.pow(f64, a.Number, b.Number) } else return .Undefined,

        .And => if (a == .Number and b == .Number) {
            const ai: i64 = @intFromFloat(a.Number);
            const bi: i64 = @intFromFloat(b.Number);
            return .{ .Number = @floatFromInt(ai & bi) };
        } else return .Undefined,
        .Or => if (a == .Number and b == .Number) {
            const ai: i64 = @intFromFloat(a.Number);
            const bi: i64 = @intFromFloat(b.Number);
            return .{ .Number = @floatFromInt(ai | bi) };
        } else return .Undefined,
        .Xor => if (a == .Number and b == .Number) {
            const ai: i64 = @intFromFloat(a.Number);
            const bi: i64 = @intFromFloat(b.Number);
            return .{ .Number = @floatFromInt(ai ^ bi) };
        } else return .Undefined,
        .Shl => if (a == .Number and b == .Number) return .{ .Number = @floatFromInt(@as(i64, @intFromFloat(a.Number)) << @intCast(u6, @as(i64, @intFromFloat(b.Number)))) } else return .Undefined,
        .Shr => if (a == .Number and b == .Number) return .{ .Number = @floatFromInt(@as(i64, @intFromFloat(a.Number)) >> @intCast(u6, @as(i64, @intFromFloat(b.Number)))) } else return .Undefined,
        .Sar => if (a == .Number and b == .Number) return .{ .Number = @floatFromInt(@as(i64, @intFromFloat(a.Number)) >> @intCast(u6, @as(i64, @intFromFloat(b.Number)))) } else return .Undefined,
        .Sal => if (a == .Number and b == .Number) return .{ .Number = @floatFromInt(@as(i64, @intFromFloat(a.Number)) << @intCast(u6, @as(i64, @intFromFloat(b.Number)))) } else return .Undefined,

        .AndBool => return .{ .Boolean = truthy(a) and truthy(b) },
        .OrBool => return .{ .Boolean = truthy(a) or truthy(b) },

        .Eq => return .{ .Boolean = valueEq(a, b) },
        .Ne => return .{ .Boolean = !valueEq(a, b) },
        .Lt => if (a == .Number and b == .Number) return .{ .Boolean = a.Number < b.Number } else return .{ .Boolean = false },
        .Gt => if (a == .Number and b == .Number) return .{ .Boolean = a.Number > b.Number } else return .{ .Boolean = false },
        .Le => if (a == .Number and b == .Number) return .{ .Boolean = a.Number <= b.Number } else return .{ .Boolean = false },
        .Ge => if (a == .Number and b == .Number) return .{ .Boolean = a.Number >= b.Number } else return .{ .Boolean = false },
        .Id => return .{ .Boolean = valueIdentical(a, b) },
        .Ni => return .{ .Boolean = !valueIdentical(a, b) },
    }
}

fn printValue(w: std.io.AnyWriter, v: Value) !void {
    switch (v) {
        .Undefined => try w.print("undefined\n", .{}),
        .Null => try w.print("null\n", .{}),
        .Boolean => |b| try w.print("{}\n", .{b}),
        .Number => |n| try w.print("{d}\n", .{n}),
        .String => |s| try w.print("{s}\n", .{s}),
    }
}

const NodeBlock = struct {
    ops: []const ir.InstructionMHIR, // view into Program.code (owned by Program)

    pub fn call(self: *NodeBlock, vm: *VM) void {
        // Hot straight-line execution, no virtual dispatch within the block.
        // NOTE: helpers (unaryApply/binaryApply/defaultForType) are small and inline.
        for (self.ops) |inst| {
            switch (inst) {
                .DeclareNewVar => |p| {
                    vm.vals.define(p.var_id, defaultForType(p.typ)) catch {};
                },
                .AssignToExistingVar => |p| {
                    vm.vals.assign(p.dest, p.value, false) catch {};
                },
                .UnaryOperation => |p| {
                    const res = unaryApply(p.op, p.operand);
                    vm.vals.assign(p.dest, res, true) catch {};
                },
                .BinaryOperation => |p| {
                    const res = binaryApply(p.op, p.lhs, p.rhs);
                    vm.vals.assign(p.dest, res, true) catch {};
                },
                .Print => |p| {
                    // If you've switched to a callback printer, call it here.
                    // With AnyWriter:
                    _ = printValue(vm.out, p.value);
                },
                else => {
                    // We never put barriers inside a block; if we see one, bail (paranoia).
                    // In Debug, help catch broken fusion; in Release, just stop the block.
                    if (@import("builtin").mode == .Debug) @panic("Barrier leaked into NodeBlock");
                    return;
                },
            }
        }
    }
};

const DEBUG_UNIMPL_PANIC = true;

const NodeBarrier = struct {
    idx: usize, // instruction index in Program.code (for diagnostics)
    pub fn call(_: *NodeBarrier, vm: *VM) void {
        _ = vm;
        if (DEBUG_UNIMPL_PANIC and @import("builtin").mode == .Debug) {
            @panic("Encountered unimplemented/barrier instruction");
        }
        // Release builds: no-op so partial programs can run.
    }
};

// =====================================
// Direct-threaded nodes (no opcode switch)
// =====================================
const Sig = fn (*VM) void;
const Node = fnkit.ChainedFunction(Sig, 64, 8);

pub const Program = struct {
    nodes: []Node,
    head: ?*const Node,
    code: []ir.InstructionMHIR, // owned copy (blocks slice from this)

    pub fn deinit(self: *Program, alloc: Alloc) void {
        for (self.nodes) |*n| n.deinit(null);
        alloc.free(self.nodes);
        alloc.free(self.code);
    }

    /// Purely chained execution (tail-calls through the block chain).
    pub fn run(self: *const Program, vm: *VM) void {
        if (self.head) |h| {
            // applyAndThen: runs this node and **tail-calls** next
            _ = h.applyAndThen(.{vm});
        }
    }
};

// ---- functors per instruction (unchanged bodies) ----
const NodeDeclareNewVar = struct {
    var_id: ir.VariableId,
    typ: ir.ValueType,
    pub fn call(self: *NodeDeclareNewVar, vm: *VM) void {
        vm.vals.define(self.var_id, defaultForType(self.typ)) catch {};
    }
};

const NodeAssignToExistingVar = struct {
    dest: ir.VariableId,
    value: ir.ValueMHIR,
    pub fn call(self: *NodeAssignToExistingVar, vm: *VM) void {
        vm.vals.assign(self.dest, self.value, false) catch {};
    }
};

const NodeUnary = struct {
    dest: ir.VariableId,
    op: ir.UnaryOperator,
    operand: ir.ValueMHIR,
    pub fn call(self: *NodeUnary, vm: *VM) void {
        const res = unaryApply(self.op, self.operand);
        vm.vals.assign(self.dest, res, true) catch {};
    }
};

const NodeBinary = struct {
    dest: ir.VariableId,
    op: ir.BinaryOperator,
    lhs: ir.ValueMHIR,
    rhs: ir.ValueMHIR,
    pub fn call(self: *NodeBinary, vm: *VM) void {
        const res = binaryApply(self.op, self.lhs, self.rhs);
        vm.vals.assign(self.dest, res, true) catch {};
    }
};

const NodePrint = struct {
    value: ir.ValueMHIR,
    pub fn call(self: *NodePrint, vm: *VM) void {
        printValue(vm.out, self.value) catch {};
    }
};

// =====================================
// Compiler: IR -> direct-threaded chain
// (linking unchanged; only ensure we call `setNext` to build the chain)
// =====================================
inline fn isBlockable(inst: ir.InstructionMHIR) bool {
    return switch (inst) {
        .DeclareNewVar, .AssignToExistingVar, .UnaryOperation, .BinaryOperation, .Print => true,
        else => false,
    };
}

// Optional cap to keep giant blocks from growing too big for I-cache; tune if needed.
const MAX_BLOCK_OPS: usize = 256;

pub fn compile(alloc: Alloc, code_in: []const ir.InstructionMHIR) !Program {
    // Own a single copy of the bytecode; blocks will slice from here.
    var owned = try alloc.dupe(ir.InstructionMHIR, code_in);

    // Worst-case: every instruction is a separate node
    var nodes = try alloc.alloc(Node, owned.len);
    for (nodes) |*n| n.* = Node.initNull();

    var used: usize = 0;
    var i: usize = 0;

    while (i < owned.len) {
        if (isBlockable(owned[i])) {
            const start = i;
            var count: usize = 0;

            // Gather a maximal block of blockable ops
            while (i < owned.len and isBlockable(owned[i]) and count < MAX_BLOCK_OPS) : (i += 1) {
                count += 1;
            }

            // Emit a NodeBlock over owned[start .. start+count)
            var nb = NodeBlock{ .ops = owned[start .. start + count] };
            nodes[used].inner = try Node.fromCallable(alloc, nb);
            used += 1;
        } else {
            // Emit an explicit barrier node (helps debug and preserves positions)
            var nb = NodeBarrier{ .idx = i };
            nodes[used].inner = try Node.fromCallable(alloc, nb);
            used += 1;
            i += 1;
        }
    }

    if (used == 0) {
        alloc.free(nodes);
        alloc.free(owned);
        return .{ .nodes = &[_]Node{}, .head = null, .code = &[_]ir.InstructionMHIR{} };
    }

    // Link the used nodes into a chain
    var last: *Node = &nodes[0];
    var j: usize = 1;
    while (j < used) : (j += 1) {
        last.setNext(&nodes[j]);
        last = @constCast(nodes[j].last());
    }

    // Trim
    if (used != nodes.len) {
        const trimmed = try alloc.alloc(Node, used);
        @memcpy(trimmed, nodes[0..used]);
        alloc.free(nodes);
        nodes = trimmed;
    }

    return .{
        .nodes = nodes,
        .head = &nodes[0],
        .code = owned,
    };
}
