const std = @import("std");
const ir = @import("ir");
const vm_mod = @import("vm");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    const stdout_writer = std.io.CountingWriter(std.Io.Writer.Discarding);

    var vm = try vm_mod.VM.init(alloc, stdout_writer);
    defer vm.deinit();

    try vm.enterScope();
    defer vm.exitScope();

    const code = [_]ir.InstructionMHIR{
        // var named "x" : number
        .{ .DeclareNewVar = .{
            .var_id = .{ .LayeredMap = ir.Name.init("x") },
            .typ = .number,
        } },
        // x = 40
        .{ .AssignToExistingVar = .{
            .dest = .{ .LayeredMap = ir.Name.init("x") },
            .value = .{ .Number = 40 },
        } },
        // v2 = 41 + 1
        .{ .BinaryOperation = .{
            .dest = @as(ir.VariableId, 2),
            .op = .Add,
            .lhs = .{ .Number = 41 },
            .rhs = .{ .Number = 1 },
        } },
        // print 42
        .{ .Print = .{ .value = .{ .Number = 42 } } },
    };

    var prog = try vm_mod.compile(alloc, &code);
    defer prog.deinit(alloc);

    prog.run(&vm);
}
