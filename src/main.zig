const std = @import("std");
const ir = @import("ir");
const vm_mod = @import("vm");

pub fn main() !void {
    // Allocator
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const alloc = gpa.allocator();

    // VM with stdout as the sink for Print
    var vm = try vm_mod.VM.init(alloc, std.io.getStdOut().writer());
    defer vm.deinit();

    // Optional: add a fresh scope (ValueManager already has one)
    try vm.enterScope();
    defer vm.exitScope();

    // --- Program (IR only): declare, assign, sum, print ---
    // Note: our BinaryOperation takes immediate Values; it doesn’t read variables yet.
    //       This still demonstrates the fused block execution.
    const code = [_]ir.InstructionMHIR{
        .{ .DeclareNewVar = .{ .var_id = 1, .typ = .number } }, // var #1 : number
        .{ .AssignToExistingVar = .{ .dest = 1, .value = .{ .Number = 40 } } }, // #1 = 40
        .{
            .BinaryOperation = .{
                .dest = 2,
                .op = .Add, // #2 = 41 + 1 = 42
                .lhs = .{ .Number = 41 },
                .rhs = .{ .Number = 1 },
            },
        },
        .{ .Print = .{ .value = .{ .Number = 42 } } }, // print 42
    };

    // Compile with block fusion and run
    var prog = try vm_mod.compile(alloc, &code);
    defer prog.deinit(alloc);

    prog.run(&vm);
}
