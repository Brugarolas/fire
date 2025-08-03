const std = @import("std");

pub fn main() !void {
    // Standard allocator for dynamic memory allocation
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit(); // Ensures memory cleanup
    //const allocator = &arena.allocator;

    // Simple hello world print
    std.debug.print("Hello, {s}!\n", .{"World"});

    // Basic type inference
    const count = 10;

    // For loop demonstration
    for (0..count) |i| {
        std.debug.print("Count: {d}\n", .{i});
    }

    // Error handling example
    if (try mayFail(false)) {
        std.debug.print("Success!\n", .{});
    } else {
        std.debug.print("Failure!\n", .{});
    }

    // Demonstrate slices and arrays
    const numbers = [_]i32{ 1, 2, 3, 4, 5 };
    const slice = numbers[1..4];
    std.debug.print("Slice: {any}\n", .{slice});

    // Demonstrating structs
    const point = Point{ .x = 3, .y = 4 };
    std.debug.print("Point: ({d}, {d})\n", .{ point.x, point.y });
}

// Struct example
test "Point struct test" {
    const p = Point{ .x = 1, .y = 2 };
    try std.testing.expect(p.x == 1 and p.y == 2);
}

const Point = struct {
    x: i32,
    y: i32,
};

// Example of function returning error union
fn mayFail(success: bool) !bool {
    if (success) return true;
    return error.Failure;
}

// Define a custom error set
const error_ = error{Failure};
