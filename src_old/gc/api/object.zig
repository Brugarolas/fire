const std = @import("std");

/// Public object header layout. Placed at object base.
pub const GcObjectHeader = packed struct {
    type_info: *const TypeInfo, // pointer to static type descriptor
    generation: u8,             // 0 = young (nursery), 1 = old
    flags: u8,                  // client / GC flags (e.g., pinned)
    // padding if needed for alignment; header size should be small
};

/// A trace function: given a visitor, visit all child pointers of the object.
pub const TraceFn = fn (ctx: *anytype, visitor: *SlotVisitor, obj: [*]u8) void;

/// TypeInfo describes object size/layout and how to trace its internal references.
pub const TypeInfo = struct {
    size: usize,          // total object size in bytes (including header)
    align: usize,         // alignment of the object
    trace: TraceFn,       // custom trace function for this type
    // optional: a compact bitmap could be embedded here for simple layouts
};

/// SlotVisitor is a lightweight adapter; real visitor type comes from tracing module.
pub const SlotVisitor = struct {
    visit: fn (visitor: *SlotVisitor, slot: [*]u8) !void,
};

/// Convenience helper: mark a child pointer if non-null.
pub fn visitChild(visitor: *SlotVisitor, child: [?*]u8) !void {
    if (child) |ptr| {
        try visitor.visit(visitor, ptr);
    }
}

/// Example: a helper to create a TraceFn from a fixed list of offsets.
/// This is useful for simple object layouts where references are at known offsets.
pub fn makeFixedOffsetsTracer(offsets: []const usize) TraceFn {
    return fn (_ctx: *anytype, visitor: *SlotVisitor, obj: [*]u8) void {
        for (offsets) |off| {
            const slot_ptr = @ptrCast([*]u8, obj + off);
            // assume pointer-sized field
            const child = @ptrCast([*]u8, undefined); // placeholder

            // Read the pointer stored there (unsafe raw load)
            const raw_ptr = @ptrCast([*]usize, slot_ptr).*;
            if (raw_ptr != 0) {
                const child_ptr = @intToPtr([*]u8, raw_ptr);
                _ = visitor.visit(visitor, child_ptr) catch {};
            }
        }
    };
}

/// Example of a manual trace function for a cons cell (two pointers).
pub fn traceConsCell(_ctx: *anytype, visitor: *SlotVisitor, obj: [*]u8) void {
    // Assume layout:
    // [header][car_ptr][cdr_ptr]
    const header_size = @sizeOf(GcObjectHeader);
    const car_ptr_ptr = @ptrCast([*]usize, obj + header_size);
    const cdr_ptr_ptr = @ptrCast([*]usize, obj + header_size + @sizeOf(usize));

    const car_raw = car_ptr_ptr.*;
    if (car_raw != 0) {
        _ = visitor.visit(visitor, @intToPtr([*]u8, car_raw)) catch {};
    }
    const cdr_raw = cdr_ptr_ptr.*;
    if (cdr_raw != 0) {
        _ = visitor.visit(visitor, @intToPtr([*]u8, cdr_raw)) catch {};
    }
}
