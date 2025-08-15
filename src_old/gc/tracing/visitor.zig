const std = @import("std");
const tracing = @import("tracing.zig");

/// A generic slot visitor callback. Called for each pointer field found in an object or root.
/// The visitor is responsible for invoking `ctx.markObject` on the pointed-to object.
pub const SlotVisitor = struct {
    ctx: *tracing.TracingContext,

    /// Visit a single slot (pointer to an object).
    pub fn visitSlot(self: *SlotVisitor, slot: [*]u8) !void {
        // Client ensures slot is a valid object pointer.
        try self.ctx.markObject(slot);
    }

    /// Visit a slice of slots (e.g., array of object references).
    pub fn visitSlots(self: *SlotVisitor, slots: [][*]u8) !void {
        for (slots) |slot| {
            try self.visitSlot(slot);
        }
    }
};

/// Example root scanner signature for clients.
///
/// Clients implement a function of this form to walk all GC roots.
/// The scanner receives a SlotVisitor to report each root pointer.
pub fn scanRootsExample(visitor: *SlotVisitor) void {
    // Example pseudocode — real client would walk registers, globals, etc.
    // e.g.,
    // for (i in 0..register_count) {
    //     const ptr = get_register(i);
    //     _ = visitor.visitSlot(ptr);
    // }
}

/// Helper to create a SlotVisitor
pub fn makeVisitor(ctx: *tracing.TracingContext) SlotVisitor {
    return SlotVisitor{ .ctx = ctx };
}
