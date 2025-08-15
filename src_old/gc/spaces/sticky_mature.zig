const std = @import("std");
const Chunk = @import("chunk.zig").Chunk;
const Block = @import("block.zig").Block;
const api = @import("../api/object.zig"); // adjust path as needed
const tracing = @import("../tracing/tracing.zig");

pub const StickyOldSpaceConfig = struct {
    promotion_threshold_lines: usize, // e.g., minimum surviving lines to keep object here
};

pub const StickyOldSpace = struct {
    chunk: Chunk,
    config: StickyOldSpaceConfig,

    pub fn init() !StickyOldSpace {
        return StickyOldSpace{
            .chunk = try Chunk.init(),
            .config = .{ .promotion_threshold_lines = 1 },
        };
    }

    pub fn deinit(self: *StickyOldSpace) !void {
        try self.chunk.deinit();
    }

    /// Receive a promoted object from nursery. It is already alive; place into old space.
    pub fn promote(self: *StickyOldSpace, obj_ptr: [*]u8, size: usize, type_info: *const api.TypeInfo) void {
        // Determine lines needed and allocate in an old block
        const line_size = @import("block.zig").LINE_SIZE;
        const lines_needed = (size + line_size - 1) / line_size;

        var target_block: ?*Block = null;
        // simple first-fit
        for (self.chunk.blocks) |*block| {
            if (block.used_lines + lines_needed <= @import("block.zig").LINES_PER_BLOCK) {
                target_block = block;
                break;
            }
        }
        if (target_block == null) {
            // In a full implementation, allocate a new chunk or trigger full GC
            return;
        }

        const ptr = target_block.?.allocLines(lines_needed);
        if (ptr == null) return; // fallback omitted for brevity

        // Copy object data from nursery to old space (shallow copy; client handles interior)
        std.mem.copy(u8, ptr.?, obj_ptr[0..size]);

        // Write header
        const header = @ptrCast(*api.GcObjectHeader, ptr.?);
        header.* = api.GcObjectHeader{
            .type_info = type_info,
            .generation = 1,
            .flags = 0,
        };

        // Mark the lines as sticky/live for first collection
        for (line_idx: usize = 0; line_idx < lines_needed; line_idx += 1) {
            target_block.?.line_marked[target_block.?.cursor - lines_needed + line_idx] = true;
        }
    }

    /// Full collection for old space using sticky immix semantics.
    pub fn collectFull(self: *StickyOldSpace, root_scanner: fn (*tracing.TracingContext) void) void {
        var ctx = tracing.TracingContext.init();

        // 1. Mark phase: walk roots and recursively mark.
        root_scanner(&ctx);
        tracing.trace(&ctx);

        // 2. Sweep phase: For each block, determine which lines are dead.
        for (self.chunk.blocks) |*block| {
            // If a line is marked live during this collection, clear its temporary mark but set sticky mark.
            for (line_idx: usize = 0; line_idx < @import("block.zig").LINES_PER_BLOCK; line_idx += 1) {
                if (block.line_marked[line_idx]) {
                    // survivor: reinforce sticky (nothing to do if we treat line_marked as sticky)
                    // Clear temporary mark after copying semantics if any
                } else if (block.line_used[line_idx]) {
                    // dead line: only reclaim if it has been unmarked across *two* collections or policy allows.
                    // For simplicity: if previously unsticky (we track via recyclable), reclaim.
                    if (!block.recyclable) {
                        // mark for reclamation next time
                        block.recyclable = true;
                    } else {
                        // reclaim now
                        block.line_used[line_idx] = false;
                        block.used_lines -= 1;
                    }
                }
                // reset temporary mark for next cycle
                block.line_marked[line_idx] = false;
            }
            if (block.used_lines == 0) {
                block.recyclable = true;
            }
        }
    }

    /// Simple write barrier: when an old object gets a pointer to a young object.
    pub fn writeBarrier(old_obj: [*]u8, field_offset: usize, new_child: [*]u8) void {
        // Client can use this to record old-to-young references.
        // E.g., add to remembered set (not implemented here).
        _ = old_obj;
        _ = field_offset;
        _ = new_child;
    }
};

