const std = @import("std");
const Chunk = @import("chunk.zig").Chunk;
const Block = @import("block.zig").Block;
const api = @import("../api/object.zig"); // for object header/type info, adjust path as needed

pub const NurseryConfig = struct {
    // Threshold to trigger a minor collection (e.g., percent full)
    collect_threshold_percent: usize, // 0..100
};

pub const ImmixNursery = struct {
    chunk: Chunk,
    config: NurseryConfig,
    /// Simple allocation cursor for fast path: current block index
    current_block_idx: usize,

    pub fn init() !ImmixNursery {
        return ImmixNursery{
            .chunk = try Chunk.init(),
            .config = .{ .collect_threshold_percent = 80 },
            .current_block_idx = 0,
        };
    }

    pub fn deinit(self: *ImmixNursery) !void {
        try self.chunk.deinit();
    }

    pub fn allocate(self: *ImmixNursery, size: usize, align: usize, type_info: *const api.TypeInfo) ?[*]u8 {
        // Simplified: we assume objects fit within a small number of lines.
        const line_size = @import("block.zig").LINE_SIZE;
        const lines_needed = (size + line_size - 1) / line_size;

        // Try current block first
        var block = self.chunk.getBlock(self.current_block_idx);
        if (block.used_lines + lines_needed > @import("block.zig").LINES_PER_BLOCK) {
            // find next block with space
            const maybe = self.chunk.tryGetFreeBlock();
            if (maybe) |b| {
                block = b;
                self.current_block_idx = (@intCast(usize, b - &self.chunk.blocks[0]));
            } else {
                // nursery is saturated -> signal collection needed
                return null;
            }
        }

        const ptr = block.allocLines(lines_needed);
        if (ptr == null) {
            // fallback: scan for any block with space
            if (self.chunk.tryGetFreeBlock()) |b| {
                block = b;
                self.current_block_idx = (@intCast(usize, b - &self.chunk.blocks[0]));
                const retry = block.allocLines(lines_needed);
                if (retry) |p| {
                    ImmixNursery.writeHeader(p, type_info);
                    return p;
                }
            }
            return null;
        }

        // write object header (after possible header size; here we assume header is at start)
        ImmixNursery.writeHeader(ptr.?, type_info);
        return ptr;
    }

    fn writeHeader(ptr: [*]u8, type_info: *const api.TypeInfo) void {
        // Client is responsible for layout; naive example of placing header at front
        const header = @ptrCast(*api.GcObjectHeader, ptr);
        header.* = api.GcObjectHeader{
            .type_info = type_info,
            .generation = 0,
            .flags = 0,
        };
    }

    pub fn shouldCollect(self: *ImmixNursery) bool {
        // Simple fullness heuristic
        var total_used_lines: usize = 0;
        const total_lines = @import("block.zig").LINES_PER_BLOCK * self.chunk.blockCount();
        for (self.chunk.blocks) |*block| {
            total_used_lines += block.used_lines;
        }
        const used_percent = (total_used_lines * 100) / total_lines;
        return used_percent >= self.config.collect_threshold_percent;
    }

    /// Perform a minor collection. Caller must supply root scanner and a promotion callback.
    pub fn collectMinor(self: *ImmixNursery, root_scanner: fn (*TracingContext) void, promote: fn ([*]u8) void) void {
        // 1. Mark live objects reachable from roots within nursery.
        // (TracingContext would encapsulate mark stacks, visited set, etc.)
        var tracing_ctx = TracingContext.init(); // placeholder; define in tracing module
        root_scanner(&tracing_ctx);

        // 2. Walk marked objects in nursery and invoke promotion callback.
        for (self.chunk.blocks) |*block| {
            for (line_idx: usize = 0; line_idx < @import("block.zig").LINES_PER_BLOCK; line_idx += 1) {
                if (block.line_marked[line_idx]) {
                    const obj_addr = block.start + (line_idx * @import("block.zig").LINE_SIZE);
                    promote(obj_addr);
                } else if (block.line_used[line_idx]) {
                    // dead: reclaim line
                    block.line_used[line_idx] = false;
                    block.used_lines -= 1;
                }
                // reset mark for next time
                block.line_marked[line_idx] = false;
            }
            // optionally set recyclable flag if block is empty
            if (block.used_lines == 0) {
                block.recyclable = true;
            }
        }

        // 3. Reset current block if it became full/empty policy
        if (self.chunk.getBlock(self.current_block_idx).used_lines == @import("block.zig").LINES_PER_BLOCK) {
            // pick another block
            if (self.chunk.tryGetFreeBlock()) |b| {
                self.current_block_idx = (@intCast(usize, b - &self.chunk.blocks[0]));
            }
        }
    }
};

/// Placeholder for the tracing context; real implementation lives in tracing/tracing.zig
pub const TracingContext = struct {
    // mark stack, visited set, etc.
    pub fn init() TracingContext {
        return TracingContext{};
    }
};
