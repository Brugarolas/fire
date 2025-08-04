const std = @import("std");
const mmap = @import("mmap.zig");
const Block = @import("block.zig").Block;
const BLOCK_SIZE = @import("block.zig").BLOCK_SIZE;

pub const BLOCKS_PER_CHUNK = 512;
pub const CHUNK_SIZE = BLOCK_SIZE * BLOCKS_PER_CHUNK;

pub const Chunk = struct {
    mem: mmap.Mmap,
    blocks: [BLOCKS_PER_CHUNK]Block,

    pub fn init() !Chunk {
        const mem = try mmap.Mmap.init(CHUNK_SIZE);
        var blocks: [BLOCKS_PER_CHUNK]Block = undefined;

        var i: usize = 0;
        while (i < BLOCKS_PER_CHUNK) : (i += 1) {
            const offset = i * BLOCK_SIZE;
            blocks[i] = Block.init(mem.ptr + offset);
        }

        return Chunk{
            .mem = mem,
            .blocks = blocks,
        };
    }

    pub fn deinit(self: *Chunk) !void {
        try self.mem.deinit();
    }

    pub fn getBlock(self: *Chunk, index: usize) *Block {
        return &self.blocks[index];
    }

    pub fn forEachBlock(self: *Chunk, f: fn (*Block) void) void {
        for (self.blocks) |*block| {
            f(block);
        }
    }

    pub fn blockCount(self: *Chunk) usize {
        return BLOCKS_PER_CHUNK;
    }

    /// Fast block ownership lookup (optional, unsafe unless carefully bounded)
    pub fn findBlockContaining(self: *Chunk, ptr: [*]u8) ?*Block {
        const base = @intFromPtr(self.mem.ptr);
        const end = base + CHUNK_SIZE;
        const addr = @intFromPtr(ptr);

        if (addr < base or addr >= end) return null;

        const index = (addr - base) / BLOCK_SIZE;
        return &self.blocks[index];
    }

    /// Returns the first block that has unused lines.
    pub fn tryGetFreeBlock(self: *Chunk) ?*Block {
        for (self.blocks) |*block| {
            if (block.used_lines < block.LINES_PER_BLOCK)
                return block;
        }
        return null;
    }

    /// Resets all block metadata — typically used for nursery collection.
    pub fn resetAllBlocks(self: *Chunk) void {
        for (self.blocks) |*block| {
            block.resetLines();
        }
    }

    /// Count how many blocks are fully used, or recyclable
    pub fn countStats(self: *Chunk) struct {
        used: usize,
        recyclable: usize,
    } {
        var used: usize = 0;
        var recyclable: usize = 0;
        for (self.blocks) |*block| {
            if (block.used_lines > 0) used += 1;
            if (block.recyclable) recyclable += 1;
        }
        return .{ .used = used, .recyclable = recyclable };
    }
};
