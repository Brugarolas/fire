const std = @import("std");

pub const BLOCK_SIZE = 32 * 1024;     // 32KB
pub const LINE_SIZE = 256;            // 256B
pub const LINES_PER_BLOCK = BLOCK_SIZE / LINE_SIZE;

pub const Block = struct {
    start: [*]u8, // start of block memory (slice of mmap)
    line_used: [LINES_PER_BLOCK]bool,
    line_marked: [LINES_PER_BLOCK]bool,
    cursor: usize, // next free line index
    recyclable: bool,
    used_lines: usize,

    pub fn init(start: [*]u8) Block {
        return Block{
            .start = start,
            .line_used = [_]bool{false} ** LINES_PER_BLOCK,
            .line_marked = [_]bool{false} ** LINES_PER_BLOCK,
            .cursor = 0,
            .recyclable = false,
            .used_lines = 0,
        };
    }

    /// Try to allocate `n` contiguous lines. Returns pointer to start, or null.
    pub fn allocLines(self: *Block, n: usize) ?[*]u8 {
        var i: usize = self.cursor;
        while (i + n <= LINES_PER_BLOCK) {
            var free = true;
            for (j: usize = 0; j < n; j += 1) {
                if (self.line_used[i + j]) {
                    free = false;
                    break;
                }
            }
            if (free) {
                for (j: usize = 0; j < n; j += 1) {
                    self.line_used[i + j] = true;
                }
                self.cursor = i + n;
                self.used_lines += n;
                return self.start + (i * LINE_SIZE);
            }
            i += 1;
        }
        return null;
    }

    pub fn resetLines(self: *Block) void {
        self.line_used = [_]bool{false} ** LINES_PER_BLOCK;
        self.line_marked = [_]bool{false} ** LINES_PER_BLOCK;
        self.cursor = 0;
        self.used_lines = 0;
        self.recyclable = false;
    }

    pub fn markLine(self: *Block, addr: [*]u8) void {
        const offset = @intFromPtr(addr) - @intFromPtr(self.start);
        const index = offset / LINE_SIZE;
        if (index < LINES_PER_BLOCK)
            self.line_marked[index] = true;
    }

    pub fn isMarked(self: *Block, addr: [*]u8) bool {
        const offset = @intFromPtr(addr) - @intFromPtr(self.start);
        const index = offset / LINE_SIZE;
        return index < LINES_PER_BLOCK and self.line_marked[index];
    }
};
