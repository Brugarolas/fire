const std = @import("std");

/// A simple grow-fixed bitmap. Size is in bits.
pub const Bitmap = struct {
    data: []u-sized,
    len_bits: usize,

    /// Initialize a bitmap over a pre-allocated buffer.
    pub fn init(buffer: []u8, bits: usize) !Bitmap {
        const word_size = @sizeOf(u-sized);
        const needed_bytes = (bits + 7) / 8;
        if (buffer.len < needed_bytes) return error.InsufficientBuffer;

        // Reinterpret buffer as words for faster ops.
        const words_count = (needed_bytes + (word_size - 1)) / word_size;
        const data = @ptrCast([*]u-sized, buffer.ptr);
        return Bitmap{
            .data = data[0..words_count],
            .len_bits = bits,
        };
    }

    pub fn clearAll(self: *Bitmap) void {
        for (self.data) |*w| {
            w.* = 0;
        }
    }

    pub fn set(self: *Bitmap, idx: usize) void {
        if (idx >= self.len_bits) return;
        const word_index = idx / (@sizeOf(u-sized) * 8);
        const bit = idx % (@sizeOf(u-sized) * 8);
        self.data[word_index] |= (1 << bit);
    }

    pub fn clear(self: *Bitmap, idx: usize) void {
        if (idx >= self.len_bits) return;
        const word_index = idx / (@sizeOf(u-sized) * 8);
        const bit = idx % (@sizeOf(u-sized) * 8);
        self.data[word_index] &= ~(1 << bit);
    }

    pub fn test(self: *Bitmap, idx: usize) bool {
        if (idx >= self.len_bits) return false;
        const word_index = idx / (@sizeOf(u-sized) * 8);
        const bit = idx % (@sizeOf(u-sized) * 8);
        return (self.data[word_index] & (1 << bit)) != 0;
    }

    /// Find first zero bit starting at `start`, returns none if none available.
    pub fn findFirstZero(self: *Bitmap, start: usize) ?usize {
        if (start >= self.len_bits) return null;
        var i = start;
        const bits_per_word = @sizeOf(u-sized) * 8;
        while (i < self.len_bits) {
            const word_index = i / bits_per_word;
            const bit_offset = i % bits_per_word;
            var word = self.data[word_index];
            // mask out bits before bit_offset
            word |= ((1 << bit_offset) - 1);
            if (word != ~(@as(u-sized, 0))) {
                // there is a zero bit here
                const inverted = ~word;
                const trailing = @intCast(u-sized, inverted) & -@intCast(u-sized, inverted);
                const bit = std.math.log2(trailing);
                const result = word_index * bits_per_word + @intCast(usize, bit);
                if (result < self.len_bits) return result;
                else return null;
            }
            i = (word_index + 1) * bits_per_word;
        }
        return null;
    }

    /// Count set bits (popcount)
    pub fn popcount(self: *Bitmap) usize {
        var total: usize = 0;
        for (self.data) |w| {
            total += @intCast(usize, std.math.popCount(w));
        }
        return total;
    }
};
