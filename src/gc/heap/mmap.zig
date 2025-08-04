const std = @import("std");

pub const Mmap = struct {
    ptr: [*]u8,
    len: usize,

    pub fn init(len: usize) !Mmap {
        const page_size = std.os.page_size;
        const aligned_len = std.math.alignForward(usize, len, page_size);
        const mapping = try std.os.mmap(
            null, // let OS choose address
            aligned_len,
            std.os.PROT.READ | std.os.PROT.WRITE,
            std.os.MAP.ANONYMOUS | std.os.MAP.PRIVATE,
            -1,
            0,
        );

        return Mmap{
            .ptr = @ptrCast([*]u8, mapping),
            .len = aligned_len,
        };
    }

    pub fn deinit(self: Mmap) !void {
        try std.os.munmap(@ptrCast([*]const u8, self.ptr), self.len);
    }

    pub fn slice(self: Mmap) []u8 {
        return self.ptr[0..self.len];
    }

    pub fn ptrAligned(self: Mmap, align: usize) ![*]u8 {
        if (@intFromPtr(self.ptr) % align != 0) {
            return error.UnalignedMemory;
        }
        return self.ptr;
    }
};
