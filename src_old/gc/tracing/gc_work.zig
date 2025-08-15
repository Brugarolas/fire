const std = @import("std");

/// A simple lock-free-ish work queue for GC marking. Each worker has its own local stack and
/// can steal from others. This is a minimal version; you can swap in more advanced
/// work-stealing later (deque, etc.).
pub const WorkItem = [*]u8; // pointer to object header

pub const WorkerQueue = struct {
    arena: *std.heap.ArenaAllocator, // for dynamic arrays if needed
    local_stack: std.ArrayList(WorkItem),
    /// Shared global queue for fallback stealing (protected by a mutex here for simplicity)
    global: *GlobalQueue,

    pub fn init(allocator: *std.mem.Allocator, global: *GlobalQueue) !WorkerQueue {
        var list = try std.ArrayList(WorkItem).init(allocator);
        return WorkerQueue{
            .arena = null, // unused for now
            .local_stack = list,
            .global = global,
        };
    }

    pub fn deinit(self: *WorkerQueue) void {
        self.local_stack.deinit();
    }

    pub fn push(self: *WorkerQueue, item: WorkItem) !void {
        try self.local_stack.append(item);
    }

    pub fn pop(self: *WorkerQueue) ?WorkItem {
        if (self.local_stack.len > 0) {
            return self.local_stack.pop();
        }
        // fallback to global
        return self.global.steal();
    }
};

pub const GlobalQueue = struct {
    mutex: std.Thread.Mutex,
    queue: std.ArrayList(WorkItem),

    pub fn init(allocator: *std.mem.Allocator) !GlobalQueue {
        var q = try std.ArrayList(WorkItem).init(allocator);
        return GlobalQueue{
            .mutex = std.Thread.Mutex.init(),
            .queue = q,
        };
    }

    pub fn deinit(self: *GlobalQueue) void {
        self.queue.deinit();
        self.mutex.deinit();
    }

    pub fn push(self: *GlobalQueue, item: WorkItem) !void {
        const guard = self.mutex.lock();
        _ = try self.queue.append(item);
        guard.unlock();
    }

    pub fn steal(self: *GlobalQueue) ?WorkItem {
        const guard = self.mutex.lock();
        if (self.queue.len == 0) {
            guard.unlock();
            return null;
        }
        const item = self.queue.pop();
        guard.unlock();
        return item;
    }
};
