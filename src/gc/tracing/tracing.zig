const std = @import("std");
const gc_work = @import("gc_work.zig");
const api = @import("../api/object.zig");

pub const TracingContext = struct {
    // Marked set: client can choose bitmap per object or global; here simple pointer set.
    marked: std.AutoHashMap([*]u8, bool),
    global_queue: gc_work.GlobalQueue,
    workers: []gc_work.WorkerQueue,
    allocator: *std.mem.Allocator,

    pub fn init(allocator: *std.mem.Allocator, worker_count: usize) !TracingContext {
        var map = std.AutoHashMap([*]u8, bool).init(allocator);
        var global_q = try gc_work.GlobalQueue.init(allocator);

        // allocate array for workers
        var workers_buf = try allocator.alloc(gc_work.WorkerQueue, worker_count);
        var workers_slice = workers_buf[0..worker_count];
        var i: usize = 0;
        while (i < worker_count) : (i += 1) {
            workers_slice[i] = try gc_work.WorkerQueue.init(allocator, &global_q);
        }

        return TracingContext{
            .marked = map,
            .global_queue = global_q,
            .workers = workers_slice,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *TracingContext) void {
        self.marked.deinit();
        self.global_queue.deinit();
        for (self.workers) |*w| {
            w.deinit();
        }
        // assume allocator cleanup is caller's responsibility
    }

    pub fn markObject(self: *TracingContext, obj: [*]u8) !void {
        // Deduplicate
        const exists = self.marked.get(obj);
        if (exists) |*v| {
            return;
        }
        try self.marked.put(obj, true);
        // enqueue for traversal (push to global so any worker can grab)
        try self.global_queue.push(obj);
    }
};

/// Core tracing/mark loop, parallelized across workers.
/// `scanObject` is provided by the client: given object pointer and a tracer callback to recursively mark children.
pub fn trace(ctx: *TracingContext, scanObject: fn (*TracingContext, [*]u8) void) void {
    const thread_count = ctx.workers.len;

    var thread_handles: [32]?*std.Thread.Thread = undefined; // up to 32
    var i: usize = 0;
    while (i < thread_count) : (i += 1) {
        const worker = &ctx.workers[i];
        thread_handles[i] = try std.Thread.spawn(.{}, workerThread, .{
            ctx,
            &ctx.workers[i],
            scanObject,
        });
    }

    // Wait for all threads
    i = 0;
    while (i < thread_count) : (i += 1) {
        if (thread_handles[i]) |handle| {
            _ = handle.wait();
        }
    }
}

const WorkerArgs = struct {
    ctx: *TracingContext,
    worker: *gc_work.WorkerQueue,
    scanObject: fn (*TracingContext, [*]u8) void,
};

fn workerThread(arg: anytype) void {
    const a = @fieldParentPtr(WorkerArgs, "ctx", &arg);
    const ctx = a.ctx;
    const worker = a.worker;
    const scanObject = a.scanObject;

    while (true) {
        const maybe = worker.pop();
        if (maybe) |obj| {
            // Scan children
            scanObject(ctx, obj);
        } else {
            // no work left; exit
            break;
        }
    }
}
