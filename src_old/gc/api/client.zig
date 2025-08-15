const std = @import("std");
const tracing = @import("../tracing/tracing.zig");
const visitor_mod = @import("../tracing/visitor.zig");
const object_mod = @import("object.zig");

pub const GcClient = struct {
    /// Called to scan all roots. The VM implements this to visit registers/globals/etc.
    scanRoots: fn (visitor: *visitor_mod.SlotVisitor) void,

    /// Given an object pointer, scan its internal pointer fields.
    scanObject: fn (ctx: *tracing.TracingContext, obj: [*]u8) void,

    /// Optional: callback when object is promoted (young -> old)
    onPromote: ?fn (obj: [*]u8) void,
};

/// A simple GC run driver: performs a full mark (using provided scan functions) and leaves
/// the marked set populated in `ctx`.
pub fn fullMark(ctx: *tracing.TracingContext, client: *GcClient) void {
    // Create root visitor
    var root_visitor = visitor_mod.makeVisitor(ctx);
    client.scanRoots(&root_visitor);

    // Trace reachable objects
    traceWithClient(ctx, client);
}

pub fn traceWithClient(ctx: *tracing.TracingContext, client: *GcClient) void {
    // Wrap scanObject to match expected signature
    const scan_wrapper = fn (ctx_inner: *tracing.TracingContext, obj: [*]u8) void {
        client.scanObject(ctx_inner, obj);
    };
    tracing.trace(ctx, scan_wrapper);
}

/// Helper to mark a root object manually.
pub fn markRoot(ctx: *tracing.TracingContext, obj: [*]u8) !void {
    try ctx.markObject(obj);
}
