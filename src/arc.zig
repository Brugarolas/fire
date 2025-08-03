// Copyright (c) 2023 Cyber (See LICENSE)

/// Runtime memory management with ARC (sharded per-thread locals + cycle GC).
const std = @import("std");
const builtin = @import("builtin");
const stdx = @import("stdx");
pub const log = cy.log.scoped(.arc);
const cy = @import("cyber.zig");
const c = @import("capi.zig");
const vmc = cy.vmc;
const rt = cy.rt;
const bt = cy.types.BuiltinTypes;
const build_options = @import("build_options");
const log_mem = build_options.log_mem;

const Atomic = std.atomic;

// ---------------------------
// Fast allocator (pluggable).
// ---------------------------
pub const FastAlloc = struct {
    pub fn allocator() std.mem.Allocator {
        inline for (.{ "fast_alloc", "mimalloc", "rpmalloc" }) |name| {
            if (@hasDecl(@import("root"), name)) {
                return @field(@import("root"), name).allocator();
            }
        }
        return std.heap.c_allocator;
    }
};

// ---------------------------------------------
// TLS locals keyed by (vm, obj) to avoid alias.
// ---------------------------------------------
const Key = struct {
    vm: *cy.VM,
    obj: *cy.HeapObject,
};

fn hashKey(_: void, k: Key) u64 {
    var h = std.hash.Wyhash.init(0);
    h.update(std.mem.asBytes(&k.vm));
    h.update(std.mem.asBytes(&k.obj));
    return h.final();
}
fn eqlKey(a: Key, b: Key) bool {
    return a.vm == b.vm and a.obj == b.obj;
}

const ThreadRc = struct {
    map: std.HashMapUnmanaged(Key, u32, hashKey, eqlKey, true) = .{},
    alloc: std.mem.Allocator,

    fn init() ThreadRc {
        return .{ .alloc = FastAlloc.allocator() };
    }
    fn deinit(self: *ThreadRc) void {
        self.map.deinit(self.alloc);
    }
};

threadlocal var tls_rc: ?ThreadRc = null;

inline fn tls() *ThreadRc {
    if (tls_rc == null) {
        tls_rc = ThreadRc.init();
    }
    return &tls_rc.?;
}

// -----------------------------------------
// Reserved-roots registry (per *VM*).
// Keeps objects that are *reserved* via
// cross-thread send but not yet installed.
// -----------------------------------------
const ReservedRoots = struct {
    mutex: std.Thread.Mutex = .{},
    map: std.AutoHashMapUnmanaged(*cy.HeapObject, u32) = .{},

    fn inc(self: *ReservedRoots, obj: *cy.HeapObject) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        var g = self.map.getOrPut(FastAlloc.allocator(), obj) catch cy.fatal();
        if (g.found_existing) {
            g.value_ptr.* += 1;
        } else {
            g.value_ptr.* = 1;
        }
    }

    fn dec(self: *ReservedRoots, obj: *cy.HeapObject) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        const p = self.map.getPtr(obj) orelse return;
        if (p.* <= 1) {
            _ = self.map.remove(obj);
        } else {
            p.* -= 1;
        }
    }

    fn markAll(self: *ReservedRoots, vm: *cy.VM) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        var it = self.map.iterator();
        while (it.next()) |e| {
            // Treat reservations as GC roots.
            const v = cy.Value.initNoCycPtr(e.key_ptr.*);
            markValue(vm, v);
        }
    }
};

// Global map VM -> ReservedRoots*
var g_vm_roots: std.AutoHashMapUnmanaged(*cy.VM, *ReservedRoots) = .{};
var g_vm_roots_mtx: std.Thread.Mutex = .{};

fn getReservedRoots(vm: *cy.VM) *ReservedRoots {
    g_vm_roots_mtx.lock();
    defer g_vm_roots_mtx.unlock();

    var g = g_vm_roots.getOrPut(FastAlloc.allocator(), vm) catch cy.fatal();
    if (g.found_existing) return g.value_ptr.*;
    const rr = FastAlloc.allocator().create(ReservedRoots) catch cy.fatal();
    rr.* = .{};
    g.value_ptr.* = rr;
    return rr;
}

// Optionally call on VM teardown if you want to reclaim memory.
// Safe to omit (process-lifetime structures).
pub fn arcUnregisterVM(vm: *cy.VM) void {
    g_vm_roots_mtx.lock();
    defer g_vm_roots_mtx.unlock();
    const rr = g_vm_roots.fetchRemove(vm) orelse return;
    rr.value.map.deinit(FastAlloc.allocator());
    FastAlloc.allocator().destroy(rr.value);
}

// ------------------------------
// Atomic helpers on head.rc
// (shard count across threads).
// ------------------------------
inline fn shardsLoad(obj: *cy.HeapObject) u32 {
    // For logging / sweep checks.
    return @atomicLoad(u32, &obj.head.rc, .Relaxed);
}
inline fn shardsAdd1(obj: *cy.HeapObject) void {
    _ = @atomicRmw(u32, &obj.head.rc, .Add, 1, .Relaxed);
}
inline fn shardsSub1(obj: *cy.HeapObject) u32 {
    // Return *previous* count so we can detect last shard.
    return @atomicRmw(u32, &obj.head.rc, .Sub, 1, .Release);
}

inline fn addNoOverflow(x: u32, y: u32, what: []const u8) u32 {
    const s = @addWithOverflow(x, y);
    if (s[1] == 1) cy.panic(what);
    return s[0];
}

// --------------------------------------
// Cross-thread reservation (Option 1).
// --------------------------------------

/// Sender MUST call before enqueueing `obj` to another thread.
/// Debug: assert sender still holds a local.
pub inline fn reserveForRemote(vm: *cy.VM, obj: *cy.HeapObject) void {
    if (cy.Trace) {
        const has_local = tls().map.contains(.{ .vm = vm, .obj = obj });
        std.debug.assert(has_local); // contract: sender owns a local
    }
    shardsAdd1(obj); // keep object alive globally
    getReservedRoots(vm).inc(obj); // make it a GC root
}

/// Receiver MUST call this after dequeue. If `reserved` is true,
/// the reservation will be consumed (removed from reserved-roots).
/// If the receiver already had locals, we cancel the extra shard.
pub inline fn installFromRemote(vm: *cy.VM, obj: *cy.HeapObject, reserved: bool) void {
    var t = tls();
    const key = Key{ .vm = vm, .obj = obj };
    var gop = t.map.getOrPut(t.alloc, key) catch cy.fatal();

    if (gop.found_existing) {
        // Already had locals on this thread.
        gop.value_ptr.* = addNoOverflow(gop.value_ptr.*, 1, "local refcount overflow");
        // Cancel sender's shard.
        _ = shardsSub1(obj);
        if (cy.TrackGlobalRC) vm.c.refCounts -= 1;
    } else {
        gop.value_ptr.* = 1;
        if (!reserved) {
            // No reservation provided; create shard now.
            shardsAdd1(obj);
            if (cy.TrackGlobalRC) vm.c.refCounts += 1;
        }
    }

    if (reserved) getReservedRoots(vm).dec(obj);
}

// Convenience overloads for Value.
pub inline fn reserveForRemoteVal(vm: *cy.VM, val: cy.Value) void {
    if (val.isPointer()) reserveForRemote(vm, val.asHeapObject());
}
pub inline fn installFromRemoteVal(vm: *cy.VM, val: cy.Value, reserved: bool) void {
    if (val.isPointer()) installFromRemote(vm, val.asHeapObject(), reserved);
}

// ------------------------------
// Public retain/release surface.
// ------------------------------
pub fn release(vm: *cy.VM, val: cy.Value) void {
    if (cy.Trace) vm.c.trace.numReleaseAttempts += 1;
    if (!val.isPointer()) {
        log.tracevIf(log_mem, "release: {s}, nop", .{vm.getTypeName(val.getTypeId())});
        return;
    }
    releaseObject(vm, val.asHeapObject());
}

pub fn isObjectAlreadyFreed(vm: *cy.VM, obj: *cy.HeapObject) bool {
    if (obj.isFreed()) return true;
    if (vm.objectTraceMap.get(obj)) |trace| {
        if (trace.free_pc != null) return true;
    }
    return false;
}

pub fn checkDoubleFree(vm: *cy.VM, obj: *cy.HeapObject) void {
    if (isObjectAlreadyFreed(vm, obj)) {
        const msg = std.fmt.allocPrint(vm.alloc, "{*} at pc: {}({s})", .{
            obj, vm.c.debugPc, @tagName(vm.c.ops[vm.c.debugPc].opcode()),
        }) catch cy.fatal();
        defer vm.alloc.free(msg);
        cy.debug.printTraceAtPc(vm, vm.c.debugPc, "double free", msg) catch cy.fatal();
        cy.debug.dumpObjectTrace(vm, obj) catch cy.fatal();
        cy.fatal();
    }
}

pub fn releaseObject(vm: *cy.VM, obj: *cy.HeapObject) void {
    if (cy.Trace) {
        checkDoubleFree(vm, obj);
        vm.c.trace.numReleaseAttempts += 1;
    }

    var t = tls();
    const key = Key{ .vm = vm, .obj = obj };
    const vp = t.map.getPtr(key) orelse {
        cy.panic("releaseObject without local hold");
        return;
    };

    // Drop local with underflow guard.
    if (vp.* == 0) cy.panic("local rc underflow");
    vp.* -= 1;

    if (vp.* != 0) {
        if (cy.Trace) vm.c.trace.numReleases += 1;
        if (cy.TraceRC) {
            log.tracevIf(log_mem, "{} -1 release(local): {s}", .{
                shardsLoad(obj), vm.getTypeName(obj.getTypeId()),
            });
        }
        return;
    }

    // Last local on this thread: clear from TLS and drop shard.
    _ = t.map.remove(key);

    if (cy.TraceRC) {
        log.tracevIf(log_mem, "{} -1 release(shard): {s}", .{
            shardsLoad(obj), vm.getTypeName(obj.getTypeId()),
        });
    }

    const prev = shardsSub1(obj); // old value
    if (cy.TrackGlobalRC) vm.c.refCounts -= 1;
    if (cy.Trace) vm.c.trace.numReleases += 1;

    if (prev == 1) {
        // We dropped the last shard across all threads; we own destruction.
        std.atomic.threadFence(.Acquire);
        @call(.never_inline, cy.heap.freeObject, .{ vm, obj, false });
        if (cy.Trace and vm.countFrees) vm.numFreed += 1;
    }
}

pub inline fn retainObject(self: *cy.VM, obj: *cy.HeapObject) void {
    if (cy.Trace) {
        checkRetainDanglingPointer(self, obj);
        self.c.trace.numRetainAttempts += 1;
    }

    var t = tls();
    const key = Key{ .vm = self, .obj = obj };
    var gop = t.map.getOrPut(t.alloc, key) catch cy.fatal();
    if (gop.found_existing) {
        gop.value_ptr.* = addNoOverflow(gop.value_ptr.*, 1, "local refcount overflow");
    } else {
        gop.value_ptr.* = 1; // first local on this thread
        shardsAdd1(obj); // create/own shard
        if (cy.TrackGlobalRC) self.c.refCounts += 1;
    }

    if (cy.Trace) {
        self.c.trace.numRetains += 1;
        log.tracevIf(log_mem, "{} +1 retain(shard/local): {s}", .{
            shardsLoad(obj), self.getTypeName(obj.getTypeId()),
        });
    }
}

const Root = @This();

pub const VmExt = struct {
    pub const retainObject = Root.retainObject;
    pub const retain = Root.retain;
    pub const releaseObject = Root.releaseObject;
    pub const release = Root.release;
};

pub fn checkRetainDanglingPointer(vm: *cy.VM, obj: *cy.HeapObject) void {
    if (isObjectAlreadyFreed(vm, obj)) {
        const msg = std.fmt.allocPrint(vm.alloc, "{*} at pc: {}({s})", .{
            obj, vm.c.debugPc, @tagName(vm.c.ops[vm.c.debugPc].opcode()),
        }) catch cy.fatal();
        defer vm.alloc.free(msg);
        cy.debug.printTraceAtPc(vm, vm.c.debugPc, "retain dangling ptr", msg) catch cy.fatal();

        if (cy.Trace) {
            cy.debug.dumpObjectTrace(vm, obj) catch cy.fatal();
        }
        cy.fatal();
    }
}

pub inline fn retain(self: *cy.VM, val: cy.Value) void {
    if (cy.Trace) self.c.trace.numRetainAttempts += 1;
    if (!val.isPointer()) return;
    retainObject(self, val.asHeapObject());
}

pub inline fn retainInc(self: *cy.VM, val: cy.Value, inc: u32) void {
    if (inc == 0) return;
    if (cy.Trace) self.c.trace.numRetainAttempts += inc;
    if (!val.isPointer()) return;

    const obj = val.asHeapObject();
    if (cy.Trace) checkRetainDanglingPointer(self, obj);

    var t = tls();
    const key = Key{ .vm = self, .obj = obj };
    var gop = t.map.getOrPut(t.alloc, key) catch cy.fatal();

    if (gop.found_existing) {
        gop.value_ptr.* = addNoOverflow(gop.value_ptr.*, inc, "local refcount overflow");
    } else {
        // First local on this thread: all incs are local; shard +1 only.
        gop.value_ptr.* = inc;
        shardsAdd1(obj);
        if (cy.TrackGlobalRC) self.c.refCounts += 1;
    }

    if (cy.Trace) {
        self.c.trace.numRetains += inc;
        log.tracevIf(log_mem, "{} +{} retainInc(local): {s}", .{
            shardsLoad(obj), inc, self.getTypeName(obj.getTypeId()),
        });
    }
}

pub fn getGlobalRC(self: *const cy.VM) usize {
    if (cy.TrackGlobalRC) {
        return self.c.refCounts;
    } else {
        cy.panic("Enable TrackGlobalRC.");
    }
}

// --------------------------------------
// GC: mark/sweep for cyclable objects.
// Reserved roots are marked, and sweep
// conservatively skips shards>0.
// --------------------------------------
pub fn performGC(vm: *cy.VM) !c.GCResult {
    log.tracev("Run gc.", .{});
    try performMark(vm);

    // Make sure dummy node has mark bit.
    cy.vm.dummyCyclableHead.typeId = vmc.GC_MARK_MASK | bt.Void;

    return try performSweep(vm);
}

fn performMark(vm: *cy.VM) !void {
    log.tracev("Perform mark.", .{});
    try markMainStackRoots(vm);

    // Mark globals & context vars.
    for (vm.c.getVarSyms().items()) |sym| {
        if (sym.value.isCycPointer()) markValue(vm, sym.value);
    }
    for (vm.c.getContextVars().items()) |context_var| {
        if (context_var.value.isCycPointer()) markValue(vm, context_var.value);
    }

    // Mark cross-thread reservations (off-heap roots).
    getReservedRoots(vm).markAll(vm);
}

fn performSweep(vm: *cy.VM) !c.GCResult {
    log.tracev("Perform sweep.", .{});
    const num_freed: u32 = 0; // TODO: populate when flattening recursive releases
    var num_cyc_freed: u32 = 0;

    // Sweep heap pages.
    for (vm.heapPages.items()) |page| {
        var i: u32 = 1;
        while (i < page.objects.len) {
            const obj = &page.objects[i];
            if (obj.freeSpan.typeId != cy.NullId) {
                if (obj.isNoMarkCyc()) {
                    // Conservative skip if any shard exists (could be a reservation).
                    const shards = @atomicLoad(u32, &obj.head.rc, .Acquire);
                    if (shards != 0) {
                        // keep for next GC; do not reset any mark (it was unmarked)
                    } else {
                        log.tracev("gc free: {s}, rc={}", .{ vm.getTypeName(obj.getTypeId()), shards });
                        if (cy.Trace) checkDoubleFree(vm, obj);
                        if (cy.TrackGlobalRC) {
                            // head.rc should be 0 here.
                            // If you adjust refCounts in freeObject for children,
                            // ensure there's no double adjust elsewhere.
                            vm.c.refCounts -= 0;
                        }
                        cy.heap.freeObject(vm, obj, true);
                        num_cyc_freed += 1;
                    }
                } else if (obj.isGcMarked()) {
                    obj.resetGcMarked();
                }
                i += 1;
            } else {
                // Freespan, skip to end.
                i += obj.freeSpan.len;
            }
        }
    }

    // Sweep non-pool cyc nodes.
    var mbNode: ?*cy.heap.DListNode = vm.cyclableHead;
    while (mbNode) |node| {
        mbNode = node.next;
        const obj = node.getHeapObject();
        if (obj.isNoMarkCyc()) {
            const shards = @atomicLoad(u32, &obj.head.rc, .Acquire);
            if (shards != 0) {
                // keep for next GC
            } else {
                log.tracev("gc free: {s}, rc={}", .{ vm.getTypeName(obj.getTypeId()), shards });
                if (cy.Trace) checkDoubleFree(vm, obj);
                if (cy.TrackGlobalRC) vm.c.refCounts -= 0;
                cy.heap.freeObject(vm, obj, true);
                num_cyc_freed += 1;
            }
        } else if (obj.isGcMarked()) {
            obj.resetGcMarked();
        }
    }

    if (cy.Trace) vm.c.trace.numCycFrees += num_cyc_freed;

    const res = c.GCResult{
        .numCycFreed = num_cyc_freed,
        .numObjFreed = num_freed,
    };
    log.tracev("gc result: num cyc {}, num obj {}", .{ res.numCycFreed, res.numObjFreed });
    return res;
}

fn markMainStackRoots(vm: *cy.VM) !void {
    if (vm.c.pc[0].opcode() == .end) return;

    var pcOff = cy.fiber.getInstOffset(vm.c.ops, vm.c.pc);
    var fpOff = cy.fiber.getStackOffset(vm.c.stack, vm.c.framePtr);

    while (true) {
        const symIdx = try cy.debug.indexOfDebugSym(vm, pcOff);
        const key = cy.debug.getUnwindKey(vm, symIdx);
        log.tracev("mark frame: pc={} {s} fp={} unwind={},{}", .{
            pcOff, @tagName(vm.c.ops[pcOff].opcode()), fpOff, key.is_null, key.idx,
        });

        if (!key.is_null) {
            const fp = vm.c.stack + fpOff;
            log.tracev("mark temps", .{});
            var cur = key;
            while (!cur.is_null) {
                if (cur.is_try) {
                    const try_e = vm.unwind_trys[cur.idx];
                    cur = try_e.prev;
                } else {
                    log.tracev("mark slot: {}", .{vm.unwind_slots[cur.idx]});
                    const v = fp[vm.unwind_slots[cur.idx]];
                    if (v.isCycPointer()) markValue(vm, v);
                    cur = vm.unwind_slot_prevs[cur.idx];
                }
            }
        }

        if (fpOff == 0) {
            return; // at main block
        } else {
            // Unwind.
            pcOff = cy.fiber.getInstOffset(vm.c.ops, vm.c.stack[fpOff + 2].retPcPtr) - vm.c.stack[fpOff + 1].call_info.call_inst_off;
            fpOff = cy.fiber.getStackOffset(vm.c.stack, vm.c.stack[fpOff + 3].retFramePtr);
        }
    }
}

/// Assumes `v` is a cyclable pointer.
fn markValue(vm: *cy.VM, v: cy.Value) void {
    const obj = v.asHeapObject();
    if (!obj.isGcMarked()) {
        obj.setGcMarked();
    } else {
        return; // Already marked.
    }

    // Visit children.
    const typeId = obj.getTypeId();
    switch (typeId) {
        bt.Map => {
            const map = obj.map.map();
            var iter = map.iterator();
            while (iter.next()) |entry| {
                if (entry.key.isCycPointer()) markValue(vm, entry.key);
                if (entry.value.isCycPointer()) markValue(vm, entry.value);
            }
        },
        bt.MapIter => markValue(vm, obj.mapIter.map),
        bt.UpValue => if (obj.up.val.isCycPointer()) markValue(vm, obj.up.val),
        bt.Fiber => {
            // TODO: Visit other fiber stacks.
        },
        else => {
            const entry = vm.c.types[typeId];
            if (entry.kind == .object) {
                const members = obj.object.getValuesConstPtr()[0..entry.data.object.numFields];
                for (members) |m| if (m.isCycPointer()) markValue(vm, m);
            } else if (entry.kind == .trait) {
                markValue(vm, obj.trait.impl);
            } else if (entry.kind == .func_union) {
                const vals = obj.func_union.getCapturedValuesPtr()[0..obj.func_union.data.closure.numCaptured];
                for (vals) |val| if (val.isCycPointer()) markValue(vm, val);
            } else {
                if (entry.sym.cast(.hostobj_t).getChildrenFn) |getChildren| {
                    const children = getChildren(@ptrCast(vm), @ptrFromInt(@intFromPtr(obj) + 8));
                    for (cy.Value.fromSliceC(children)) |child| {
                        if (child.isCycPointer()) markValue(vm, child);
                    }
                }
            }
        },
    }
}

pub fn countObjects(vm: *cy.VM) usize {
    var count: usize = 0;
    for (vm.heapPages.items()) |page| {
        var i: u32 = 1;
        while (i < page.objects.len) {
            const obj = &page.objects[i];
            if (obj.freeSpan.typeId != cy.NullId) {
                count += 1;
                i += 1;
            } else {
                i += obj.freeSpan.len; // Freespan, skip to end.
            }
        }
    }

    // Traverse non-pool cyc nodes.
    var mbNode: ?*cy.heap.DListNode = vm.cyclableHead;
    while (mbNode) |node| {
        count += 1;
        mbNode = node.next;
    }

    // Account for the dummy cyclable node.
    count -= 1;

    return count;
}

pub fn checkGlobalRC(ivm: *cy.VM) !void {
    const vm: *c.ZVM = @ptrCast(ivm);
    const rc = getGlobalRC(ivm);
    if (rc != 0) {
        std.debug.print("unreleased refcount: {}\n", .{rc});
        vm.traceDumpLiveObjects();
        return error.UnreleasedReferences;
    }
}

pub fn dumpObjectAllocTrace(vm: *cy.VM, obj: *cy.HeapObject, allocPc: u32) !void {
    var buf: [256]u8 = undefined;
    const typeId = obj.getTypeId();
    const typeName = vm.getTypeName(typeId);
    const valStr = try vm.bufPrintValueShortStr(&vm.tempBuf, cy.Value.initNoCycPtr(obj));
    const msg = try std.fmt.bufPrint(&buf, "{*}, type: {s}, rc: {} at pc: {}\nval={s}", .{
        obj, typeName, obj.head.rc, allocPc, valStr,
    });
    try cy.debug.printTraceAtPc(vm, allocPc, "alloced", msg);
}
