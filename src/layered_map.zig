const std = @import("std");

pub fn LayeredMap(comptime K: type, comptime V: type) type {
    const Alloc = std.mem.Allocator;

    const Cell = struct {
        mutex: std.Thread.Mutex = .{},
        ref_count: std.atomic.Value(usize) = std.atomic.Value(usize).init(1),
        value: V,

        pub fn create(alloc: Alloc, init: V) !*Cell {
            var p = try alloc.create(Cell);
            p.* = .{ .value = init };
            return p;
        }

        pub fn retain(self: *Cell) void {
            _ = self.ref_count.fetchAdd(1, .Monotonic);
        }

        pub fn release(self: *Cell, alloc: Alloc) void {
            const old = self.ref_count.fetchSub(1, .AcqRel);
            if (old == 1) {
                // no destructor for V assumed; if needed, drop here
                alloc.destroy(self);
            }
        }
    };

    const Version = struct {
        layer_id: u64,
        cell: *Cell,
    };

    const MapSlot = struct {
        key: K,
        versions: std.ArrayListUnmanaged(Version),

        fn deinit(self: *MapSlot, alloc: Alloc) void {
            // release all cells held by this slot
            for (self.versions.items) |v| v.cell.release(alloc);
            self.versions.deinit(alloc);
        }
    };

    const LayerInfo = struct {
        layer_id: u64,
        changed_indices: std.ArrayListUnmanaged(usize),
    };

    return struct {
        // --- core storage ---
        alloc: Alloc,
        map_id: u64,
        layer_stack: std.ArrayListUnmanaged(LayerInfo),
        slots: std.ArrayListUnmanaged(MapSlot),
        key_index: std.AutoHashMap(K, usize),

        last_key_ptr: u64 = 1,
        last_value_ptr: u64 = 1,
        layer_counter: u64 = 1,

        return_register: std.ArrayListUnmanaged(?*Cell),

        // pool of ArrayListUnmanaged(usize) with capacity 12
        small_vec_pool: std.ArrayListUnmanaged(std.ArrayListUnmanaged(usize)),

        const Self = @This();

        // ---------------- utilities ----------------
        inline fn addrU64(ptr: anytype) u64 {
            return @intCast(u64, @intFromPtr(ptr));
        }

        inline fn rotl64(x: u64, comptime n: u6) u64 {
            return std.math.rotl(u64, x, n);
        }

        fn poolGetVec12(self: *Self) !std.ArrayListUnmanaged(usize) {
            if (self.small_vec_pool.items.len != 0) {
                return self.small_vec_pool.pop();
            }
            var v = std.ArrayListUnmanaged(usize){};
            try v.ensureTotalCapacity(self.alloc, 12);
            return v;
        }

        fn poolPutVec12(self: *Self, v_in: std.ArrayListUnmanaged(usize)) void {
            // only pool if exact capacity 12
            if (v_in.capacity == 12) {
                var v = v_in;
                v.shrinkRetainingCapacity(0);
                _ = self.small_vec_pool.append(self.alloc, v) catch {};
            } else {
                // drop
                var v = v_in;
                v.deinit(self.alloc);
            }
        }

        // ---------------- lifecycle ----------------
        pub fn init(alloc: Alloc) !Self {
            // random-ish id from an address
            var dummy: u8 = 0;
            const address_seed: u64 = @intCast(u64, @intFromPtr(&dummy));
            const map_id: u64 =
                (0x_cafe_f00d_1234_5678_u64 * address_seed ^ 0x_dead_beef)
                |> (fn (x: u64) u64 { return std.math.rotl(u64, x, 17); }( . ));

            var self = Self{
                .alloc = alloc,
                .map_id = map_id,
                .layer_stack = .{},
                .slots = .{},
                .key_index = std.AutoHashMap(K, usize).init(alloc),
                .return_register = .{},
                .small_vec_pool = .{},
            };

            try self.layer_stack.ensureTotalCapacity(alloc, 24);
            try self.slots.ensureTotalCapacity(alloc, 12);
            try self.return_register.ensureTotalCapacity(alloc, 16);

            // Pre-warm pool with 50 vectors of capacity 12
            try self.small_vec_pool.ensureTotalCapacity(alloc, 50);
            var i: usize = 0;
            while (i < 50) : (i += 1) {
                var v = std.ArrayListUnmanaged(usize){};
                try v.ensureTotalCapacity(alloc, 12);
                try self.small_vec_pool.append(alloc, v);
            }

            _ = try self.enterLayer(); // first layer automatically
            return self;
        }

        pub fn deinit(self: *Self) void {
            // release return register cells we still hold
            for (self.return_register.items) |maybe_cell| {
                if (maybe_cell) |cell| cell.release(self.alloc);
            }
            self.return_register.deinit(self.alloc);

            // release slots and their versions
            for (self.slots.items) |*slot| slot.deinit(self.alloc);
            self.slots.deinit(self.alloc);

            // layer stack changed_indices lists (don’t forget pooled vs non-pooled)
            for (self.layer_stack.items) |*layer| {
                if (layer.changed_indices.capacity == 12) {
                    // return to pool
                    self.poolPutVec12(layer.changed_indices);
                } else {
                    layer.changed_indices.deinit(self.alloc);
                }
            }
            self.layer_stack.deinit(self.alloc);

            // drain pool storage
            for (self.small_vec_pool.items) |*v| v.deinit(self.alloc);
            self.small_vec_pool.deinit(self.alloc);

            self.key_index.deinit();
        }

        // ---------------- layering ----------------
        pub fn enterLayer(self: *Self) !u64 {
            const layer_id = self.map_id
                * self.layer_counter
                * self.last_key_ptr
                * self.last_value_ptr;

            self.layer_counter +%= 1;

            // push return register slot
            try self.return_register.append(self.alloc, null);

            // capacity heuristic: 256, 48, else pooled 12
            const depth = self.layer_stack.items.len;
            var changed: std.ArrayListUnmanaged(usize) = switch (depth) {
                0, 1 => blk: {
                    var v = std.ArrayListUnmanaged(usize){};
                    try v.ensureTotalCapacity(self.alloc, 256);
                    break :blk v;
                },
                2 => blk: {
                    var v = std.ArrayListUnmanaged(usize){};
                    try v.ensureTotalCapacity(self.alloc, 48);
                    break :blk v;
                },
                else => try self.poolGetVec12(),
            };

            try self.layer_stack.append(self.alloc, .{
                .layer_id = layer_id,
                .changed_indices = changed,
            });
            return layer_id;
        }

        pub fn exitLayer(self: *Self) void {
            const layer_info = self.layer_stack.popOrNull() orelse @panic("No layer to exit");
            const layer_id = layer_info.layer_id;

            _ = self.return_register.popOrNull() orelse @panic("No return register to exit");

            // revert in reverse order
            var li = layer_info.changed_indices;
            var idx: isize = @intCast(isize, li.items.len);
            while (idx > 0) {
                idx -= 1;
                const slot_idx = li.items[@intCast(usize, idx)];
                var slot = &self.slots.items[slot_idx];
                const top = slot.versions.popOrNull() orelse @panic("Internal error: no versions but changed?");
                if (top.layer_id != layer_id) @panic("Internal error: mismatch layer");
                // release the popped cell
                top.cell.release(self.alloc);

                if (slot.versions.items.len == 0) {
                    // remove from key_index
                    _ = self.key_index.remove(slot.key);
                }
            }

            // return or free the changed_indices vector
            if (li.capacity == 12) {
                self.poolPutVec12(li);
            } else {
                li.deinit(self.alloc);
            }
        }

        pub fn layerDepth(self: *const Self) usize {
            return self.layer_stack.items.len;
        }

        pub fn getLastLayerId(self: *const Self) u64 {
            if (self.layer_stack.items.len == 0) @panic("No layer to get last layer id");
            return self.layer_stack.items[self.layer_stack.items.len - 1].layer_id;
        }

        // ---------------- insert / capture ----------------
        pub fn insert(self: *Self, key: K, value: V) !void {
            const layer = self.layer_stack.items[self.layer_stack.items.len - 1];
            const layer_id = layer.layer_id;

            var cell = try Cell.create(self.alloc, value);

            // update entropy ptrs
            self.last_key_ptr = self.addrU64(&key);
            self.last_value_ptr = self.addrU64(cell);

            if (self.key_index.get(key)) |slot_idx| {
                var slot = &self.slots.items[slot_idx];
                if (slot.versions.items.len != 0 and slot.versions.items[slot.versions.items.len - 1].layer_id == layer_id) {
                    // overwrite current layer's top
                    var top = &slot.versions.items[slot.versions.items.len - 1];
                    top.cell.release(self.alloc);
                    top.cell = cell;
                    return;
                }
                // push new version
                try slot.versions.append(self.alloc, .{ .layer_id = layer_id, .cell = cell });
                try self.layer_stack.items[self.layer_stack.items.len - 1].changed_indices.append(self.alloc, slot_idx);
            } else {
                const slot_idx_new = self.slots.items.len;
                // slot.versions starts with one entry
                var versions = std.ArrayListUnmanaged(Version){};
                try versions.ensureTotalCapacity(self.alloc, 1);
                versions.appendAssumeCapacity(.{ .layer_id = layer_id, .cell = cell });

                try self.slots.append(self.alloc, .{ .key = key, .versions = versions });
                try self.key_index.put(self.slots.items[slot_idx_new].key, slot_idx_new);
                try self.layer_stack.items[self.layer_stack.items.len - 1].changed_indices.append(self.alloc, slot_idx_new);
            }
        }

        pub fn insertCell(self: *Self, key: K, cell_in: *Cell) !void {
            const layer = self.layer_stack.items[self.layer_stack.items.len - 1];
            const layer_id = layer.layer_id;

            cell_in.retain(); // store our own ref
            self.last_key_ptr = self.addrU64(&key);
            self.last_value_ptr = self.addrU64(cell_in);

            if (self.key_index.get(key)) |slot_idx| {
                var slot = &self.slots.items[slot_idx];
                if (slot.versions.items.len != 0 and slot.versions.items[slot.versions.items.len - 1].layer_id == layer_id) {
                    var top = &slot.versions.items[slot.versions.items.len - 1];
                    top.cell.release(self.alloc);
                    top.cell = cell_in;
                    return;
                }
                try slot.versions.append(self.alloc, .{ .layer_id = layer_id, .cell = cell_in });
                try self.layer_stack.items[self.layer_stack.items.len - 1].changed_indices.append(self.alloc, slot_idx);
            } else {
                const slot_idx_new = self.slots.items.len;
                var versions = std.ArrayListUnmanaged(Version){};
                try versions.ensureTotalCapacity(self.alloc, 1);
                versions.appendAssumeCapacity(.{ .layer_id = layer_id, .cell = cell_in });

                try self.slots.append(self.alloc, .{ .key = key, .versions = versions });
                try self.key_index.put(self.slots.items[slot_idx_new].key, slot_idx_new);
                try self.layer_stack.items[self.layer_stack.items.len - 1].changed_indices.append(self.alloc, slot_idx_new);
            }
        }

        pub fn captureCell(self: *Self, key: K) !*Cell {
            if (self.get(key)) |cell| {
                cell.retain();
                return cell;
            }
            // create default, store in current layer, and return retained
            var default_val: V = std.mem.zeroes(V);
            if (@hasDecl(V, "init")) {
                // If V provides a custom init, prefer it (optional pattern)
                default_val = @field(V, "init")();
            }
            var cell = try Cell.create(self.alloc, default_val);
            // insertCell retains; but we already own one ref; to keep one for caller,
            // insert with an extra retain and then release once after
            cell.retain();
            try self.insertCell(key, cell);
            // Our initial create() ref + insertCell's retain => 2; drop one so caller owns 1
            cell.release(self.alloc);
            return cell;
        }

        // ---------------- queries ----------------
        /// Borrowing get: no retain. Do not outlive map unless you retain.
        pub fn get(self: *const Self, key: K) ?*Cell {
            const slot_idx = self.key_index.get(key) orelse return null;
            const slot = &self.slots.items[slot_idx];
            if (slot.versions.items.len == 0) return null;
            return slot.versions.items[slot.versions.items.len - 1].cell;
        }

        /// Retained get: caller must release.
        pub fn getRetained(self: *const Self, key: K) ?*Cell {
            const c = self.get(key) orelse return null;
            c.retain();
            return c;
        }

        pub fn valuesCells(self: *const Self) ValuesIter {
            return ValuesIter{ .map = self, .i = 0 };
        }

        pub fn iterKeys(self: *const Self, alloc: Alloc) ![]K {
            // Collect keys for which a visible version exists (versions.len > 0).
            var out = try std.ArrayList(K).initCapacity(alloc, self.key_index.count());
            defer out.deinit();
            // Iterate slots; only include keys with non-empty stacks.
            for (self.slots.items) |slot| {
                if (slot.versions.items.len != 0) {
                    try out.append(slot.key);
                }
            }
            return out.toOwnedSlice();
        }

        // ---------------- return register ----------------
        pub fn setReturn(self: *Self, value: V) !void {
            if (self.return_register.items.len == 0) return; // no layer
            var cell = try Cell.create(self.alloc, value);
            var last = &self.return_register.items[self.return_register.items.len - 1];
            if (last.*) |old| old.release(self.alloc);
            last.* = cell;
        }

        /// Take ownership of the current layer's return cell (map forgets it).
        pub fn takeReturn(self: *Self) ?*Cell {
            if (self.return_register.items.len == 0) return null;
            var last = &self.return_register.items[self.return_register.items.len - 1];
            const res = last.*;
            last.* = null;
            return res;
        }

        // ---------------- iterator over visible cells ----------------
        pub const ValuesIter = struct {
            map: *const Self,
            i: usize,

            pub fn next(self: *ValuesIter) ?*Cell {
                while (self.i < self.map.slots.items.len) : (self.i += 1) {
                    const slot = &self.map.slots.items[self.i];
                    if (slot.versions.items.len != 0) {
                        const c = slot.versions.items[slot.versions.items.len - 1].cell;
                        self.i += 1;
                        return c;
                    }
                }
                return null;
            }
        };
    };
}