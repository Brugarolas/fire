use crate::helpers::collections::{HashMap};
use std::fmt::{Debug, Display};
use std::hash::Hash;

/////////////////////////////////////////////////////////////////////////////////////
/// Layered Hash Map
/////////////////////////////////////////////////////////////////////////////////////
/// A helper function to get the "address" of an item as a `u64`.
/// WARNING: In real code, this can be problematic if items move in memory. This is very C-like code, not idiomatic Rust.
/// It's used here for internal implementation of a fast random generator, that uses the memory address of some items as a seed.
/// The objective here is to have a good fast random generator that doesn't involve any expensive computation or a system call.
#[inline]
fn addr_u64<T>(x: &T) -> u64 {
    x as *const T as u64
}

type Matrix<T> = Vec<Vec<T>>;

// We'll store a small stack of `Vec<usize>` for re-use
thread_local! {
    static VEC_POOL_12: std::sync::Mutex<Matrix<usize>> = std::sync::Mutex::new({
        let mut init = Vec::with_capacity(50);
        for _ in 0..50 {
            init.push(Vec::with_capacity(12));
        }
        init
    });
}

/// Return a Vec<usize> that has capacity exactly 12 if available,
/// otherwise create a new one with capacity 12.
fn pool_get_vec_12() -> Vec<usize> {
    VEC_POOL_12.with(|pool| {
        let mut guard = pool.lock().unwrap();          // ← was borrow_mut()
        if let Some(mut v) = guard.pop() {
            v.clear();                                 // ensure length == 0
            v
        } else {
            Vec::with_capacity(12)
        }
    })
}

/// Return a Vec<usize> to the pool if its capacity == 12.
fn pool_put_vec_12(mut v: Vec<usize>) {
    if v.capacity() == 12 {
        v.clear();
        VEC_POOL_12.with(|pool| {
            pool.lock().unwrap().push(v);              // ← was borrow_mut()
        });
    }
    // else: drop and let the allocator reclaim it
}

/// Minimal struct storing one key and a stack of `(layer_id, value)` versions.
#[derive(Debug, Clone)]
struct MapSlot<K, V> {
    key: K,
    // top of this Vec is the "current" version for that key
    versions: Vec<(u64, V)>,
}

/// Each layer in the stack has:
///   - layer_id (semi-random, computed on `enter_scope`)
///   - changed_indices: which slots in `slots` got new versions
#[derive(Debug, Clone, PartialEq)]
struct LayerInfo {
    layer_id: u64,
    changed_indices: Vec<usize>,
}

/// The main data structure:
///  - `map_id`: random once at creation
///  - `layer_stack`: stack of `(layer_id, changed_indices)`
///  - `slots`: a growable array of `MapSlot`
///  - `key_index`: a HashMap from K to an index in `slots`
///  - `last_key_ptr`, `last_value_ptr`: updated on each insertion
///  - `layer_counter`: incremented each time we add a new layer
#[derive(Debug, Clone)]
pub struct LayeredMap<K, V>
where
    K: Hash + Clone + Eq,
    V: Default + Clone,
{
    map_id: u64,
    layer_stack: Vec<LayerInfo>,
    slots: Vec<MapSlot<K, V>>,
    key_index: HashMap<K, usize>,

    last_key_ptr: u64,
    last_value_ptr: u64,
    layer_counter: u64,

    return_register: Vec<Option<V>>,
}

impl<K, V> LayeredMap<K, V>
where
    K: Hash + Clone + Eq,
    V: Default + Clone,
{
    /// Create a new LayeredMap with some initial capacity.
    /// We do a single "random-ish" step for `map_id`.
    pub fn new() -> Self {
        let address_seed = addr_u64(&0u8); // or something
        let map_id = 0xcafe_f00d_fafa_feed_u64
            .wrapping_mul(address_seed)
            .rotate_left(17)
            ^ 0xdead_beef;

        let mut new_object = Self {
            map_id,
            layer_stack: Vec::with_capacity(24), // you asked for default 8 or 32, adapt as you like
            slots: Vec::with_capacity(12),
            key_index: HashMap::with_capacity(256 * 256),

            last_key_ptr: 1,   // some nonzero default
            last_value_ptr: 1, // some nonzero default
            layer_counter: 1,

            return_register: Vec::with_capacity(16),
        };

        new_object.enter_layer(); // enter the first layer automatically

        return new_object;
    }

    /// Enter a new layer (scope). We compute a "semi-random" layer_id:
    ///   layer_id = map_id * layer_counter * last_key_ptr * last_value_ptr
    /// Return the layer_id for reference if needed.
    pub fn enter_layer(&mut self) -> u64 {
        let layer_id = self
            .map_id
            .wrapping_mul(self.layer_counter)
            .wrapping_mul(self.last_key_ptr)
            .wrapping_mul(self.last_value_ptr);

        self.layer_counter = self.layer_counter.wrapping_add(1);

        self.return_register.push(None);

        // Decide capacity:
        let depth = self.layer_stack.len();
        let changed = if depth == 0 || depth == 1 {
            // first layer
            Vec::with_capacity(256)
        } else if depth == 2 {
            // second layer
            Vec::with_capacity(48)
        } else {
            // for deeper layers
            // we can get a pre-pooled Vec of capacity 12
            pool_get_vec_12()
        };

        self.layer_stack.push(LayerInfo {
            layer_id,
            changed_indices: changed,
        });
        layer_id
    }

    /// Exit the current layer (like popping a scope).
    /// We pop the last layer and revert changes in each changed slot.
    ///
    /// Returns a Vec containing the (key, value) pairs of all items that were
    /// defined in the layer that was just exited.
    pub fn exit_layer(&mut self) -> Vec<(K, V)> {
        let layer_info = self.layer_stack.pop().expect("No layer to exit");
        let layer_id = layer_info.layer_id;

        self.return_register.pop().expect("No return register to exit");

        // This will hold the items that were unique to the popped layer.
        let mut exited_scope_items = Vec::new();

        // Revert changes
        for &slot_idx in layer_info.changed_indices.iter().rev() {
            let slot = &mut self.slots[slot_idx];
            if let Some(&(top_layer_id, _)) = slot.versions.last() {
                if top_layer_id == layer_id {
                    // This item was defined in the scope we are exiting.
                    // Pop it and add it to our results.
                    if let Some((_, val)) = slot.versions.pop() {
                        exited_scope_items.push((slot.key.clone(), val));
                    }

                    // If the slot is now empty, the key is no longer accessible.
                    if slot.versions.is_empty() {
                        self.key_index.remove(&slot.key);
                    }
                } else {
                    // This should not happen with correct usage.
                    panic!("Internal error: layer mismatch during exit_layer");
                }
            } else {
                panic!("Internal error: no versions in slot but marked as changed?");
            }
        }

        // Return the Vec to the pool if its capacity allows.
        if layer_info.changed_indices.capacity() == 12 {
            pool_put_vec_12(layer_info.changed_indices);
        }

        exited_scope_items
    }

    /// Insert a value for a given key in the current top layer.
    /// - If the top version for that key is already from this layer,
    ///   we just overwrite the value.
    /// - Otherwise we push a new version `(layer_id, value)`.
    /// - If it’s brand-new to the map, we also store in `key_index`
    ///   and mark the current slot as changed in the layer.
    pub fn insert(&mut self, key: K, value: V) {
        let current_layer = self
            .layer_stack
            .last_mut()
            .expect("enter_layer must have been called");
        let layer_id = current_layer.layer_id;

        // Shared cell we'll store
        let cell = value;

        // Existing slot?
        if let Some(&slot_idx) = self.key_index.get(&key) {
            let slot = &mut self.slots[slot_idx];
            if let Some(&mut (top_id, ref mut top_val)) = slot.versions.last_mut() {
                if top_id == layer_id {
                    *top_val = cell;
                    return;
                }
            }
            slot.versions.push((layer_id, cell));
            current_layer.changed_indices.push(slot_idx);
        } else {
            let slot_idx = self.slots.len();
            self.slots.push(MapSlot {
                key: key.clone(),
                versions: vec![(layer_id, cell)],
            });
            self.key_index.insert(key, slot_idx);
            current_layer.changed_indices.push(slot_idx);
        }
    }

    /// Get the current value for a given key.
    /// We find the slot, then return the top version’s value.
    pub fn get(&self, key: &K) -> Option<V> {
        let slot_idx = self.key_index.get(key)?;
        let slot     = &self.slots[*slot_idx];
        let (_, cell) = slot.versions.last()?;
        Some(cell.clone())
    }

    /// Current number of layers (the size of the layer stack).
    pub fn layer_depth(&self) -> usize {
        self.layer_stack.len()
    }

    /// Set the special scoped return register
    pub fn set_return(&mut self, value: V) {
        if let Some(last) = self.return_register.last_mut() {
            *last = Some(value);
        }
    }

    /// Get the special scoped return register value
    pub fn take_return(&mut self) -> Option<V> {
        self.return_register
            .last_mut()
            .and_then(|slot| slot.take())
    }

    /// Get the layer id of the last layer
    pub fn get_last_layer_id(&self) -> u64 {
        let layer_id = self.layer_stack.last().map(|layer| layer.layer_id);

        if layer_id.is_some() {
            return layer_id.unwrap();
        }

        panic!("No layer to get last layer id");
    }

    /// Obtain the shared cell for `key`, creating an `Arc<Mutex<V::default()>>`
    /// if the variable does not yet exist in the current scope.
    pub fn capture_cell(&mut self, key: &K) -> V {
        if let Some(existing) = self.get(key) {
            return existing;               // clone of Rc
        }

        // create a brand-new cell and store it in the current layer
        let cell = V::default();
        self.insert_cell(key.clone(), cell.clone());
        cell
    }

    /// Directly insert an **existing** `Arc<Mutex<V>>` into the map
    /// (used when a closure wants to share an outer cell).
    pub fn insert_cell(&mut self, key: K, cell: V) {
        let current_layer = self.layer_stack.last_mut()
            .expect("enter_layer must be called first");
        let layer_id = current_layer.layer_id;

        if let Some(&slot_idx) = self.key_index.get(&key) {
            let slot = &mut self.slots[slot_idx];
            if let Some(&mut (top_id, ref mut top_cell)) = slot.versions.last_mut() {
                if top_id == layer_id {
                    *top_cell = cell;
                    return;
                }
            }
            slot.versions.push((layer_id, cell));
            current_layer.changed_indices.push(slot_idx);
        } else {
            let slot_idx = self.slots.len();
            self.slots.push(MapSlot {
                key: key.clone(),
                versions: vec![(layer_id, cell)],
            });
            self.key_index.insert(key, slot_idx);
            current_layer.changed_indices.push(slot_idx);
        }
    }

    /// Return the *currently-visible* Rc cell for `key`, if any.
    pub fn find_cell(&self, key: &K) -> Option<V> {
        // `get()` probably returns Option<&Arc<…>>
        self.get(key).map(|cell| cell.clone())
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Some(&slot_idx) = self.key_index.get(key) {
            let slot = &mut self.slots[slot_idx];
            if let Some(&mut (_, ref mut cell)) = slot.versions.last_mut() {
                return Some(cell);
            }
        }
        None
    }

    pub fn iter_keys(&self) -> Vec<K> where K: Clone {
        self.key_index.keys().cloned().collect()
    }

    /// Iterate over the *currently‑visible* `Arc<Mutex<V>>` cells.
    ///
    /// Each key keeps a stack of versions; the last entry is the one that is
    /// visible in the current lexical layer.
    #[inline]
    pub fn values_cells(&self) -> impl Iterator<Item = &V> {
        self.slots
            .iter()
            .filter_map(|slot| slot.versions.last().map(|(_, cell)| cell))
    }

    /// Checks if a key has a value defined specifically in the current (top-most) layer.
    ///
    /// This is used to detect variable shadowing or redeclaration within the same scope.
    /// It returns `true` only if the most recent version of the key belongs to the
    /// current layer's ID.
    pub fn is_in_current_layer(&self, key: &K) -> bool {
        // First, get the ID of the current layer. If there's no layer, nothing can be in it.
        if let Some(current_layer) = self.layer_stack.last() {
            // Next, find the slot for the key. If the key doesn't exist at all, it's not in this layer.
            if let Some(&slot_idx) = self.key_index.get(key) {
                let slot = &self.slots[slot_idx];

                // Finally, check the top-most version in that slot.
                if let Some((top_layer_id, _)) = slot.versions.last() {
                    // The key is in the current layer if and only if the top version's
                    // layer ID matches the current layer's ID.
                    return *top_layer_id == current_layer.layer_id;
                }
            }
        }

        // If any of the above checks fail, the key is not defined in the current layer.
        false
    }
}
