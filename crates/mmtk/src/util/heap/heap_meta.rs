use crate::util::heap::layout::vm_layout::vm_layout;
use crate::util::heap::layout::Mmapper;
use crate::util::os::{HugePageSupport, MmapAnnotation, MmapResult};
use crate::util::Address;

pub struct HeapMeta {
    pub heap_cursor: Address,
    pub heap_limit: Address,
}

impl HeapMeta {
    pub fn new() -> Self {
        HeapMeta {
            heap_cursor: vm_layout().heap_start,
            heap_limit: vm_layout().heap_end,
        }
    }

    pub fn reserve_quarantined(
        &mut self,
        extent: usize,
        align: Option<usize>,
        top: bool,
        mmapper: &dyn Mmapper,
        huge_page_option: HugePageSupport,
        anno: &MmapAnnotation,
    ) -> MmapResult<Address> {
        let start = if top {
            let raw_start = self.heap_limit - extent;
            if let Some(align) = align {
                raw_start.align_down(align)
            } else {
                raw_start
            }
        } else {
            let raw_start = self.heap_cursor;
            if let Some(align) = align {
                raw_start.align_up(align)
            } else {
                raw_start
            }
        };

        let start = Self::quarantine_first_free(
            start,
            extent,
            align,
            top,
            self.heap_cursor,
            self.heap_limit,
            mmapper,
            huge_page_option,
            anno,
        )?;

        if top {
            self.heap_limit = start;
        } else {
            self.heap_cursor = start + extent;
        }

        assert!(
            self.heap_cursor <= self.heap_limit,
            "Out of virtual address space after quarantining [{}, {})",
            start,
            start + extent,
        );

        Ok(start)
    }

    /// Quarantines `extent` bytes at `start`. The fixed mmap fails when another mapping
    /// already occupies part of the range: on Windows, high-entropy ASLR can place the
    /// process's bottom-up allocations (thread stacks, heaps, mapped NLS files) inside the
    /// first space slot. Aligned (slot-sized) requests then move to the next free slot in
    /// the allocation direction, staying within `[cursor, limit]`; space indices are derived
    /// from addresses, so any free slot works. Each attempt targets a range that MMTk has
    /// not mapped yet, which the OS reserves atomically, so failed attempts leave no state.
    #[allow(clippy::too_many_arguments)]
    fn quarantine_first_free(
        start: Address,
        extent: usize,
        align: Option<usize>,
        top: bool,
        cursor: Address,
        limit: Address,
        mmapper: &dyn Mmapper,
        huge_page_option: HugePageSupport,
        anno: &MmapAnnotation,
    ) -> MmapResult<Address> {
        let pages = crate::util::conversions::bytes_to_pages_up(extent);
        let first_error = match mmapper.quarantine_address_range(start, pages, huge_page_option, anno)
        {
            Ok(()) => return Ok(start),
            Err(error) => error,
        };
        let Some(step) = align.filter(|&a| a >= extent) else {
            return Err(first_error);
        };
        let mut candidate = start;
        loop {
            candidate = if top {
                if candidate.as_usize() < cursor.as_usize() + step {
                    break;
                }
                candidate - step
            } else {
                if candidate.as_usize() + step + extent > limit.as_usize() {
                    break;
                }
                candidate + step
            };
            if mmapper
                .quarantine_address_range(candidate, pages, huge_page_option, anno)
                .is_ok()
            {
                warn!(
                    "Address range at {} is in use ({}); quarantined {} instead",
                    start, first_error, candidate
                );
                return Ok(candidate);
            }
        }
        Err(first_error)
    }

    pub fn get_discontig_start(&self) -> Address {
        self.heap_cursor
    }

    pub fn get_discontig_end(&self) -> Address {
        self.heap_limit - 1
    }
}

// make clippy happy
impl Default for HeapMeta {
    fn default() -> Self {
        Self::new()
    }
}
