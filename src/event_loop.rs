// runtime/event_loop.rs (new)
#![allow(unused_imports)]

use std::{
    cmp::Reverse,
    collections::{BinaryHeap, VecDeque},
    sync::{Mutex, Condvar},
    time::{Duration, Instant},
};
use once_cell::sync::Lazy;
use std::sync::atomic::{AtomicU64, Ordering};
use ahash::AHashSet as HashSet;

#[derive(Clone, Copy)]
pub struct MicroTask {
    pub fun: i64,
    pub arg: i64,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum TimerKind { Timeout, Interval }

#[derive(Clone)]
struct Task {
    id: u64,
    when: Instant,
    kind: TimerKind,
    period: Option<Duration>,
    fun: i64,        // VM closure value (tagged)
    canceled: bool,
}

impl PartialEq for Task { fn eq(&self, o: &Self) -> bool { self.when.eq(&o.when) && self.id == o.id } }
impl Eq for Task {}
impl PartialOrd for Task { fn partial_cmp(&self, o: &Self) -> Option<std::cmp::Ordering> { Some(self.cmp(o)) } }
impl Ord for Task { fn cmp(&self, o: &Self) -> std::cmp::Ordering { self.when.cmp(&o.when).then(self.id.cmp(&o.id)) } }

// inside Inner:
struct Inner {
    heap: BinaryHeap<Reverse<Task>>,
    ready: VecDeque<Task>,
    active: usize,
    canceled: HashSet<u64>,
    micro: VecDeque<MicroTask>,
}

pub struct EventLoop {
    m: Mutex<Inner>,
    cv: Condvar,
    next_id: AtomicU64,
}

pub static EVENT_LOOP: Lazy<EventLoop> = Lazy::new(|| EventLoop {
    m: Mutex::new(Inner { heap: BinaryHeap::new(), ready: VecDeque::new(), active: 0, canceled: HashSet::new(), micro: VecDeque::new() }),
    cv: Condvar::new(),
    next_id: AtomicU64::new(1),
});

impl EventLoop {
    pub fn schedule(&self, fun: i64, delay_ms: i64, kind: TimerKind) -> u64 {
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let d = if delay_ms <= 0 { Duration::from_millis(0) } else { Duration::from_millis(delay_ms as u64) };
        let t = Task {
            id,
            when: Instant::now() + d,
            kind,
            period: if kind == TimerKind::Interval { Some(d.max(Duration::from_millis(1))) } else { None },
            fun,
            canceled: false,
        };
        let mut g = self.m.lock().unwrap();
        g.heap.push(Reverse(t));
        g.active += 1;
        self.cv.notify_all();
        id
    }

    pub fn enqueue_microtask(&self, fun: i64, arg: i64) {
        let mut g = self.m.lock().unwrap();
        g.micro.push_back(MicroTask { fun, arg });
        self.cv.notify_all();
    }

    pub fn run_microtasks(&self, budget: usize, mut call1: impl FnMut(i64, i64)) -> usize {
        let mut ran = 0;
        loop {
            if ran >= budget { break; }
            let mt = {
                let mut g = self.m.lock().unwrap();
                match g.micro.pop_front() {
                    Some(m) => m,
                    None => break,
                }
            };
            call1(mt.fun, mt.arg);
            ran += 1;
        }
        ran
    }

    // fix clear():
    pub fn clear(&self, id: u64) {
        let mut g = self.m.lock().unwrap();

        // mark ready-queue tasks and count how many we actually canceled
        let mut dec = 0usize;
        for r in g.ready.iter_mut() {
            if r.id == id && !r.canceled {
                r.canceled = true;
                dec += 1;
            }
        }
        if dec > 0 {
            g.active = g.active.saturating_sub(dec);
        }

        // make future pops from the heap drop this id before enqueueing
        g.canceled.insert(id);

        self.cv.notify_all();
    }

    // when moving due items out of the heap:
    pub fn poll_due_and_enqueue(&self) {
        let mut g = self.m.lock().unwrap();
        let now = Instant::now();
        while let Some(Reverse(t)) = g.heap.peek().cloned() {
            if t.when > now { break; }
            let _ = g.heap.pop();

            // drop if canceled while sitting in the heap
            if g.canceled.remove(&t.id) {
                g.active = g.active.saturating_sub(1);
                continue;
            }
            g.ready.push_back(t);
        }
    }

    // when running ready tasks:
    pub fn run_ready(&self, budget: usize, mut call_closure: impl FnMut(i64)) -> usize {
        let mut ran = 0;
        loop {
            if ran >= budget { break; }
            let task = {
                let mut g = self.m.lock().unwrap();
                match g.ready.pop_front() {
                    Some(t) => t,
                    None => break,
                }
            };

            // skip if canceled (either flagged while ready, or tombstoned)
            let canceled_now = {
                let mut g = self.m.lock().unwrap();
                task.canceled || g.canceled.remove(&task.id)
            };
            if canceled_now {
                let mut g = self.m.lock().unwrap();
                g.active = g.active.saturating_sub(1);
                continue;
            }

            call_closure(task.fun);
            ran += 1;

            if task.kind == TimerKind::Interval {
                let mut g = self.m.lock().unwrap();
                let p = task.period.unwrap();
                g.heap.push(Reverse(Task { when: Instant::now() + p, ..task }));
            } else {
                let mut g = self.m.lock().unwrap();
                g.active = g.active.saturating_sub(1);
            }
        }
        ran
    }

    /// Drive the loop once:
    /// 1) drain some microtasks,
    /// 2) move due timers to the ready queue,
    /// 3) run at most one ready timer callback,
    /// 4) if nothing ran, wait until the next timer (or briefly if none).
    ///
    /// Returns `true` if any work (microtask or timer) was executed.
    pub fn pump_once(
        &self,
        mut call_micro: impl FnMut(i64, i64),  // (fun, arg)
        mut call_timer: impl FnMut(i64),       // (fun)
    ) -> bool {
        // 1) Drain some microtasks first
        let ran_micro = self.run_microtasks(1024, |f, a| call_micro(f, a));
        if ran_micro > 0 { return true; }

        // 2) Promote due timers
        self.poll_due_and_enqueue();

        // 3) Run at most one ready timer
        let ran_timers = self.run_ready(1, &mut call_timer);
        if ran_timers > 0 { return true; }

        // 4) Nothing ran; wait until next timer or a short timeout
        let mut g = self.m.lock().unwrap();

        // If something arrived concurrently, loop again immediately (no wait)
        if !g.micro.is_empty() || !g.ready.is_empty() {
            return false;
        }

        if let Some(std::cmp::Reverse(next)) = g.heap.peek().cloned() {
            let now = Instant::now();
            let dur = if next.when > now { next.when - now } else { Duration::from_millis(0) };
            let (_g2, _) = self.cv.wait_timeout(g, dur).unwrap();
        } else {
            let (_g2, _) = self.cv.wait_timeout(g, Duration::from_millis(1)).unwrap();
        }

        false
    }

    // Block and drive the loop until no pending timers exist.
    pub fn run_until_quiescent(
        &self,
        mut call_micro: impl FnMut(i64, i64),  // (fun, arg)
        mut call_timer: impl FnMut(i64),       // (fun)
    ) {
        loop {
            // 1) Drain all microtasks
            let _ = self.run_microtasks(usize::MAX, |f, a| call_micro(f, a));

            // 2) Timers
            self.poll_due_and_enqueue();
            let _ran = self.run_ready(usize::MAX, &mut call_timer);

            // 3) Quiescence / wait
            let mut g = self.m.lock().unwrap();
            if g.active == 0 && g.ready.is_empty() && g.micro.is_empty() { break; }
            if !g.micro.is_empty() { continue; }

            if let Some(std::cmp::Reverse(next)) = g.heap.peek().cloned() {
                let now = Instant::now();
                if next.when <= now { continue; }
                let dur = next.when - now;
                let (g2, _) = self.cv.wait_timeout(g, dur).unwrap();
                g = g2;
            } else if g.ready.is_empty() {
                let (g2, _) = self.cv.wait_timeout(g, Duration::from_millis(1)).unwrap();
                g = g2;
            }
        }
    }

    // Root scanning hook for the GC: now also visit microtask closures
    pub fn with_root_slots<F: FnMut(*mut i64)>(&self, mut f: F) {
        let g = self.m.lock().unwrap();
        for Reverse(t) in g.heap.iter()  { let ptr = &t.fun as *const i64 as *mut i64; f(ptr); }
        for t in g.ready.iter()          { let ptr = &t.fun as *const i64 as *mut i64; f(ptr); }
        for m in g.micro.iter()          { let ptr = &m.fun as *const i64 as *mut i64; f(ptr); }
    }
}
