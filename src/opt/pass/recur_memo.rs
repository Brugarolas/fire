#![allow(dead_code)]

use crate::opt::{InstCursor, OptimizationWIR, WirEditQueue};
use crate::wir::{Function, Inst, FuncId, Type};

#[derive(Default)]
pub struct MemoizeRecursion {
    last_func: Option<FuncId>,
}

impl OptimizationWIR for MemoizeRecursion {
    fn optimize_node(&mut self, cur: &mut InstCursor, _q: &mut WirEditQueue) -> bool {
        // Run at most once per function
        let mut already = false;
        cur.with_func(|f| {
            already = self.last_func == Some(f.id);
            if !already {
                self.last_func = Some(f.id);
            }
        });
        if already { return false; }

        cur.with_func(|f| run_on_function(f));
        // Function-level transform; per-node "changed" signal not meaningful here.
        false
    }
}

fn run_on_function(func: &mut Function) {
    // 1) single parameter?
    if func.sig.params.len() != 1 { return; }

    // 2) primitive parameter?
    if !is_primitive_ty(&func.sig.params[0]) { return; }

    // 3 & 4) scan for only self-calls and no external state
    let self_id = func.id;
    let mut saw_self_call = false;

    for n in &func.nodes {
        match &n.kind {
            // allow direct self calls; reject other direct calls
            Inst::CallDirect { callee, .. } => {
                if *callee == self_id {
                    saw_self_call = true;
                } else {
                    return; // calls someone else
                }
            }
            // disallow any other call shape
            Inst::CallIC { .. }
            | Inst::CallClosure { .. }
            | Inst::CallNative { .. } => return,

            // allowed pure compute/control:
            Inst::Const(_)
            | Inst::Mov(_)
            | Inst::IntBin { .. }
            | Inst::F64Bin { .. }
            | Inst::CmpInt { .. }
            | Inst::CmpF64 { .. }
            | Inst::Phi(_)
            | Inst::Jump(_, _)
            | Inst::Branch { .. }
            | Inst::Switch { .. }
            | Inst::Return(_)
            | Inst::EffectEntry
            | Inst::Safepoint
            | Inst::OSRPoint => { /* ok */ }

            // everything else is treated as external state / effects
            _ => return,
        }
    }

    if !saw_self_call { return; }

    // Rewrite direct self-calls to memoized
    for n in &mut func.nodes {
        if let Inst::CallDirect { callee, args, .. } = &n.kind {
            if *callee == self_id && args.len() == 1 {
                n.kind = Inst::CallDirectMemoized { callee: *callee, args: args.clone() };
            }
        }
    }
}

fn is_primitive_ty(t: &Type) -> bool {
    matches!(t, Type::Int32 | Type::F64 | Type::Bool | Type::Null | Type::Num)
}
