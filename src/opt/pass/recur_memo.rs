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
    let arity = func.sig.params.len();
    if !(1..=4).contains(&arity) { return; }
    if !func.sig.params.iter().all(is_primitive_ty) { return; }

    let self_id = func.id;
    let mut saw_self_call = false;

    for n in &func.nodes {
        match &n.kind {
            Inst::CallDirect { callee, .. } => {
                if *callee == self_id {
                    saw_self_call = true;
                } else {
                    return; // calls someone else
                }
            }
            // reject any non-direct call shape
            Inst::CallIC { .. } | Inst::CallClosure { .. } | Inst::CallNative { .. } => return,

            // allowed pure compute/control/markers:
            Inst::Const(_) | Inst::Mov(_)
            | Inst::IntBin { .. } | Inst::F64Bin { .. }
            | Inst::CmpInt { .. } | Inst::CmpF64 { .. }
            | Inst::Phi(_) | Inst::Jump(_, _) | Inst::Branch { .. } | Inst::Switch { .. }
            | Inst::Return(_) | Inst::EffectEntry | Inst::Safepoint | Inst::OSRPoint => {}

            // everything else = effects / external state
            _ => return,
        }
    }
    if !saw_self_call { return; }

    for n in &mut func.nodes {
        if let Inst::CallDirect { callee, args, .. } = &n.kind {
            if *callee == self_id && (1..=4).contains(&args.len()) {
                n.kind = Inst::CallDirectMemoized { callee: *callee, args: args.clone() };
            }
        }
    }
}

fn is_primitive_ty(t: &Type) -> bool {
    matches!(t, Type::Int32 | Type::F64 | Type::Bool | Type::Null | Type::Num)
}

