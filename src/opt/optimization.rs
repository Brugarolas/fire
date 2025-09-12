#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::Optimize;
use crate::opt::OptimizationPass;
/* use crate::opt::pass::peephole_simplify::PeepholeSimplify;
use crate::opt::pass::const_fold::ConstFold;
use crate::opt::pass::copy_propagation::CopyPropagation;
use crate::opt::pass::branch_fold::BranchFold;
use crate::opt::pass::strength_reduction::StrengthReduction;
use crate::opt::pass::licm::Licm;
use crate::opt::pass::sccp::Sccp;
use crate::opt::pass::value_numbering::GlobalValueNumbering;
use crate::opt::pass::dead_code_elim::MegaDCE;
use crate::opt::pass::com_subexpr_elim::CommonSubexprElim; */
use crate::opt::pass::recur_memo::MemoizeRecursion;
use crate::opt::pass::tail_call::TailCallOpt;

pub fn optimization_passes() -> Optimize {
    let early = OptimizationPass::new(vec![
        /*
        SmallBox::new(ConstFold),         // fold consts first
        SmallBox::new(PeepholeSimplify),  // then cheap canonical forms
        SmallBox::new(CopyPropagation),   // finally, copy propagation
        SmallBox::new(StrengthReduction), // after copy propagation to catch more patterns
        SmallBox::new(CommonSubexprElim::default()), // common subexpression elimination before any global passes
        SmallBox::new(MegaDCE::default()), // after local rewrites to clean up dead code
        SmallBox::new(BranchFold::default()), // cheap local rewrites first to expose CSE opportunities

        SmallBox::new(Licm), // loop invariant code motion to hoist out of loops
        SmallBox::new(Sccp::default()), // sparse conditional constant propagation to simplify based on known values
        SmallBox::new(GlobalValueNumbering::default()), // global value numbering to eliminate redundant calculations
        SmallBox::new(MegaDCE::default()), // final DCE to clean up after all the other passes
        */

        Box::new(TailCallOpt::new()), // tail call optimization (self-recursive calls to jumps)
        Box::new(MemoizeRecursion::default()), // last, convert direct recursive calls to memoized calls (specific optimizations)
    ]);

    Optimize::new().with_pass(early)
}

/*
let optimizer = Optimizer::new(
    let early = OptimizationPass::default()
        .with_optimization(SmallBox::new(ConstFold::default()))
        .with_optimization(SmallBox::new(PeepholeSimplify::default()))
        .with_optimization(SmallBox::new(CopyPropagation::default()))
        .with_optimization(SmallBox::new(StrengthReduction::default()))
        .with_optimization(SmallBox::new(CommonSubexprElim::default()))
        .with_optimization(SmallBox::new(DCE::default()));

    let secondary = OptimizationPass::default()
        .with_optimization(SmallBox::new(BranchFold::default()));
        .with_optimization(SmallBox::new(Licm::default()))
        .with_optimization(SmallBox::new(Sccp::default()))
        .with_optimization(SmallBox::new(GlobalValueNumbering::default()));
        .with_optimization(SmallBox::new(DCE::default()));

    let last = OptimizationPass::default()
        .with_optimization(SmallBox::new(TailCallOpt::new()))
        .with_optimization(SmallBox::new(MemoizeRecursion::default()));

    self.add_pass(early)
        .add_pass(secondary)
        .add_pass(last);

    self
) */
