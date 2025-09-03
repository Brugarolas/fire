use crate::opt::Optimize;
use crate::opt::OptimizationPass;
use crate::opt::pass::peephole_simplify::PeepholeSimplify;
use crate::opt::pass::const_fold::ConstFold;
use crate::opt::pass::copy_propagation::CopyPropagation;
use crate::opt::pass::branch_fold::BranchFold;
use crate::opt::pass::guards::GuardElim;
use crate::opt::pass::strength_reduction::StrengthReduction;
use crate::opt::pass::licm::Licm;
use crate::opt::pass::sccp::Sccp;
use crate::opt::pass::value_numbering::GlobalValueNumbering;
use crate::opt::pass::dead_code_elim::MegaDCE;
use crate::opt::pass::com_subexpr_elim::CommonSubexprElim;
use crate::opt::pass::recur_memo::MemoizeRecursion;

pub fn optimization_passes() -> Optimize {
    let early = OptimizationPass::new(vec![
        Box::new(ConstFold),         // fold consts first
        Box::new(PeepholeSimplify),  // then cheap canonical forms
        Box::new(CopyPropagation),   // finally, copy propagation
        Box::new(StrengthReduction), // after copy propagation to catch more patterns
        Box::new(CommonSubexprElim::default()), // common subexpression elimination before any global passes
        Box::new(MegaDCE::default()), // after local rewrites to clean up dead code

        Box::new(BranchFold::default()), // cheap local rewrites first to expose CSE opportunities
        Box::new(GuardElim::default()),  // guards before GVN so we can delete redundant guards that otherwise block CSE

        Box::new(Licm), // loop invariant code motion to hoist out of loops
        Box::new(Sccp::default()), // sparse conditional constant propagation to simplify based on known values
        Box::new(GlobalValueNumbering::default()), // global value numbering to eliminate redundant calculations
        Box::new(MegaDCE::default()), // final DCE to clean up after all the other passes

        Box::new(MemoizeRecursion::default()), // last, convert direct recursive calls to memoized calls (specific optimizations)
    ]);

    Optimize::new().with_pass(early)
}
