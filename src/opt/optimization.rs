#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::opt::OptimizationPass;
use crate::opt::Optimize;
use crate::opt::pass::branch_fold::BranchFold;
use crate::opt::pass::com_subexpr_elim::CommonSubexprElim;
use crate::opt::pass::const_fold::ConstFold;
use crate::opt::pass::dead_code_elim::DCE;
use crate::opt::pass::dead_store_elim::DeadStoreElim;
use crate::opt::pass::licm::Licm;
use crate::opt::pass::peephole_simplify::PeepholeSimplify;
use crate::opt::pass::recur_memo::MemoizeRecursion;
use crate::opt::pass::rle_lsf::RedundantLoadElim;
use crate::opt::pass::sccp::Sccp;
use crate::opt::pass::simplify_cfg::SimplifyCFG;
use crate::opt::pass::sroa::SROA;
use crate::opt::pass::tail_call::TailCallOpt;
use crate::opt::pass::value_numbering::GlobalValueNumbering;

pub fn optimization_passes() -> Optimize {
    let early = OptimizationPass::new(vec![
        Box::new(SROA::default()), // scalar replacement of aggregates to expose more optimization opportunities
        Box::new(ConstFold::default()), // fold consts first
        Box::new(PeepholeSimplify::default()), // then cheap canonical forms
        Box::new(SimplifyCFG::default()), // simplify CFG to remove empty blocks, etc.
        Box::new(BranchFold::default()), // cheap local rewrites first to expose CSE opportunities
        Box::new(CommonSubexprElim::default()), // common subexpression elimination before any global passes
        Box::new(DCE::default()),               // after local rewrites to clean up dead code
        Box::new(DeadStoreElim::default()), // dead store elimination to remove stores to dead variables
        Box::new(RedundantLoadElim::default()), // redundant load elimination to remove loads that can be replaced with existing values
        Box::new(Sccp::default()), // sparse conditional constant propagation to simplify based on known values
        Box::new(SimplifyCFG::default()), // again; SCCP creates new merges
        Box::new(Licm::default()), // loop invariant code motion to hoist out of loops
        Box::new(GlobalValueNumbering::default()), // global value numbering to eliminate redundant calculations
        Box::new(DCE::default()),                  // after global passes to clean up dead code
        Box::new(TailCallOpt::new()), // tail call optimization (self-recursive calls to jumps)
        Box::new(MemoizeRecursion::default()), // last, convert direct recursive calls to memoized calls (specific optimizations)
    ]);

    Optimize::new().with_pass(early)
}
