use crate::opt::Optimize;
use crate::opt::OptimizationPass;
use crate::opt::pass::peephole_simplify::PeepholeSimplify;
use crate::opt::pass::const_fold::ConstFold;
use crate::opt::pass::copy_propagation::CopyPropagation;
use crate::opt::pass::branch_fold::BranchFold;
use crate::opt::pass::guards::GuardElim;

pub fn early_pipeline() -> Optimize {
    let early = OptimizationPass::new(vec![
        Box::new(ConstFold),         // fold consts first
        Box::new(PeepholeSimplify),  // then cheap canonical forms
        Box::new(CopyPropagation),   // finally, copy propagation

        Box::new(BranchFold::default()), // cheap local rewrites first to expose CSE opportunities
        Box::new(GuardElim::default()),  // guards before GVN so we can delete redundant guards that otherwise block CSE
    ]);

    Optimize::new().with_pass(early)
}
