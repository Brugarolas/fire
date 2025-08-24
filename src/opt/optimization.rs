use crate::opt::Optimize;
use crate::opt::OptimizationPass;
use crate::opts::peephole_simplify::PeepholeSimplify;
use crate::opts::const_fold::ConstFold;

pub fn early_pipeline() -> Optimize {
    let early = OptimizationPass::new(vec![
        Box::new(ConstFold),         // fold consts first
        Box::new(PeepholeSimplify),  // then cheap canonical forms
    ]);

    Optimize::new().with_pass(early)
}
