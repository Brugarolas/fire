pub mod peephole_simplify;
pub mod const_fold;
pub mod copy_propagation;
pub mod strength_reduction;
pub mod com_subexpr_elim;
// pub mod dead_code_elim;
// pub mod unreachable_code_elim;
// pub mod dead_store_elim;
// pub mod tail_call_opt;
// pub mod inlining;
pub mod dead_code_elim;

pub mod branch_fold;
pub mod guards;

pub mod licm;
pub mod sccp;
pub mod value_numbering;

pub mod recur_memo;