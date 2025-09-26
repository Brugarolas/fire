#![allow(unused_imports)]
#![allow(unused_variables)]

pub mod branch_fold;
pub mod com_subexpr_elim;
pub mod const_fold;
pub mod dead_code_elim;
pub mod dead_store_elim;
pub mod licm;
pub mod peephole_simplify;
pub mod recur_memo;
pub mod rle_lsf;
pub mod sccp;
pub mod simplify_cfg;
pub mod sroa;
pub mod tail_call;
pub mod value_numbering;
