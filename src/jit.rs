// src/jit.rs
//! jit.rs — Cranelift JIT for WIR (Cranelift 0.121.x compatible)

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module as _};

use crate::wir::{
    Constant, Function as WirFunction, Inst, IntBinOp, Value as WirValue, ValueDef, ValueId,
};

/// ABI: `unsafe extern "C" fn(argv: *const i64, argc: usize) -> i64`
pub type JitFnPtr = unsafe extern "C" fn(*const i64, usize) -> i64;

pub struct JIT {
    module: JITModule,
    fctx: FunctionBuilderContext,
}

impl Default for JIT {
    fn default() -> Self {
        // Cranelift 0.121: JITBuilder::new returns Result
        let jb = JITBuilder::new(cranelift_module::default_libcall_names())
            .expect("JITBuilder::new");
        let module = JITModule::new(jb);
        Self {
            module,
            fctx: FunctionBuilderContext::new(),
        }
    }
}

impl JIT {
    pub fn compile(&mut self, fun: &WirFunction) -> Result<JitFnPtr, String> {
        // Build a fresh context each compile
        let mut ctx = self.module.make_context();

        // (argv: ptr, argc: i64) -> i64
        let ptr_ty = self.module.target_config().pointer_type();
        ctx.func.signature.params.push(AbiParam::new(ptr_ty));
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        ctx.func.signature.returns.push(AbiParam::new(types::I64));

        // CLIF builder
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut self.fctx);
        let entry = fb.create_block();
        fb.append_block_params_for_function_params(entry);
        fb.switch_to_block(entry);

        let (args_base, _argc) = {
            let p = fb.block_params(entry);
            (p[0], p[1])
        };

        let mut vmap = ValueMap::new();
        let mut terminated = false;

        // Straight-line lowering: block 0 only for now
        for nid in &fun.blocks[0].insts {
            if terminated { break; }

            let node = &fun.nodes[nid.0 as usize];
            let res_count = node.results.len();

            let mut emit_const = |c: &Constant| -> Value {
                match c {
                    Constant::Int32(x) => fb.ins().iconst(types::I64, *x as i64),
                    Constant::F64(f)   => fb.ins().iconst(types::I64, f.to_bits() as i64),
                    Constant::Bool(b)  => fb.ins().iconst(types::I64, if *b { 1 } else { 0 }),
                    Constant::Null     => fb.ins().iconst(types::I64, 0),
                    Constant::Str(_)   => { trap_unsupported(&mut fb, "Const(Str)"); terminated = true; fb.ins().iconst(types::I64, 0) }
                }
            };

            match &node.kind {
                Inst::Const(c) => {
                    let v = emit_const(c);
                    if res_count == 1 { vmap.bind(node.results[0], v); }
                }

                Inst::Mov(src) => {
                    let v = vmap.get_or_load(*src, &mut fb, args_base, &fun.values);
                    if res_count == 1 { vmap.bind(node.results[0], v); }
                }

                Inst::IntBin { op, a, b } => {
                    let a = vmap.get_or_load(*a, &mut fb, args_base, &fun.values);
                    let b = vmap.get_or_load(*b, &mut fb, args_base, &fun.values);
                    let v = match op {
                        IntBinOp::Add => fb.ins().iadd(a, b),
                        IntBinOp::Sub => fb.ins().isub(a, b),
                        IntBinOp::Mul => fb.ins().imul(a, b),
                        IntBinOp::DivS => fb.ins().sdiv(a, b),
                        IntBinOp::RemS => fb.ins().srem(a, b),
                        IntBinOp::And => fb.ins().band(a, b),
                        IntBinOp::Or  => fb.ins().bor(a, b),
                        IntBinOp::Xor => fb.ins().bxor(a, b),
                        IntBinOp::Shl => fb.ins().ishl(a, b),
                        IntBinOp::ShrU => fb.ins().ushr(a, b),
                        IntBinOp::Sar => fb.ins().sshr(a, b),
                    };
                    if res_count == 1 { vmap.bind(node.results[0], v); }
                }

                Inst::CmpInt { kind, a, b } => {
                    let a = vmap.get_or_load(*a, &mut fb, args_base, &fun.values);
                    let b = vmap.get_or_load(*b, &mut fb, args_base, &fun.values);
                    let cc = match kind {
                        crate::wir::CmpKind::Eq => IntCC::Equal,
                        crate::wir::CmpKind::Ne => IntCC::NotEqual,
                        crate::wir::CmpKind::Lt => IntCC::SignedLessThan,
                        crate::wir::CmpKind::Le => IntCC::SignedLessThanOrEqual,
                        crate::wir::CmpKind::Gt => IntCC::SignedGreaterThan,
                        crate::wir::CmpKind::Ge => IntCC::SignedGreaterThanOrEqual,
                    };
                    let cond = fb.ins().icmp(cc, a, b);
                    let one = fb.ins().iconst(types::I64, 1);
                    let zero = fb.ins().iconst(types::I64, 0);
                    let v = fb.ins().select(cond, one, zero);
                    if res_count == 1 { vmap.bind(node.results[0], v); }
                }

                Inst::Return(vals) => {
                    let ret = if vals.is_empty() {
                        fb.ins().iconst(types::I64, 0)
                    } else {
                        vmap.get_or_load(vals[0], &mut fb, args_base, &fun.values)
                    };
                    fb.ins().return_(&[ret]);
                    terminated = true; // nothing else allowed in this block
                }

                // Benign markers:
                Inst::EffectEntry => {}
                Inst::Safepoint => {}

                // Everything else -> trap (terminator) and stop emitting
                _ => {
                    trap_unsupported(&mut fb, "unsupported");
                    terminated = true;
                }
            }
        }

        // If we never emitted a terminator, add a default return now.
        if !terminated {
            let zero = fb.ins().iconst(types::I64, 0);
            fb.ins().return_(&[zero]);
            terminated = true;
        }

        fb.seal_all_blocks();
        fb.finalize();

        // Declare, define, finalize
        let name = format!("wir_f_{}", self.module.declarations().get_functions().count());
        let func_id = self
            .module
            .declare_function(&name, Linkage::Local, &ctx.func.signature)
            .map_err(|e| e.to_string())?;
        self.module.define_function(func_id, &mut ctx).map_err(|e| e.to_string())?;
        self.module.clear_context(&mut ctx);
        self.module.finalize_definitions().map_err(|e| e.to_string())?;

        let code = self.module.get_finalized_function(func_id);
        let fptr: JitFnPtr = unsafe { std::mem::transmute(code) };
        Ok(fptr)
    }
}

/// Value binder: maps WIR ValueIds to CLIF Values, and lazily loads argv[idx] when needed.
struct ValueMap {
    map: HashMap<ValueId, Value>,
}

impl ValueMap {
    fn new() -> Self {
        Self { map: HashMap::new() }
    }

    fn bind(&mut self, id: ValueId, v: Value) {
        self.map.insert(id, v);
    }

    fn get(&self, id: ValueId) -> Option<Value> {
        self.map.get(&id).copied()
    }

    fn get_or_load(
        &mut self,
        id: ValueId,
        fb: &mut FunctionBuilder,
        args_base: Value,
        values: &Vec<WirValue>,
    ) -> Value {
        if let Some(v) = self.get(id) {
            return v;
        }
        if let Some(v) = synth_const(values, id, fb) {
            self.bind(id, v);
            return v;
        }
        // Fallback: treat as positional argument at index `id.0` (demo ABI).
        let offset = (id.0 as i64) * 8;
        let addr = fb.ins().iadd_imm(args_base, offset);
        let loaded = fb.ins().load(types::I64, MemFlags::trusted(), addr, 0);
        self.bind(id, loaded);
        loaded
    }
}

fn synth_const(values: &Vec<WirValue>, id: ValueId, fb: &mut FunctionBuilder) -> Option<Value> {
    match &values[id.0 as usize].def {
        ValueDef::Const(c) => match c {
            Constant::Int32(x) => Some(fb.ins().iconst(types::I64, *x as i64)),
            Constant::F64(f) => Some(fb.ins().iconst(types::I64, f.to_bits() as i64)),
            Constant::Bool(b) => Some(fb.ins().iconst(types::I64, if *b { 1 } else { 0 })),
            Constant::Null => Some(fb.ins().iconst(types::I64, 0)),
            Constant::Str(_) => None,
        },
        _ => None,
    }
}

fn trap_unsupported(fb: &mut FunctionBuilder, _what: &str) {
    // 'trap' is a terminator. Do NOT emit any further instructions in this block.
    let code = TrapCode::unwrap_user(0xE0);
    fb.ins().trap(code);
}
