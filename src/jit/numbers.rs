//! Number semantics for `IntBin` / `CmpInt`.
//!
//! Both operands being small integers is the common case and is handled inline. Everything
//! else (floats, overflow, inexact division, string `+`) goes to a slow path that is itself
//! compiled with Cranelift once per operator and shared by every call site.
use super::*;
use crate::value::{BoxedF64, TAG_BOXED_F64};
use crate::wir::CmpKind;
use cranelift::codegen::ir::Block;

const SMI_MIN: i64 = i64::MIN >> 1;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum NumHelper {
    Bin(IntBinOp),
    Cmp(CmpKind),
}

impl NumHelper {
    fn symbol(self) -> String {
        match self {
            NumHelper::Bin(op) => format!("__napalm_num_{op:?}"),
            NumHelper::Cmp(kind) => format!("__napalm_cmp_{kind:?}"),
        }
    }
}

fn is_bitwise(op: IntBinOp) -> bool {
    matches!(
        op,
        IntBinOp::And
            | IntBinOp::Or
            | IntBinOp::Xor
            | IntBinOp::Shl
            | IntBinOp::Sar
            | IntBinOp::ShrU
            | IntBinOp::Not
    )
}

fn raw_int_op(fb: &mut FunctionBuilder, op: IntBinOp, a: Value, b: Value) -> Value {
    match op {
        IntBinOp::Add => fb.ins().iadd(a, b),
        IntBinOp::Sub => fb.ins().isub(a, b),
        IntBinOp::Mul => fb.ins().imul(a, b),
        IntBinOp::DivS => fb.ins().sdiv(a, b),
        IntBinOp::RemS => fb.ins().srem(a, b),
        IntBinOp::And => fb.ins().band(a, b),
        IntBinOp::Or => fb.ins().bor(a, b),
        IntBinOp::Xor => fb.ins().bxor(a, b),
        IntBinOp::Shl => fb.ins().ishl(a, b),
        IntBinOp::ShrU => fb.ins().ushr(a, b),
        IntBinOp::Sar => fb.ins().sshr(a, b),
        IntBinOp::Not => fb.ins().bnot(a),
    }
}

fn smi_encode(fb: &mut FunctionBuilder, raw: Value) -> Value {
    let shifted = fb.ins().ishl_imm_s(raw, 1);
    fb.ins().bor_imm_s(shifted, 1)
}

/// Jump to `done(smi(raw))` when `raw` fits in a small integer, else to `overflow`.
fn finish_checked(fb: &mut FunctionBuilder, raw: Value, done: Block, overflow: Block) {
    let shifted = fb.ins().ishl_imm_s(raw, 1);
    let back = fb.ins().sshr_imm_s(shifted, 1);
    let fits = fb.ins().icmp(IntCC::Equal, back, raw);
    let encoded = fb.ins().bor_imm_s(shifted, 1);
    fb.ins().brif(fits, done, &[encoded.into()], overflow, &[]);
}

impl JIT {
    /// `a op b` with a small-integer fast path and a shared compiled slow path.
    pub(super) fn emit_int_bin(
        &mut self,
        fb: &mut FunctionBuilder,
        op: IntBinOp,
        a: Value,
        b: Value,
    ) -> Result<Value, String> {
        let helper = self.num_helper(NumHelper::Bin(op))?;
        let fast = fb.create_block();
        let slow = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);
        fb.set_cold_block(slow);

        let both = fb.ins().band(a, b);
        let both_smi = fb.ins().band_imm_s(both, 1);
        fb.ins().brif(both_smi, fast, &[], slow, &[]);

        fb.switch_to_block(fast);
        let ra = fb.ins().sshr_imm_s(a, 1);
        let rb = fb.ins().sshr_imm_s(b, 1);
        match op {
            IntBinOp::Add | IntBinOp::Sub => {
                let raw = raw_int_op(fb, op, ra, rb);
                finish_checked(fb, raw, done, slow);
            }
            IntBinOp::Mul => {
                let (raw, overflow) = fb.ins().smul_overflow(ra, rb);
                let check = fb.create_block();
                fb.ins().brif(overflow, slow, &[], check, &[]);
                fb.switch_to_block(check);
                finish_checked(fb, raw, done, slow);
            }
            IntBinOp::DivS | IntBinOp::RemS => {
                // Operands are 63-bit, so `srem`/`sdiv` cannot hit the i64::MIN / -1 trap.
                let nonzero = fb.create_block();
                fb.ins().brif(rb, nonzero, &[], slow, &[]);
                fb.switch_to_block(nonzero);
                let rem = fb.ins().srem(ra, rb);
                if op == IntBinOp::RemS {
                    let encoded = smi_encode(fb, rem);
                    fb.ins().jump(done, &[encoded.into()]);
                } else {
                    let exact = fb.create_block();
                    fb.ins().brif(rem, slow, &[], exact, &[]);
                    fb.switch_to_block(exact);
                    let quotient = fb.ins().sdiv(ra, rb);
                    finish_checked(fb, quotient, done, slow);
                }
            }
            _ => {
                let raw = raw_int_op(fb, op, ra, rb);
                let encoded = smi_encode(fb, raw);
                fb.ins().jump(done, &[encoded.into()]);
            }
        }

        fb.switch_to_block(slow);
        let callee = self.module.declare_func_in_func(helper, fb.func);
        let call = fb.ins().call(callee, &[a, b]);
        let slow_result = fb.inst_results(call)[0];
        fb.ins().jump(done, &[slow_result.into()]);

        fb.switch_to_block(done);
        Ok(result)
    }

    /// Comparison producing a tagged bool. Small integers (and immediates such as booleans)
    /// compare inline; boxed operands go through the shared slow path.
    pub(super) fn emit_cmp(
        &mut self,
        fb: &mut FunctionBuilder,
        kind: CmpKind,
        a: Value,
        b: Value,
    ) -> Result<Value, String> {
        let helper = self.num_helper(NumHelper::Cmp(kind))?;
        let fast = fb.create_block();
        let slow = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);
        fb.set_cold_block(slow);

        let a_ptr = Self::emit_is_ptr(fb, a);
        let b_ptr = Self::emit_is_ptr(fb, b);
        let any_ptr = fb.ins().bor(a_ptr, b_ptr);
        fb.ins().brif(any_ptr, slow, &[], fast, &[]);

        fb.switch_to_block(fast);
        let value = Self::emit_legacy_cmp(fb, kind, a, b);
        fb.ins().jump(done, &[value.into()]);

        fb.switch_to_block(slow);
        let callee = self.module.declare_func_in_func(helper, fb.func);
        let call = fb.ins().call(callee, &[a, b]);
        let slow_result = fb.inst_results(call)[0];
        fb.ins().jump(done, &[slow_result.into()]);

        fb.switch_to_block(done);
        Ok(result)
    }

    fn emit_is_ptr(fb: &mut FunctionBuilder, v: Value) -> Value {
        let nonnull = fb.ins().icmp_imm_s(IntCC::NotEqual, v, 0);
        let bits = fb.ins().band_imm_s(v, PTR_TAG_MASK);
        let aligned = fb.ins().icmp_imm_s(IntCC::Equal, bits, 0);
        fb.ins().band(nonnull, aligned)
    }

    /// Integer comparison of immediates: booleans decode to 0/1, everything else is
    /// compared by its untagged bits (pointer identity for heap values).
    fn emit_legacy_cmp(fb: &mut FunctionBuilder, kind: CmpKind, a: Value, b: Value) -> Value {
        let decode = |fb: &mut FunctionBuilder, v: Value| {
            let is_true = fb.ins().icmp_imm_s(IntCC::Equal, v, BOOL_TRUE);
            let is_false = fb.ins().icmp_imm_s(IntCC::Equal, v, BOOL_FALSE);
            let is_bool = fb.ins().bor(is_true, is_false);
            let bool_raw = fb.ins().uextend(types::I64, is_true);
            let raw = fb.ins().sshr_imm_s(v, 1);
            fb.ins().select(is_bool, bool_raw, raw)
        };
        let ra = decode(fb, a);
        let rb = decode(fb, b);
        let cc = match kind {
            CmpKind::Eq => IntCC::Equal,
            CmpKind::Ne => IntCC::NotEqual,
            CmpKind::Lt => IntCC::SignedLessThan,
            CmpKind::Le => IntCC::SignedLessThanOrEqual,
            CmpKind::Gt => IntCC::SignedGreaterThan,
            CmpKind::Ge => IntCC::SignedGreaterThanOrEqual,
        };
        let cond = fb.ins().icmp(cc, ra, rb);
        Self::tagged_bool(fb, cond)
    }

    /// Returns (declaring and compiling on first use) the shared slow-path function.
    fn num_helper(&mut self, helper: NumHelper) -> Result<cranelift_module::FuncId, String> {
        if let Some(id) = self.num_helpers.get(&helper) {
            return Ok(*id);
        }
        let mut sig = self.module.make_signature();
        sig.call_conv = self.module.isa().default_call_conv();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = self
            .module
            .declare_function(&helper.symbol(), Linkage::Local, &sig)
            .map_err(|e| e.to_string())?;
        self.num_helpers.insert(helper, id);

        let mut ctx = self.module.make_context();
        ctx.func.signature = sig;
        let mut builder_ctx = FunctionBuilderContext::new();
        let mut fb = FunctionBuilder::new(&mut ctx.func, &mut builder_ctx);
        let entry = fb.create_block();
        fb.append_block_params_for_function_params(entry);
        fb.switch_to_block(entry);
        let (a, b) = (fb.block_params(entry)[0], fb.block_params(entry)[1]);
        let value = match helper {
            NumHelper::Bin(op) => self.build_bin_slow_path(&mut fb, op, a, b)?,
            NumHelper::Cmp(kind) => self.build_cmp_slow_path(&mut fb, kind, a, b),
        };
        fb.ins().return_(&[value]);
        fb.seal_all_blocks();
        fb.finalize(self.module.isa().frontend_config());
        self.module
            .define_function(id, &mut ctx)
            .map_err(|e| format!("define {}: {e:?}", helper.symbol()))?;
        self.module.clear_context(&mut ctx);
        Ok(id)
    }

    fn build_bin_slow_path(
        &mut self,
        fb: &mut FunctionBuilder,
        op: IntBinOp,
        a: Value,
        b: Value,
    ) -> Result<Value, String> {
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);

        if op == IntBinOp::Add {
            // `+` concatenates as soon as either side is a string.
            let concat = fb.create_block();
            let check_b = fb.create_block();
            let numeric = fb.create_block();
            self.tag_guard(fb, a, TAG_STRING, concat, check_b);
            fb.switch_to_block(check_b);
            self.tag_guard(fb, b, TAG_STRING, concat, numeric);
            fb.switch_to_block(concat);
            let joined = self.intrinsic_host(fb, "wir_string_concat_coerce", &[a, b])?;
            fb.ins().jump(done, &[joined.into()]);
            fb.switch_to_block(numeric);
        }

        let fa = self.emit_value_to_f64(fb, a);
        let fbv = self.emit_value_to_f64(fb, b);
        let value = if is_bitwise(op) {
            // Bitwise operators work on the integer part (NaN/±inf saturate; NaN -> 0).
            let ia = fb.ins().fcvt_to_sint_sat(types::I64, fa);
            let ib = fb.ins().fcvt_to_sint_sat(types::I64, fbv);
            let raw = raw_int_op(fb, op, ia, ib);
            smi_encode(fb, raw)
        } else {
            let x = match op {
                IntBinOp::Add => fb.ins().fadd(fa, fbv),
                IntBinOp::Sub => fb.ins().fsub(fa, fbv),
                IntBinOp::Mul => fb.ins().fmul(fa, fbv),
                IntBinOp::DivS => fb.ins().fdiv(fa, fbv),
                IntBinOp::RemS => {
                    // fmod: a - trunc(a / b) * b, keeping a when b is infinite.
                    let q = fb.ins().fdiv(fa, fbv);
                    let t = fb.ins().trunc(q);
                    let m = fb.ins().fmul(t, fbv);
                    let r = fb.ins().fsub(fa, m);
                    let abs_b = fb.ins().fabs(fbv);
                    let inf = fb.ins().f64const(f64::INFINITY);
                    let b_inf = fb.ins().fcmp(FloatCC::Equal, abs_b, inf);
                    let a_inf = fb.ins().fabs(fa);
                    let a_finite = fb.ins().fcmp(FloatCC::LessThan, a_inf, inf);
                    let keep_a = fb.ins().band(b_inf, a_finite);
                    fb.ins().select(keep_a, fa, r)
                }
                _ => unreachable!("bitwise ops handled above"),
            };
            self.emit_f64_to_value(fb, x)?
        };
        fb.ins().jump(done, &[value.into()]);
        fb.switch_to_block(done);
        Ok(result)
    }

    fn build_cmp_slow_path(
        &mut self,
        fb: &mut FunctionBuilder,
        kind: CmpKind,
        a: Value,
        b: Value,
    ) -> Value {
        let float = fb.create_block();
        let check_b = fb.create_block();
        let legacy = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);

        self.tag_guard(fb, a, TAG_BOXED_F64, float, check_b);
        fb.switch_to_block(check_b);
        self.tag_guard(fb, b, TAG_BOXED_F64, float, legacy);

        fb.switch_to_block(float);
        let fa = self.emit_value_to_f64(fb, a);
        let fbv = self.emit_value_to_f64(fb, b);
        let cc = match kind {
            CmpKind::Eq => FloatCC::Equal,
            CmpKind::Ne => FloatCC::NotEqual,
            CmpKind::Lt => FloatCC::LessThan,
            CmpKind::Le => FloatCC::LessThanOrEqual,
            CmpKind::Gt => FloatCC::GreaterThan,
            CmpKind::Ge => FloatCC::GreaterThanOrEqual,
        };
        let cond = fb.ins().fcmp(cc, fa, fbv);
        let value = Self::tagged_bool(fb, cond);
        fb.ins().jump(done, &[value.into()]);

        fb.switch_to_block(legacy);
        let value = Self::emit_legacy_cmp(fb, kind, a, b);
        fb.ins().jump(done, &[value.into()]);

        fb.switch_to_block(done);
        result
    }

    /// ToNumber: small int, boxed f64, null/false -> 0, true -> 1, anything else -> NaN.
    fn emit_value_to_f64(&self, fb: &mut FunctionBuilder, v: Value) -> Value {
        let smi = fb.create_block();
        let other = fb.create_block();
        let pointer = fb.create_block();
        let immediate = fb.create_block();
        let boxed = fb.create_block();
        let nan = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::F64);

        let tag_bit = fb.ins().band_imm_s(v, 1);
        fb.ins().brif(tag_bit, smi, &[], other, &[]);

        fb.switch_to_block(smi);
        let raw = fb.ins().sshr_imm_s(v, 1);
        let x = fb.ins().fcvt_from_sint(types::F64, raw);
        fb.ins().jump(done, &[x.into()]);

        fb.switch_to_block(other);
        let is_ptr = Self::emit_is_ptr(fb, v);
        fb.ins().brif(is_ptr, pointer, &[], immediate, &[]);

        fb.switch_to_block(immediate);
        let is_true = fb.ins().icmp_imm_s(IntCC::Equal, v, BOOL_TRUE);
        let one = fb.ins().f64const(1.0);
        let zero = fb.ins().f64const(0.0);
        let x = fb.ins().select(is_true, one, zero);
        fb.ins().jump(done, &[x.into()]);

        fb.switch_to_block(pointer);
        self.tag_guard(fb, v, TAG_BOXED_F64, boxed, nan);

        fb.switch_to_block(boxed);
        let ptr = self.value_as_ptr(fb, v);
        let x = fb.ins().load(
            types::F64,
            MemFlagsData::trusted(),
            ptr,
            offset_of!(BoxedF64, val) as i32,
        );
        fb.ins().jump(done, &[x.into()]);

        fb.switch_to_block(nan);
        let x = fb.ins().f64const(f64::NAN);
        fb.ins().jump(done, &[x.into()]);

        fb.switch_to_block(done);
        result
    }

    /// Integral results that fit a small integer stay unboxed; everything else is boxed.
    fn emit_f64_to_value(&mut self, fb: &mut FunctionBuilder, x: Value) -> Result<Value, String> {
        let check = fb.create_block();
        let boxed = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);

        let raw = fb.ins().fcvt_to_sint_sat(types::I64, x);
        let back = fb.ins().fcvt_from_sint(types::F64, raw);
        let integral = fb.ins().fcmp(FloatCC::Equal, back, x);
        fb.ins().brif(integral, check, &[], boxed, &[]);

        fb.switch_to_block(check);
        // fcvt saturates, so the range check also rejects values outside 63 bits.
        let low = fb.ins().icmp_imm_s(IntCC::SignedGreaterThanOrEqual, raw, SMI_MIN);
        let high = fb.ins().icmp_imm_s(IntCC::SignedLessThanOrEqual, raw, !SMI_MIN);
        let fits = fb.ins().band(low, high);
        let encoded = smi_encode(fb, raw);
        fb.ins().brif(fits, done, &[encoded.into()], boxed, &[]);

        fb.switch_to_block(boxed);
        let bits = fb.ins().bitcast(types::I64, MemFlagsData::new(), x);
        let value = self.intrinsic_host(fb, "wir_box_f64_runtime", &[bits])?;
        fb.ins().jump(done, &[value.into()]);

        fb.switch_to_block(done);
        Ok(result)
    }
}
