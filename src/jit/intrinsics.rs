use super::*;
use crate::value::{TAG_ARRAY, TAG_BOXED_F64, TAG_CLOSURE, TAG_MAP, TAG_OBJECT, TAG_PROXY, TAG_SET};
use cranelift::codegen::ir::Block;

#[derive(Clone, Copy, Debug)]
struct VecLayout {
    data: i32,
    len: i32,
    cap: i32,
}

fn vec_layout() -> VecLayout {
    static LAYOUT: OnceLock<VecLayout> = OnceLock::new();
    *LAYOUT.get_or_init(|| {
        // Vec guarantees three words but not their order. Discover the host
        // compiler's layout once; never bake a guessed Rust ABI into JIT code.
        assert_eq!(mem::size_of::<Vec<i64>>(), 3 * mem::size_of::<usize>());
        let mut probe = Vec::<i64>::with_capacity(7);
        probe.extend([11, 22, 33]);
        let words =
            unsafe { std::slice::from_raw_parts((&probe as *const Vec<i64>).cast::<usize>(), 3) };
        let offset = |value| {
            let indices: Vec<_> = words
                .iter()
                .enumerate()
                .filter_map(|(i, word)| (*word == value).then_some(i))
                .collect();
            assert_eq!(indices.len(), 1, "unsupported Vec layout");
            ARRAY_BUF_OFFSET + (indices[0] * mem::size_of::<usize>()) as i32
        };
        VecLayout {
            data: offset(probe.as_ptr() as usize),
            len: offset(probe.len()),
            cap: offset(probe.capacity()),
        }
    })
}

impl JIT {
    pub(super) fn intrinsic_host(
        &mut self,
        fb: &mut FunctionBuilder,
        name: &str,
        args: &[Value],
    ) -> Result<Value, String> {
        self.call_host(
            fb,
            name,
            |sig| {
                sig.params
                    .extend(args.iter().map(|_| AbiParam::new(types::I64)));
                sig.returns.push(AbiParam::new(types::I64));
            },
            args,
        )
    }

    pub(super) fn tagged_bool(fb: &mut FunctionBuilder, condition: Value) -> Value {
        let yes = fb.ins().iconst(types::I64, BOOL_TRUE);
        let no = fb.ins().iconst(types::I64, BOOL_FALSE);
        fb.ins().select(condition, yes, no)
    }

    pub(super) fn tag_guard(
        &self,
        fb: &mut FunctionBuilder,
        value: Value,
        tag: u32,
        good: Block,
        bad: Block,
    ) {
        let check = fb.create_block();
        let nonnull = fb.ins().icmp_imm(IntCC::NotEqual, value, 0);
        let bits = fb.ins().band_imm(value, PTR_TAG_MASK);
        let aligned = fb.ins().icmp_imm(IntCC::Equal, bits, 0);
        let pointer = fb.ins().band(nonnull, aligned);
        fb.ins().brif(pointer, check, &[], bad, &[]);
        fb.switch_to_block(check);
        let ptr = self.value_as_ptr(fb, value);
        let actual = fb
            .ins()
            .load(types::I32, MemFlagsData::trusted(), ptr, OBJ_TAG_OFFSET);
        let matches = fb.ins().icmp_imm(IntCC::Equal, actual, tag as i64);
        fb.ins().brif(matches, good, &[], bad, &[]);
    }

    pub(super) fn emit_core_intrinsic(
        &mut self,
        fb: &mut FunctionBuilder,
        name: &str,
        args: &[Value],
    ) -> Result<Option<Value>, String> {
        let tag = match name {
            "wir_is_obj" => Some(TAG_OBJECT),
            "wir_is_str" => Some(TAG_STRING),
            "wir_is_map" => Some(TAG_MAP),
            "wir_is_set" => Some(TAG_SET),
            "wir_is_proxy" => Some(TAG_PROXY),
            "wir_is_array" => Some(TAG_ARRAY),
            "wir_is_closure" => Some(TAG_CLOSURE),
            _ => None,
        };
        if let Some(tag) = tag {
            let yes = fb.create_block();
            let no = fb.create_block();
            let done = fb.create_block();
            let result = fb.append_block_param(done, types::I64);
            self.tag_guard(fb, args[0], tag, yes, no);
            fb.switch_to_block(yes);
            let value = fb.ins().iconst(types::I64, BOOL_TRUE);
            fb.ins().jump(done, &[value.into()]);
            fb.switch_to_block(no);
            let value = fb.ins().iconst(types::I64, BOOL_FALSE);
            fb.ins().jump(done, &[value.into()]);
            fb.switch_to_block(done);
            return Ok(Some(result));
        }
        if matches!(name, "wir_is_nullish" | "wir_is_null") {
            let condition = fb.ins().icmp_imm(IntCC::Equal, args[0], 0);
            return Ok(Some(Self::tagged_bool(fb, condition)));
        }
        if name == "wir_is_bool" {
            let is_false = fb.ins().icmp_imm(IntCC::Equal, args[0], BOOL_FALSE);
            let is_true = fb.ins().icmp_imm(IntCC::Equal, args[0], BOOL_TRUE);
            let condition = fb.ins().bor(is_false, is_true);
            return Ok(Some(Self::tagged_bool(fb, condition)));
        }
        if name == "wir_is_number" {
            // Small integers carry the low tag bit; everything else must be a boxed f64.
            let yes = fb.create_block();
            let boxed = fb.create_block();
            let no = fb.create_block();
            let done = fb.create_block();
            let result = fb.append_block_param(done, types::I64);
            let smi_bit = fb.ins().band_imm(args[0], 1);
            fb.ins().brif(smi_bit, yes, &[], boxed, &[]);
            fb.switch_to_block(boxed);
            self.tag_guard(fb, args[0], TAG_BOXED_F64, yes, no);
            fb.switch_to_block(yes);
            let value = fb.ins().iconst(types::I64, BOOL_TRUE);
            fb.ins().jump(done, &[value.into()]);
            fb.switch_to_block(no);
            let value = fb.ins().iconst(types::I64, BOOL_FALSE);
            fb.ins().jump(done, &[value.into()]);
            fb.switch_to_block(done);
            return Ok(Some(result));
        }
        if matches!(
            name,
            "wir_array_len"
                | "wir_array_get"
                | "wir_array_set"
                | "wir_array_push"
                | "wir_array_pop"
                | "wir_array_shift"
                | "wir_array_unshift"
                | "wir_array_set_len"
                | "wir_array_fill"
        ) {
            return self.emit_array_intrinsic(fb, name, args).map(Some);
        }
        if matches!(
            name,
            "wir_string_len"
                | "wir_string_starts_with"
                | "wir_string_ends_with"
                | "wir_string_slice"
                | "wir_string_substring"
                | "wir_string_index_of"
                | "wir_string_last_index_of"
        ) {
            return self.emit_string_intrinsic(fb, name, args).map(Some);
        }
        if matches!(
            name,
            "wir_string_trim"
                | "wir_string_trim_start"
                | "wir_string_trim_end"
                | "wir_string_to_upper_case"
                | "wir_string_to_lower_case"
        ) {
            return self.emit_string_transform(fb, name, args[0]).map(Some);
        }
        Ok(None)
    }

    fn emit_array_intrinsic(
        &mut self,
        fb: &mut FunctionBuilder,
        name: &str,
        args: &[Value],
    ) -> Result<Value, String> {
        let layout = vec_layout();
        let ptr_ty = self.ptr_ty();
        let valid = fb.create_block();
        let empty = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);
        self.tag_guard(fb, args[0], TAG_ARRAY, valid, empty);
        fb.switch_to_block(empty);
        let default = fb.ins().iconst(
            types::I64,
            if matches!(
                name,
                "wir_array_len" | "wir_array_push" | "wir_array_unshift"
            ) {
                SMI_ZERO
            } else {
                0
            },
        );
        fb.ins().jump(done, &[default.into()]);
        fb.switch_to_block(valid);
        let array = self.value_as_ptr(fb, args[0]);
        let len = fb
            .ins()
            .load(ptr_ty, MemFlagsData::trusted(), array, layout.len);
        let len_i64 = self.ptr_to_i64(fb, len);
        if name == "wir_array_len" {
            let tagged = Self::encode_smi(fb, len_i64);
            fb.ins().jump(done, &[tagged.into()]);
            fb.switch_to_block(done);
            return Ok(result);
        }
        let data = fb
            .ins()
            .load(ptr_ty, MemFlagsData::trusted(), array, layout.data);
        let zero = fb.ins().iconst(types::I64, 0);
        let slow = fb.create_block();
        match name {
            "wir_array_get" | "wir_array_set" => {
                let index = fb.ins().sshr_imm_s(args[1], 1);
                let nonnegative = fb.create_block();
                let negative = fb.ins().icmp_imm(IntCC::SignedLessThan, index, 0);
                fb.ins()
                    .brif(negative, done, &[zero.into()], nonnegative, &[]);
                fb.switch_to_block(nonnegative);
                let inbounds = fb.create_block();
                let fits = fb.ins().icmp(IntCC::UnsignedLessThan, index, len_i64);
                if name == "wir_array_get" {
                    fb.ins().brif(fits, inbounds, &[], done, &[zero.into()]);
                } else {
                    fb.ins().brif(fits, inbounds, &[], slow, &[]);
                }
                fb.switch_to_block(inbounds);
                let slot = Self::array_slot(self, fb, data, index);
                if name == "wir_array_get" {
                    let value = fb.ins().load(types::I64, MemFlagsData::trusted(), slot, 0);
                    fb.ins().jump(done, &[value.into()]);
                } else {
                    self.guard_array_store(fb, args[2], slow);
                    fb.ins().store(MemFlagsData::trusted(), args[2], slot, 0);
                    fb.ins().jump(done, &[zero.into()]);
                }
            }
            "wir_array_pop" | "wir_array_shift" => {
                let nonempty = fb.create_block();
                let is_empty = fb.ins().icmp_imm(IntCC::Equal, len, 0);
                fb.ins().brif(is_empty, done, &[zero.into()], nonempty, &[]);
                fb.switch_to_block(nonempty);
                let new_len = fb.ins().iadd_imm_s(len_i64, -1);
                let index = if name == "wir_array_pop" {
                    new_len
                } else {
                    zero
                };
                let slot = self.array_slot(fb, data, index);
                let value = fb.ins().load(types::I64, MemFlagsData::trusted(), slot, 0);
                if name == "wir_array_shift" {
                    self.shift_array(fb, data, new_len, false);
                }
                let new_len_ptr = self.value_as_ptr(fb, new_len);
                fb.ins()
                    .store(MemFlagsData::trusted(), new_len_ptr, array, layout.len);
                fb.ins().jump(done, &[value.into()]);
            }
            "wir_array_push" | "wir_array_unshift" => {
                let cap = fb
                    .ins()
                    .load(ptr_ty, MemFlagsData::trusted(), array, layout.cap);
                let space = fb.create_block();
                let fits = fb.ins().icmp(IntCC::UnsignedLessThan, len, cap);
                fb.ins().brif(fits, space, &[], slow, &[]);
                fb.switch_to_block(space);
                self.guard_array_store(fb, args[1], slow);
                let index = if name == "wir_array_push" {
                    len_i64
                } else {
                    zero
                };
                if name == "wir_array_unshift" {
                    self.shift_array(fb, data, len_i64, true);
                }
                let slot = self.array_slot(fb, data, index);
                fb.ins().store(MemFlagsData::trusted(), args[1], slot, 0);
                let new_len = fb.ins().iadd_imm_s(len, 1);
                fb.ins()
                    .store(MemFlagsData::trusted(), new_len, array, layout.len);
                let new_len = self.ptr_to_i64(fb, new_len);
                let tagged = Self::encode_smi(fb, new_len);
                fb.ins().jump(done, &[tagged.into()]);
            }
            "wir_array_set_len" => {
                let requested = fb.ins().sshr_imm_s(args[1], 1);
                let count = fb.ins().smax(requested, zero);
                let cap = fb
                    .ins()
                    .load(ptr_ty, MemFlagsData::trusted(), array, layout.cap);
                let cap_i64 = self.ptr_to_i64(fb, cap);
                let fits = fb
                    .ins()
                    .icmp(IntCC::UnsignedLessThanOrEqual, count, cap_i64);
                let space = fb.create_block();
                fb.ins().brif(fits, space, &[], slow, &[]);
                fb.switch_to_block(space);
                self.fill_array_range(fb, data, len_i64, count, zero);
                let count = self.value_as_ptr(fb, count);
                fb.ins()
                    .store(MemFlagsData::trusted(), count, array, layout.len);
                fb.ins().jump(done, &[zero.into()]);
            }
            "wir_array_fill" => {
                self.guard_array_store(fb, args[1], slow);
                self.fill_array_range(fb, data, zero, len_i64, args[1]);
                fb.ins().jump(done, &[zero.into()]);
            }
            _ => unreachable!(),
        }
        if matches!(
            name,
            "wir_array_set"
                | "wir_array_push"
                | "wir_array_unshift"
                | "wir_array_set_len"
                | "wir_array_fill"
        ) {
            fb.switch_to_block(slow);
            let fallback = self.intrinsic_host(fb, name, args)?;
            fb.ins().jump(done, &[fallback.into()]);
        }
        fb.switch_to_block(done);
        Ok(result)
    }

    fn encode_smi(fb: &mut FunctionBuilder, raw: Value) -> Value {
        let shifted = fb.ins().ishl_imm_s(raw, 1);
        fb.ins().bor_imm(shifted, 1)
    }

    fn array_slot(&self, fb: &mut FunctionBuilder, data: Value, index: Value) -> Value {
        let bytes = fb.ins().ishl_imm_s(index, 3);
        let offset = self.value_as_ptr(fb, bytes);
        fb.ins().iadd(data, offset)
    }

    fn guard_array_store(&self, fb: &mut FunctionBuilder, value: Value, slow: Block) {
        #[cfg(not(feature = "gc"))]
        let _ = (fb, value, slow);
        #[cfg(feature = "gc")]
        {
            let store = fb.create_block();
            let nonnull = fb.ins().icmp_imm(IntCC::NotEqual, value, 0);
            let bits = fb.ins().band_imm(value, PTR_TAG_MASK);
            let aligned = fb.ins().icmp_imm(IntCC::Equal, bits, 0);
            let pointer = fb.ins().band(nonnull, aligned);
            fb.ins().brif(pointer, slow, &[], store, &[]);
            fb.switch_to_block(store);
        }
    }

    fn fill_array_range(
        &self,
        fb: &mut FunctionBuilder,
        data: Value,
        start: Value,
        end: Value,
        value: Value,
    ) {
        let head = fb.create_block();
        let body = fb.create_block();
        let done = fb.create_block();
        let index = fb.append_block_param(head, types::I64);
        fb.ins().jump(head, &[start.into()]);
        fb.switch_to_block(head);
        let more = fb.ins().icmp(IntCC::UnsignedLessThan, index, end);
        fb.ins().brif(more, body, &[], done, &[]);
        fb.switch_to_block(body);
        let slot = self.array_slot(fb, data, index);
        fb.ins().store(MemFlagsData::trusted(), value, slot, 0);
        let next = fb.ins().iadd_imm_s(index, 1);
        fb.ins().jump(head, &[next.into()]);
        fb.switch_to_block(done);
    }

    fn shift_array(&self, fb: &mut FunctionBuilder, data: Value, count: Value, right: bool) {
        let head = fb.create_block();
        let body = fb.create_block();
        let done = fb.create_block();
        let remaining = fb.append_block_param(head, types::I64);
        fb.ins().jump(head, &[count.into()]);
        fb.switch_to_block(head);
        let more = fb.ins().icmp_imm(IntCC::NotEqual, remaining, 0);
        fb.ins().brif(more, body, &[], done, &[]);
        fb.switch_to_block(body);
        let next = fb.ins().iadd_imm_s(remaining, -1);
        let (src, dst) = if right {
            (next, remaining)
        } else {
            let index = fb.ins().isub(count, remaining);
            (fb.ins().iadd_imm_s(index, 1), index)
        };
        let src = self.array_slot(fb, data, src);
        let dst = self.array_slot(fb, data, dst);
        let value = fb.ins().load(types::I64, MemFlagsData::trusted(), src, 0);
        fb.ins().store(MemFlagsData::trusted(), value, dst, 0);
        fb.ins().jump(head, &[next.into()]);
        fb.switch_to_block(done);
    }

    fn emit_string_intrinsic(
        &mut self,
        fb: &mut FunctionBuilder,
        name: &str,
        args: &[Value],
    ) -> Result<Value, String> {
        let ptr_ty = self.ptr_ty();
        let valid = fb.create_block();
        let invalid = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);
        self.tag_guard(fb, args[0], TAG_STRING, valid, invalid);
        fb.switch_to_block(invalid);
        let default = match name {
            "wir_string_len" => SMI_ZERO,
            "wir_string_index_of" | "wir_string_last_index_of" => -1,
            "wir_string_starts_with" | "wir_string_ends_with" => BOOL_FALSE,
            _ => 0,
        };
        let default = fb.ins().iconst(types::I64, default);
        fb.ins().jump(done, &[default.into()]);
        fb.switch_to_block(valid);
        let string = self.value_as_ptr(fb, args[0]);
        let len = fb
            .ins()
            .load(ptr_ty, MemFlagsData::trusted(), string, STR_LEN_OFFSET);
        let len = self.ptr_to_i64(fb, len);
        if name == "wir_string_len" {
            let tagged = Self::encode_smi(fb, len);
            fb.ins().jump(done, &[tagged.into()]);
            fb.switch_to_block(done);
            return Ok(result);
        }
        let data = fb
            .ins()
            .load(ptr_ty, MemFlagsData::trusted(), string, STR_DATA_OFFSET);
        let zero = fb.ins().iconst(types::I64, 0);
        let slow = fb.create_block();
        if matches!(name, "wir_string_slice" | "wir_string_substring") {
            let start = fb.ins().sshr_imm_s(args[1], 1);
            let end = fb.ins().sshr_imm_s(args[2], 1);
            let start = Self::string_index(fb, start, len, name == "wir_string_slice");
            let sentinel = fb.ins().icmp_imm(IntCC::Equal, end, -1);
            let end = Self::string_index(fb, end, len, name == "wir_string_slice");
            let end = fb.ins().select(sentinel, len, end);
            let (start, end) = if name == "wir_string_substring" {
                (fb.ins().umin(start, end), fb.ins().umax(start, end))
            } else {
                let empty = fb.ins().icmp(IntCC::UnsignedGreaterThanOrEqual, start, end);
                (
                    fb.ins().select(empty, zero, start),
                    fb.ins().select(empty, zero, end),
                )
            };
            self.string_boundary(fb, data, len, start, slow);
            self.string_boundary(fb, data, len, end, slow);
            let bytes = fb.ins().isub(end, start);
            let offset = self.value_as_ptr(fb, start);
            let substring = fb.ins().iadd(data, offset);
            let value = self.call_jit_intern_bytes(fb, substring, bytes)?;
            fb.ins().jump(done, &[value.into()]);
        } else {
            let search_valid = fb.create_block();
            self.tag_guard(fb, args[1], TAG_STRING, search_valid, invalid);
            fb.switch_to_block(search_valid);
            let search = self.value_as_ptr(fb, args[1]);
            let needle_len = fb
                .ins()
                .load(ptr_ty, MemFlagsData::trusted(), search, STR_LEN_OFFSET);
            let needle_len = self.ptr_to_i64(fb, needle_len);
            let needle = fb
                .ins()
                .load(ptr_ty, MemFlagsData::trusted(), search, STR_DATA_OFFSET);
            if matches!(name, "wir_string_starts_with" | "wir_string_ends_with") {
                let compare = fb.create_block();
                let fits = fb
                    .ins()
                    .icmp(IntCC::UnsignedLessThanOrEqual, needle_len, len);
                fb.ins().brif(fits, compare, &[], invalid, &[]);
                fb.switch_to_block(compare);
                let start = if name == "wir_string_ends_with" {
                    fb.ins().isub(len, needle_len)
                } else {
                    zero
                };
                let offset = self.value_as_ptr(fb, start);
                let haystack = fb.ins().iadd(data, offset);
                let count = self.value_as_ptr(fb, needle_len);
                let order = self.call_memcmp(fb, haystack, needle, count)?;
                let equal = fb.ins().icmp_imm(IntCC::Equal, order, 0);
                let tagged = Self::tagged_bool(fb, equal);
                fb.ins().jump(done, &[tagged.into()]);
            } else {
                let raw_pos = fb.ins().sshr_imm_s(args[2], 1);
                let backwards = name == "wir_string_last_index_of";
                let (start, end) = if backwards {
                    // Match the runtime's prefix-exclusive lastIndexOf semantics.
                    let negative = fb.ins().icmp_imm(IntCC::SignedLessThan, raw_pos, 0);
                    let last = fb.ins().iadd_imm_s(len, -1);
                    let last = fb.ins().smax(last, zero);
                    let pos = fb.ins().umin(raw_pos, last);
                    let end = fb.ins().iadd_imm_s(pos, 1);
                    (zero, fb.ins().select(negative, len, end))
                } else {
                    (Self::string_index(fb, raw_pos, len, false), len)
                };
                // Rust str slicing checks boundaries even before searching.
                self.string_boundary(fb, data, len, if backwards { end } else { start }, slow);
                let span = fb.ins().isub(end, start);
                // Keep Rust's optimized substring search for large inputs;
                // an inline candidate scan is intended for short strings.
                let short = fb.create_block();
                let bounded = fb.ins().icmp_imm(IntCC::UnsignedLessThanOrEqual, span, 64);
                fb.ins().brif(bounded, short, &[], slow, &[]);
                fb.switch_to_block(short);
                let compare = fb.create_block();
                let fits = fb
                    .ins()
                    .icmp(IntCC::UnsignedLessThanOrEqual, needle_len, span);
                fb.ins().brif(fits, compare, &[], invalid, &[]);
                fb.switch_to_block(compare);
                let last_start = fb.ins().isub(end, needle_len);
                let head = fb.create_block();
                let body = fb.create_block();
                let advance = fb.create_block();
                let found = fb.create_block();
                let index = fb.append_block_param(head, types::I64);
                fb.ins()
                    .jump(head, &[if backwards { last_start } else { start }.into()]);
                fb.switch_to_block(head);
                let remaining = if backwards {
                    fb.ins().icmp(IntCC::SignedGreaterThanOrEqual, index, start)
                } else {
                    fb.ins()
                        .icmp(IntCC::UnsignedLessThanOrEqual, index, last_start)
                };
                fb.ins().brif(remaining, body, &[], invalid, &[]);
                fb.switch_to_block(body);
                let offset = self.value_as_ptr(fb, index);
                let haystack = fb.ins().iadd(data, offset);
                let count = self.value_as_ptr(fb, needle_len);
                let order = self.call_memcmp(fb, haystack, needle, count)?;
                let equal = fb.ins().icmp_imm(IntCC::Equal, order, 0);
                fb.ins().brif(equal, found, &[], advance, &[]);
                fb.switch_to_block(found);
                let tagged = Self::encode_smi(fb, index);
                fb.ins().jump(done, &[tagged.into()]);
                fb.switch_to_block(advance);
                let next = fb.ins().iadd_imm_s(index, if backwards { -1 } else { 1 });
                fb.ins().jump(head, &[next.into()]);
            }
        }
        if matches!(
            name,
            "wir_string_slice"
                | "wir_string_substring"
                | "wir_string_index_of"
                | "wir_string_last_index_of"
        ) {
            fb.switch_to_block(slow);
            let value = self.intrinsic_host(fb, name, args)?;
            fb.ins().jump(done, &[value.into()]);
        }
        fb.switch_to_block(done);
        Ok(result)
    }

    fn string_index(fb: &mut FunctionBuilder, index: Value, len: Value, relative: bool) -> Value {
        let zero = fb.ins().iconst(types::I64, 0);
        let index = if relative {
            let negative = fb.ins().icmp_imm(IntCC::SignedLessThan, index, 0);
            let from_end = fb.ins().iadd(len, index);
            fb.ins().select(negative, from_end, index)
        } else {
            index
        };
        let clamped = fb.ins().smax(index, zero);
        fb.ins().umin(clamped, len)
    }

    fn string_boundary(
        &self,
        fb: &mut FunctionBuilder,
        data: Value,
        len: Value,
        index: Value,
        slow: Block,
    ) {
        let byte = fb.create_block();
        let valid = fb.create_block();
        let at_end = fb.ins().icmp(IntCC::Equal, index, len);
        fb.ins().brif(at_end, valid, &[], byte, &[]);
        fb.switch_to_block(byte);
        let inbounds = fb.ins().icmp(IntCC::UnsignedLessThan, index, len);
        let load = fb.create_block();
        fb.ins().brif(inbounds, load, &[], slow, &[]);
        fb.switch_to_block(load);
        let offset = self.value_as_ptr(fb, index);
        let ptr = fb.ins().iadd(data, offset);
        let byte = fb.ins().load(types::I8, MemFlagsData::trusted(), ptr, 0);
        let bits = fb.ins().band_imm(byte, 0xC0);
        let boundary = fb.ins().icmp_imm(IntCC::NotEqual, bits, 0x80);
        fb.ins().brif(boundary, valid, &[], slow, &[]);
        fb.switch_to_block(valid);
    }

    fn emit_string_transform(
        &mut self,
        fb: &mut FunctionBuilder,
        name: &str,
        input: Value,
    ) -> Result<Value, String> {
        let valid = fb.create_block();
        let invalid = fb.create_block();
        let slow = fb.create_block();
        let done = fb.create_block();
        let result = fb.append_block_param(done, types::I64);
        self.tag_guard(fb, input, TAG_STRING, valid, invalid);
        fb.switch_to_block(invalid);
        let zero = fb.ins().iconst(types::I64, 0);
        fb.ins().jump(done, &[zero.into()]);
        fb.switch_to_block(valid);
        let ptr_ty = self.ptr_ty();
        let string = self.value_as_ptr(fb, input);
        let data = fb
            .ins()
            .load(ptr_ty, MemFlagsData::trusted(), string, STR_DATA_OFFSET);
        let len = fb
            .ins()
            .load(ptr_ty, MemFlagsData::trusted(), string, STR_LEN_OFFSET);
        let len = self.ptr_to_i64(fb, len);
        let zero = fb.ins().iconst(types::I64, 0);
        if matches!(
            name,
            "wir_string_trim" | "wir_string_trim_start" | "wir_string_trim_end"
        ) {
            let start = if name == "wir_string_trim_end" {
                zero
            } else {
                self.trim_ascii(fb, data, zero, len, false, slow)
            };
            let end = if name == "wir_string_trim_start" {
                len
            } else {
                self.trim_ascii(fb, data, start, len, true, slow)
            };
            let size = fb.ins().isub(end, start);
            let unchanged = fb.ins().icmp(IntCC::Equal, size, len);
            let allocate = fb.create_block();
            fb.ins()
                .brif(unchanged, done, &[input.into()], allocate, &[]);
            fb.switch_to_block(allocate);
            let offset = self.value_as_ptr(fb, start);
            let substring = fb.ins().iadd(data, offset);
            let value = self.call_jit_intern_bytes(fb, substring, size)?;
            fb.ins().jump(done, &[value.into()]);
        } else {
            let short = fb.create_block();
            let fits = fb.ins().icmp_imm(IntCC::UnsignedLessThanOrEqual, len, 64);
            fb.ins().brif(fits, short, &[], slow, &[]);
            fb.switch_to_block(short);
            let buffer =
                fb.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 64, 0));
            let buffer = fb.ins().stack_addr(ptr_ty, buffer, 0);
            let head = fb.create_block();
            let body = fb.create_block();
            let ascii = fb.create_block();
            let finish = fb.create_block();
            let index = fb.append_block_param(head, types::I64);
            fb.ins().jump(head, &[zero.into()]);
            fb.switch_to_block(head);
            let more = fb.ins().icmp(IntCC::UnsignedLessThan, index, len);
            fb.ins().brif(more, body, &[], finish, &[]);
            fb.switch_to_block(body);
            let offset = self.value_as_ptr(fb, index);
            let source = fb.ins().iadd(data, offset);
            let byte = fb.ins().load(types::I8, MemFlagsData::trusted(), source, 0);
            let is_ascii = fb.ins().icmp_imm(IntCC::UnsignedLessThan, byte, 128);
            fb.ins().brif(is_ascii, ascii, &[], slow, &[]);
            fb.switch_to_block(ascii);
            let uppercase = name == "wir_string_to_upper_case";
            let lower = fb.ins().icmp_imm(
                IntCC::UnsignedGreaterThanOrEqual,
                byte,
                if uppercase { b'a' } else { b'A' } as i64,
            );
            let upper = fb.ins().icmp_imm(
                IntCC::UnsignedLessThanOrEqual,
                byte,
                if uppercase { b'z' } else { b'Z' } as i64,
            );
            let letter = fb.ins().band(lower, upper);
            let changed = fb.ins().iadd_imm_s(byte, if uppercase { -32 } else { 32 });
            let converted = fb.ins().select(letter, changed, byte);
            let destination = fb.ins().iadd(buffer, offset);
            fb.ins()
                .store(MemFlagsData::trusted(), converted, destination, 0);
            let next = fb.ins().iadd_imm_s(index, 1);
            fb.ins().jump(head, &[next.into()]);
            fb.switch_to_block(finish);
            let value = self.call_jit_intern_bytes(fb, buffer, len)?;
            fb.ins().jump(done, &[value.into()]);
        }
        fb.switch_to_block(slow);
        let value = self.intrinsic_host(fb, name, &[input])?;
        fb.ins().jump(done, &[value.into()]);
        fb.switch_to_block(done);
        Ok(result)
    }

    fn trim_ascii(
        &self,
        fb: &mut FunctionBuilder,
        data: Value,
        start: Value,
        end: Value,
        backwards: bool,
        slow: Block,
    ) -> Value {
        let head = fb.create_block();
        let body = fb.create_block();
        let ascii = fb.create_block();
        let advance = fb.create_block();
        let done = fb.create_block();
        let index = fb.append_block_param(head, types::I64);
        let result = fb.append_block_param(done, types::I64);
        fb.ins()
            .jump(head, &[if backwards { end } else { start }.into()]);
        fb.switch_to_block(head);
        let more = if backwards {
            fb.ins().icmp(IntCC::UnsignedGreaterThan, index, start)
        } else {
            fb.ins().icmp(IntCC::UnsignedLessThan, index, end)
        };
        fb.ins().brif(more, body, &[], done, &[index.into()]);
        fb.switch_to_block(body);
        let byte_index = if backwards {
            fb.ins().iadd_imm_s(index, -1)
        } else {
            index
        };
        let offset = self.value_as_ptr(fb, byte_index);
        let source = fb.ins().iadd(data, offset);
        let byte = fb.ins().load(types::I8, MemFlagsData::trusted(), source, 0);
        let is_ascii = fb.ins().icmp_imm(IntCC::UnsignedLessThan, byte, 128);
        fb.ins().brif(is_ascii, ascii, &[], slow, &[]);
        fb.switch_to_block(ascii);
        let space = fb.ins().icmp_imm(IntCC::Equal, byte, 32);
        let lower = fb
            .ins()
            .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, byte, 9);
        let upper = fb.ins().icmp_imm(IntCC::UnsignedLessThanOrEqual, byte, 13);
        let control = fb.ins().band(lower, upper);
        let whitespace = fb.ins().bor(space, control);
        fb.ins()
            .brif(whitespace, advance, &[], done, &[index.into()]);
        fb.switch_to_block(advance);
        let next = fb.ins().iadd_imm_s(index, if backwards { -1 } else { 1 });
        fb.ins().jump(head, &[next.into()]);
        fb.switch_to_block(done);
        result
    }
}

#[cfg(all(test, not(feature = "gc")))]
mod tests {
    use super::*;
    use crate::{runtime, value};

    struct Compiled {
        _jit: JIT,
        function: JitFnPtr,
        ir: String,
    }

    impl Compiled {
        fn new(name: &str, arity: usize) -> Self {
            let mut jit = JIT::default();
            let ptr_ty = jit.ptr_ty();
            let mut ctx = jit.module.make_context();
            ctx.func.signature.params.push(AbiParam::new(ptr_ty));
            ctx.func.signature.params.push(AbiParam::new(ptr_ty));
            ctx.func.signature.returns.push(AbiParam::new(types::I64));
            let mut fctx = FunctionBuilderContext::new();
            {
                let mut fb = FunctionBuilder::new(&mut ctx.func, &mut fctx);
                let entry = fb.create_block();
                fb.append_block_params_for_function_params(entry);
                fb.switch_to_block(entry);
                let argv = fb.block_params(entry)[0];
                let args: Vec<_> = (0..arity)
                    .map(|i| {
                        fb.ins()
                            .load(types::I64, MemFlagsData::trusted(), argv, (i * 8) as i32)
                    })
                    .collect();
                let result = jit
                    .call_import(
                        &mut fb,
                        name,
                        |sig| {
                            sig.params
                                .extend((0..arity).map(|_| AbiParam::new(types::I64)));
                            sig.returns.push(AbiParam::new(types::I64));
                        },
                        &args,
                    )
                    .expect("emit intrinsic");
                fb.ins().return_(&[result]);
                fb.seal_all_blocks();
                fb.finalize(jit.module.isa().frontend_config());
            }
            let ir = ctx.func.display().to_string();
            let id = jit
                .module
                .declare_function("test_intrinsic", Linkage::Local, &ctx.func.signature)
                .unwrap();
            jit.module
                .define_function(id, &mut ctx)
                .expect("verify and compile intrinsic");
            jit.module.finalize_definitions().unwrap();
            let function = unsafe { mem::transmute(jit.module.get_finalized_function(id)) };
            Self {
                _jit: jit,
                function,
                ir,
            }
        }

        fn call(&self, args: &[i64]) -> i64 {
            unsafe { (self.function)(args.as_ptr(), args.len()) }
        }
    }

    #[test]
    fn wir_array_instructions_use_the_shared_layout_and_tagged_results() {
        use crate::wir::{Builder, Module, Type};
        for operation in ["length", "get", "set"] {
            let mut module = Module::new();
            let mut builder =
                Builder::new(&mut module, operation, vec![Type::Top; 3], vec![Type::Top]);
            let arr = builder.param(0);
            let idx = builder.param(1);
            let val = builder.param(2);
            let result = match operation {
                "length" => builder.array_len(arr),
                "get" => builder.load_elem(arr, idx, None),
                "set" => {
                    builder
                        .push_node(Inst::StoreElem { arr, idx, val }, None, 1, true)
                        .1[0]
                }
                _ => unreachable!(),
            };
            builder.ret(&[result]);
            let function = builder.finish();
            let mut jit = JIT::default();
            jit.compile(&function).unwrap();
            let pointers = jit.finalize_and_get_pointers().unwrap();
            let compiled = pointers[&function.id.0];
            for len in [0, 3, 8] {
                let actual = value::array_new(len);
                let expected = value::array_new(len);
                for index in [-1, 0, 2, 12] {
                    let input = value::obj_new();
                    let args = [actual, value::make_smi(index), input];
                    let result = unsafe { compiled(args.as_ptr(), args.len()) };
                    let expected_result = match operation {
                        "length" => value::wir_array_len(expected),
                        "get" => value::wir_array_get(expected, args[1]),
                        "set" => value::wir_array_set(expected, args[1], input),
                        _ => unreachable!(),
                    };
                    assert_eq!(result, expected_result, "{operation}({len}, {index})");
                    assert_eq!(array_contents(actual), array_contents(expected));
                }
            }
            for input in [
                0,
                BOOL_FALSE,
                BOOL_TRUE,
                value::make_smi(1),
                value::intern_string("not an array"),
            ] {
                let args = [input, value::make_smi(0), 0];
                assert_eq!(
                    unsafe { compiled(args.as_ptr(), args.len()) },
                    if operation == "length" { SMI_ZERO } else { 0 }
                );
            }
        }
    }

    #[test]
    fn module_binding_ids_do_not_alias_and_values_are_gc_roots() {
        let first = value::obj_new();
        let second = value::obj_new();
        wir_binding_store(1_000_000, first);
        wir_binding_store(2_000_001, second);
        assert_eq!(wir_binding_load(1_000_000), first);
        assert_eq!(wir_binding_load(2_000_001), second);
        let mut roots = Vec::new();
        bindings_with_root_slots(|slot| roots.push(unsafe { *slot }));
        assert!(roots.contains(&first));
        assert!(roots.contains(&second));
        wir_binding_store(1_000_000, 0);
        wir_binding_store(2_000_001, 0);
    }

    #[test]
    fn object_predicate_is_compiled_without_host_calls() {
        let compiled = Compiled::new("wir_is_obj", 1);
        assert!(!compiled.ir.contains(" = call "));
        let object = value::obj_new();
        assert_eq!(compiled.call(&[object]), BOOL_TRUE);
        for value in [
            0,
            BOOL_FALSE,
            BOOL_TRUE,
            value::make_smi(1),
            value::intern_string("x"),
            value::array_new(0),
            value::map_new(),
            value::proxy_new(object, value::obj_new()),
        ] {
            assert_eq!(compiled.call(&[value]), BOOL_FALSE);
        }
    }

    #[test]
    fn predicates_match_runtime_without_host_calls() {
        let object = value::obj_new();
        let proxy = value::proxy_new(object, value::obj_new());
        let inputs = [
            0,
            value::make_smi(0),
            value::make_smi(-1),
            BOOL_TRUE,
            BOOL_FALSE,
            value::intern_string("test"),
            value::array_new(0),
            object,
            value::map_new(),
            value::set_new(),
            proxy,
            value::box_f64(1.25),
        ];
        for (name, runtime) in [
            (
                "wir_is_str",
                runtime::wir_is_str as unsafe extern "C" fn(i64) -> i64,
            ),
            ("wir_is_map", runtime::wir_is_map),
            ("wir_is_set", runtime::wir_is_set),
            ("wir_is_proxy", runtime::wir_is_proxy),
            ("wir_is_nullish", runtime::wir_is_nullish),
        ] {
            let compiled = Compiled::new(name, 1);
            assert!(!compiled.ir.contains(" = call "), "{name}: {}", compiled.ir);
            for input in inputs {
                assert_eq!(
                    compiled.call(&[input]),
                    unsafe { runtime(input) },
                    "{name}({input})"
                );
            }
        }
    }

    #[test]
    fn type_guard_predicates_are_compiled_without_host_calls() {
        let object = value::obj_new();
        let array = value::array_new(0);
        let string = value::intern_string("test");
        let boxed = value::box_f64(1.25);
        let inputs = [
            0,
            value::make_smi(0),
            value::make_smi(-7),
            BOOL_TRUE,
            BOOL_FALSE,
            string,
            array,
            object,
            value::map_new(),
            value::set_new(),
            boxed,
        ];
        for (name, accepts) in [
            ("wir_is_null", &[0][..]),
            ("wir_is_bool", &[BOOL_TRUE, BOOL_FALSE][..]),
            ("wir_is_number", &[value::make_smi(0), value::make_smi(-7), boxed][..]),
            ("wir_is_array", &[array][..]),
            ("wir_is_closure", &[][..]),
        ] {
            let compiled = Compiled::new(name, 1);
            assert!(!compiled.ir.contains(" = call "), "{name}: {}", compiled.ir);
            for input in inputs {
                let expected = if accepts.contains(&input) { BOOL_TRUE } else { BOOL_FALSE };
                assert_eq!(compiled.call(&[input]), expected, "{name}({input})");
            }
        }
    }

    #[test]
    fn array_reads_and_vec_layout_match_runtime() {
        let len = Compiled::new("wir_array_len", 1);
        let get = Compiled::new("wir_array_get", 2);
        assert!(!len.ir.contains(" = call "));
        assert!(!get.ir.contains(" = call "));
        for capacity in [0, 1, 4, 19] {
            for size in 0..=capacity {
                let mut buf = Vec::with_capacity(capacity);
                buf.extend((0..size).map(|i| value::make_smi(i as i64 + 100)));
                let array = value::array_from_vec(buf);
                assert_eq!(len.call(&[array]), value::wir_array_len(array));
                for index in [-100, -1, 0, 1, 3, 18, 19, i32::MAX as i64] {
                    let index = value::make_smi(index);
                    assert_eq!(
                        get.call(&[array, index]),
                        value::wir_array_get(array, index)
                    );
                }
            }
        }
        assert_eq!(len.call(&[0]), value::make_smi(0));
        assert_eq!(get.call(&[0, value::make_smi(0)]), 0);
    }

    fn array_contents(array: i64) -> Vec<i64> {
        unsafe { (&*(array as *const BoxedArray)).buf.clone() }
    }

    #[test]
    fn array_mutations_match_runtime_including_capacity_changes() {
        let mutations: [(&str, unsafe extern "C" fn(i64, i64) -> i64); 4] = [
            ("wir_array_push", value::wir_array_push),
            ("wir_array_unshift", value::wir_array_unshift),
            ("wir_array_set_len", value::wir_array_set_len),
            ("wir_array_fill", value::wir_array_fill),
        ];
        let pointer_value = value::intern_string("kept alive");
        for (name, runtime) in mutations {
            let compiled = Compiled::new(name, 2);
            for capacity in [0, 3, 20] {
                for input in [
                    value::make_smi(-1),
                    value::make_smi(0),
                    value::make_smi(2),
                    value::make_smi(30),
                    BOOL_FALSE,
                    0,
                ] {
                    let initial: Vec<_> = (0..capacity.min(3)).map(value::make_smi).collect();
                    let mut native = Vec::with_capacity(capacity as usize);
                    native.extend_from_slice(&initial);
                    let expected = value::array_from_vec(native.clone());
                    let actual = value::array_from_vec(native);
                    let result = unsafe { runtime(expected, input) };
                    assert_eq!(compiled.call(&[actual, input]), result, "{name}");
                    assert_eq!(array_contents(actual), array_contents(expected), "{name}");
                }
            }
            if name != "wir_array_set_len" {
                let actual = value::array_from_vec(vec![0, 0]);
                let expected = value::array_from_vec(vec![0, 0]);
                assert_eq!(compiled.call(&[actual, pointer_value]), unsafe {
                    runtime(expected, pointer_value)
                });
                assert_eq!(array_contents(actual), array_contents(expected));
            }
        }
        let set = Compiled::new("wir_array_set", 3);
        let pop = Compiled::new("wir_array_pop", 1);
        let shift = Compiled::new("wir_array_shift", 1);
        assert!(!pop.ir.contains(" = call "));
        assert!(!shift.ir.contains(" = call "));
        let actual = value::array_from_vec(vec![1, 3, 5]);
        let expected = value::array_from_vec(vec![1, 3, 5]);
        for index in [-1, 0, 2, 10] {
            let index = value::make_smi(index);
            assert_eq!(
                set.call(&[actual, index, pointer_value]),
                value::wir_array_set(expected, index, pointer_value)
            );
            assert_eq!(array_contents(actual), array_contents(expected));
        }
        for _ in 0..15 {
            assert_eq!(pop.call(&[actual]), value::wir_array_pop(expected));
            assert_eq!(shift.call(&[actual]), value::wir_array_shift(expected));
            assert_eq!(array_contents(actual), array_contents(expected));
        }
    }

    #[test]
    fn string_predicates_match_runtime_for_utf8_and_empty_inputs() {
        for (name, runtime) in [
            (
                "wir_string_starts_with",
                value::wir_string_starts_with as unsafe extern "C" fn(i64, i64) -> i64,
            ),
            ("wir_string_ends_with", value::wir_string_ends_with),
        ] {
            let compiled = Compiled::new(name, 2);
            for text in ["", "a", "napalm", "abababab", "\u{e9}\u{4e16}\u{754c}"] {
                let text = value::intern_string(text);
                for needle in ["", "n", "napalm", "napalm!", "ab", "\u{e9}", "\u{754c}"] {
                    let needle = value::intern_string(needle);
                    assert_eq!(compiled.call(&[text, needle]), unsafe {
                        runtime(text, needle)
                    });
                }
            }
            for invalid in [0, BOOL_TRUE, value::make_smi(12), value::array_new(0)] {
                let text = value::intern_string("test");
                assert_eq!(compiled.call(&[invalid, text]), BOOL_FALSE);
                assert_eq!(compiled.call(&[text, invalid]), BOOL_FALSE);
            }
        }
        let len = Compiled::new("wir_string_len", 1);
        assert!(!len.ir.contains(" = call "));
        for text in ["", "napalm", "\u{e9}\u{4e16}\u{754c}"] {
            let text = value::intern_string(text);
            assert_eq!(len.call(&[text]), unsafe { value::wir_string_len(text) });
        }
    }

    #[test]
    fn string_slicing_matches_runtime_at_every_valid_boundary() {
        for (name, runtime) in [
            (
                "wir_string_slice",
                value::wir_string_slice as unsafe extern "C" fn(i64, i64, i64) -> i64,
            ),
            ("wir_string_substring", value::wir_string_substring),
        ] {
            let compiled = Compiled::new(name, 3);
            for text in ["", "abcdef", "\u{e9}\u{4e16}\u{754c}"] {
                let boxed = value::intern_string(text);
                for start in -12..12 {
                    for end in -12..12 {
                        let len = text.len() as i64;
                        let clamp = |i: i64| {
                            if name == "wir_string_slice" && i < 0 {
                                (len + i).max(0).min(len)
                            } else {
                                i.max(0).min(len)
                            }
                        };
                        let s = clamp(start) as usize;
                        let e = if end == -1 {
                            len as usize
                        } else {
                            clamp(end) as usize
                        };
                        if (name == "wir_string_slice" && s >= e)
                            || (text.is_char_boundary(s) && text.is_char_boundary(e))
                        {
                            let args = [boxed, value::make_smi(start), value::make_smi(end)];
                            let expected = unsafe { runtime(args[0], args[1], args[2]) };
                            let actual = compiled.call(&args);
                            assert_eq!(
                                runtime::fmt_value(actual),
                                runtime::fmt_value(expected),
                                "{name}({text:?}, {start}, {end})"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn string_search_matches_runtime_positions_and_sentinels() {
        for (name, runtime) in [
            (
                "wir_string_index_of",
                value::wir_string_index_of as unsafe extern "C" fn(i64, i64, i64) -> i64,
            ),
            ("wir_string_last_index_of", value::wir_string_last_index_of),
        ] {
            let compiled = Compiled::new(name, 3);
            for text in [
                "",
                "a",
                "abababa",
                "napalm-runtime",
                "\u{e9}\u{4e16}\u{754c}\u{e9}",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaba",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaba",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaabab",
            ] {
                for needle in ["", "a", "aba", "runtime", "missing", "\u{e9}", "\u{754c}"] {
                    for pos in -3..20 {
                        let boundary = if name == "wir_string_index_of" {
                            (pos.max(0) as usize).min(text.len())
                        } else if pos < 0 {
                            text.len()
                        } else {
                            (pos as usize).min(text.len().saturating_sub(1)) + 1
                        };
                        if boundary > text.len() || !text.is_char_boundary(boundary) {
                            continue;
                        }
                        let args = [
                            value::intern_string(text),
                            value::intern_string(needle),
                            value::make_smi(pos),
                        ];
                        assert_eq!(
                            compiled.call(&args),
                            unsafe { runtime(args[0], args[1], args[2]) },
                            "{name}({text:?}, {needle:?}, {pos})"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn string_transforms_match_ascii_and_unicode_runtime_behavior() {
        for (name, runtime) in [
            (
                "wir_string_trim",
                value::wir_string_trim as unsafe extern "C" fn(i64) -> i64,
            ),
            ("wir_string_trim_start", value::wir_string_trim_start),
            ("wir_string_trim_end", value::wir_string_trim_end),
            ("wir_string_to_upper_case", value::wir_string_to_upper_case),
            ("wir_string_to_lower_case", value::wir_string_to_lower_case),
        ] {
            let compiled = Compiled::new(name, 1);
            for text in [
                "",
                " ",
                "\t\n\r\u{b}\u{c}",
                " ABC abc 123! ",
                "aZzA[]",
                "\u{a0}\u{e9}\u{2003}",
                " stra\u{df}e ",
                "\u{130}",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaA",
                "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaA",
            ] {
                let boxed = value::intern_string(text);
                let expected = unsafe { runtime(boxed) };
                assert_eq!(
                    runtime::fmt_value(compiled.call(&[boxed])),
                    runtime::fmt_value(expected),
                    "{name}({text:?})"
                );
            }
            for invalid in [
                0,
                BOOL_FALSE,
                BOOL_TRUE,
                value::make_smi(1),
                value::array_new(0),
            ] {
                assert_eq!(compiled.call(&[invalid]), 0, "{name}");
            }
        }
    }
}
