use super::*;
use cranelift::codegen::ir::{Block, StackSlot};

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(i64)]
pub(super) enum CompletionKind {
    Return = 1,
    Throw = 2,
}

struct RegionSlots {
    locals: StackSlot,
    completion: StackSlot,
}

pub(super) struct ExceptionFlow {
    state: Value,
    regions: Vec<RegionSlots>,
    async_completion: Option<(StackSlot, Block, Block)>,
}

impl ExceptionFlow {
    pub(super) fn new(fb: &mut FunctionBuilder, fun: &WirFunction, state: Value) -> Self {
        let regions = fun
            .try_regions
            .iter()
            .map(|region| {
                let count = fun
                    .nodes
                    .iter()
                    .filter_map(|node| match &node.kind {
                        Inst::TryLeave {
                            region: id, locals, ..
                        } if *id == region.id => Some(locals.len()),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(0);
                RegionSlots {
                    locals: fb.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        (count.max(1) * 8) as u32,
                        3,
                    )),
                    completion: fb.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        16,
                        3,
                    )),
                }
            })
            .collect();
        let async_completion = fun.is_async.then(|| {
            let slot =
                fb.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 3));
            let resolve = fb.create_block();
            let reject = fb.create_block();
            fb.append_block_param(resolve, types::I64);
            fb.append_block_param(reject, types::I64);
            (slot, resolve, reject)
        });
        Self {
            state,
            regions,
            async_completion,
        }
    }

    pub(super) fn snapshot(&self, fb: &mut FunctionBuilder, region: TryRegionId, values: &[Value]) {
        for (index, value) in values.iter().enumerate() {
            fb.ins().stack_store(
                types::I64,
                *value,
                self.regions[region.0 as usize].locals,
                (index * 8) as i32,
            );
        }
    }

    pub(super) fn enter_finally(&self, fb: &mut FunctionBuilder, region: TryRegionId) {
        let zero = fb.ins().iconst(types::I64, 0);
        fb.ins().stack_store(
            types::I64,
            zero,
            self.regions[region.0 as usize].completion,
            0,
        );
        fb.ins().stack_store(
            types::I64,
            zero,
            self.regions[region.0 as usize].completion,
            8,
        );
    }

    fn args(&self, fb: &mut FunctionBuilder, region: TryRegionId, count: usize) -> Vec<BlockArg> {
        (0..count)
            .map(|index| {
                fb.ins()
                    .stack_load(
                        types::I64,
                        types::I64,
                        self.regions[region.0 as usize].locals,
                        (index * 8) as i32,
                    )
                    .into()
            })
            .collect()
    }

    pub(super) fn complete(
        &self,
        fb: &mut FunctionBuilder,
        fun: &WirFunction,
        blocks: &[Block],
        source: BlockId,
        kind: CompletionKind,
        value: Value,
    ) {
        for region in fun.try_regions.iter().rev() {
            let in_body = region.body_blocks.contains(&source);
            if !in_body && !region.catch_blocks.contains(&source) {
                continue;
            }
            if kind == CompletionKind::Throw && in_body {
                if let Some(handler) = region.catches.first() {
                    let target = blocks[handler.handler.0 as usize];
                    let mut args = Vec::new();
                    if handler.binds_exception {
                        args.push(value.into());
                    }
                    args.extend(self.args(
                        fb,
                        region.id,
                        fb.block_params(target).len() - args.len(),
                    ));
                    let zero = fb.ins().iconst(types::I64, 0);
                    fb.ins().store(MemFlagsData::trusted(), zero, self.state, 0);
                    fb.ins().jump(target, &args);
                    return;
                }
            }
            if let Some(finally) = region.finally_entry {
                let slot = self.regions[region.id.0 as usize].completion;
                let kind_value = fb.ins().iconst(types::I64, kind as i64);
                fb.ins().stack_store(types::I64, kind_value, slot, 0);
                fb.ins().stack_store(types::I64, value, slot, 8);
                let zero = fb.ins().iconst(types::I64, 0);
                fb.ins().store(MemFlagsData::trusted(), zero, self.state, 0);
                let target = blocks[finally.0 as usize];
                let args = self.args(fb, region.id, fb.block_params(target).len());
                fb.ins().jump(target, &args);
                return;
            }
        }
        if let Some((_, resolve, reject)) = self.async_completion {
            let zero = fb.ins().iconst(types::I64, 0);
            fb.ins().store(MemFlagsData::trusted(), zero, self.state, 0);
            fb.ins().jump(
                if kind == CompletionKind::Throw {
                    reject
                } else {
                    resolve
                },
                &[value.into()],
            );
        } else if kind == CompletionKind::Throw {
            let pending = fb.ins().iconst(types::I64, 1);
            fb.ins()
                .store(MemFlagsData::trusted(), value, self.state, 8);
            fb.ins()
                .store(MemFlagsData::trusted(), pending, self.state, 0);
            let zero = fb.ins().iconst(types::I64, 0);
            fb.ins().return_(&[zero]);
        } else {
            fb.ins().return_(&[value]);
        }
    }

    pub(super) fn save_deferred(&self, fb: &mut FunctionBuilder, deferred: Value) {
        if let Some((slot, _, _)) = self.async_completion {
            fb.ins().stack_store(types::I64, deferred, slot, 0);
        }
    }

    pub(super) fn finish(&self, jit: &mut JIT, fb: &mut FunctionBuilder) -> Result<(), String> {
        if let Some((slot, resolve, reject)) = self.async_completion {
            for (block, name) in [
                (resolve, "wir_deferred_resolve"),
                (reject, "wir_deferred_reject"),
            ] {
                fb.switch_to_block(block);
                let value = fb.block_params(block)[0];
                let deferred = fb.ins().stack_load(types::I64, types::I64, slot, 0);
                jit.call_import(
                    fb,
                    name,
                    |s| {
                        s.params.push(AbiParam::new(types::I64));
                        s.params.push(AbiParam::new(types::I64));
                        s.returns.push(AbiParam::new(types::I64));
                    },
                    &[deferred, value],
                )?;
                fb.ins().return_(&[deferred]);
            }
        }
        Ok(())
    }

    pub(super) fn check(
        &self,
        fb: &mut FunctionBuilder,
        fun: &WirFunction,
        blocks: &[Block],
        source: BlockId,
    ) {
        let pending = fb
            .ins()
            .load(types::I64, MemFlagsData::trusted(), self.state, 0);
        let failed = fb.ins().icmp_imm(IntCC::NotEqual, pending, 0);
        let exceptional = fb.create_block();
        let normal = fb.create_block();
        fb.ins().brif(failed, exceptional, &[], normal, &[]);
        fb.switch_to_block(exceptional);
        let error = fb
            .ins()
            .load(types::I64, MemFlagsData::trusted(), self.state, 8);
        self.complete(fb, fun, blocks, source, CompletionKind::Throw, error);
        fb.switch_to_block(normal);
    }

    pub(super) fn exit_finally(
        &self,
        fb: &mut FunctionBuilder,
        fun: &WirFunction,
        blocks: &[Block],
        region: TryRegionId,
    ) {
        let slot = self.regions[region.0 as usize].completion;
        let kind = fb.ins().stack_load(types::I64, types::I64, slot, 0);
        let value = fb.ins().stack_load(types::I64, types::I64, slot, 8);
        let normal = fb.create_block();
        let abrupt = fb.create_block();
        let is_normal = fb.ins().icmp_imm(IntCC::Equal, kind, 0);
        fb.ins().brif(is_normal, normal, &[], abrupt, &[]);
        fb.switch_to_block(abrupt);
        let returning = fb.create_block();
        let throwing = fb.create_block();
        let is_return = fb
            .ins()
            .icmp_imm(IntCC::Equal, kind, CompletionKind::Return as i64);
        fb.ins().brif(is_return, returning, &[], throwing, &[]);
        let source = fun.try_regions[region.0 as usize]
            .finally_entry
            .expect("finally entry");
        fb.switch_to_block(returning);
        self.complete(fb, fun, blocks, source, CompletionKind::Return, value);
        fb.switch_to_block(throwing);
        self.complete(fb, fun, blocks, source, CompletionKind::Throw, value);
        fb.switch_to_block(normal);
    }
}
