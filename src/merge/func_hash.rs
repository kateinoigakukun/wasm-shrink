use std::hash::{Hash, Hasher};
use walrus::ir::*;
use walrus::{
    ir::{InstrSeq, InstrSeqId, Visitor},
    InstrLocId, LocalFunction, Module,
};

pub(crate) fn run<H: Hasher>(func: &LocalFunction, module: &Module, hasher: &mut H) {
    let v = &mut Emit {
        blocks: vec![],
        block_kinds: vec![BlockKind::FunctionEntry],
        hasher,
        module,
    };
    dfs_in_order(v, func, func.entry_block());

    debug_assert!(v.blocks.is_empty());
    debug_assert!(v.block_kinds.is_empty());
}

/// Different kinds of blocks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BlockKind {
    /// A `block` block.
    Block,

    /// A `loop` block.
    Loop,

    /// An `if` block
    If,

    /// An `Else` block
    Else,

    /// The entry to a function.
    FunctionEntry,
}

struct Emit<'a, 'b, H: Hasher> {
    // Stack of blocks that we are currently emitting instructions for. A branch
    // is only valid if its target is one of these blocks. See also the
    // `branch_target` method.
    blocks: Vec<InstrSeqId>,

    // The kinds of blocks we have on the stack. This is parallel to `blocks`
    // 99% of the time, except we push a new block kind in `visit_instr`, before
    // we push the block in `start_instr_seq`, because this is when we know the
    // kind.
    block_kinds: Vec<BlockKind>,

    // The instruction sequence we are building up to emit.
    hasher: &'a mut H,

    module: &'b Module,
}

impl<'instr, H: Hasher> Visitor<'instr> for Emit<'_, '_, H> {
    fn start_instr_seq(&mut self, seq: &'instr InstrSeq) {
        self.blocks.push(seq.id());
        debug_assert_eq!(self.blocks.len(), self.block_kinds.len());

        match self.block_kinds.last().unwrap() {
            BlockKind::Block => {
                self.hasher.write_u8(0x02); // block
                self.block_type(seq.ty);
            }
            BlockKind::Loop => {
                self.hasher.write_u8(0x03); // loop
                self.block_type(seq.ty);
            }
            BlockKind::If => {
                self.hasher.write_u8(0x04); // if
                self.block_type(seq.ty);
            }
            // Function entries are implicitly started, and don't need any
            // opcode to start them. `Else` blocks are started when `If` blocks
            // end in an `else` opcode, which we handle in `end_instr_seq`
            // below.
            BlockKind::FunctionEntry | BlockKind::Else => {}
        }
    }

    fn end_instr_seq(&mut self, seq: &'instr InstrSeq) {
        let popped_block = self.blocks.pop();
        debug_assert_eq!(popped_block, Some(seq.id()));

        let popped_kind = self.block_kinds.pop();
        debug_assert!(popped_kind.is_some());

        debug_assert_eq!(self.blocks.len(), self.block_kinds.len());

        if let BlockKind::If = popped_kind.unwrap() {
            // We're about to visit the `else` block, so push its kind.
            //
            // TODO: don't emit `else` for empty else blocks
            self.block_kinds.push(BlockKind::Else);
            self.hasher.write_u8(0x05); // else
        } else {
            self.hasher.write_u8(0x0b); // end
        }
    }

    fn visit_instr(&mut self, instr: &'instr Instr, _: &'instr InstrLocId) {
        use self::Instr::*;

        match instr {
            Block(_) => self.block_kinds.push(BlockKind::Block),
            Loop(_) => self.block_kinds.push(BlockKind::Loop),

            // Push the `if` block kind, and then when we finish encoding the
            // `if` block, we'll pop the `if` kind and push the `else`
            // kind. This allows us to maintain the `self.blocks.len() ==
            // self.block_kinds.len()` invariant.
            IfElse(_) => self.block_kinds.push(BlockKind::If),

            BrTable(e) => {
                self.hasher.write_u8(0x0e); // br_table
                self.hasher.write_usize(e.blocks.len());
                for b in e.blocks.iter() {
                    let target = self.branch_target(*b);
                    self.hasher.write_u32(target);
                }
                let default = self.branch_target(e.default);
                self.hasher.write_u32(default);
            }

            Const(e) => match e.value {
                Value::I32(_) => self.hasher.write_u8(0x41),
                Value::I64(_) => self.hasher.write_u8(0x42),
                Value::F32(_) => self.hasher.write_u8(0x43),
                Value::F64(_) => self.hasher.write_u8(0x44),
                Value::V128(_) => unimplemented!(),
            },
            Drop(_) => self.hasher.write_u8(0x1a),   // drop
            Return(_) => self.hasher.write_u8(0x0f), // return

            MemorySize(_e) => {
                self.hasher.write_u8(0x3f); // memory.size
            }

            MemoryGrow(_e) => {
                self.hasher.write_u8(0x40); // memory.grow
            }

            MemoryInit(_e) => {
                self.hasher.write(&[0xfc, 0x08]); // memory.init
            }

            DataDrop(_e) => {
                self.hasher.write(&[0xfc, 0x09]); // data.drop
            }

            MemoryCopy(_e) => {
                self.hasher.write(&[0xfc, 0x0a]); // memory.copy
            }

            MemoryFill(_e) => {
                self.hasher.write(&[0xfc, 0x0b]); // memory.fill
            }

            Binop(e) => {
                use walrus::ir::BinaryOp::*;

                match e.op {
                    I32Eq => self.hasher.write_u8(0x46),
                    I32Ne => self.hasher.write_u8(0x47),
                    I32LtS => self.hasher.write_u8(0x48),
                    I32LtU => self.hasher.write_u8(0x49),
                    I32GtS => self.hasher.write_u8(0x4a),
                    I32GtU => self.hasher.write_u8(0x4b),
                    I32LeS => self.hasher.write_u8(0x4c),
                    I32LeU => self.hasher.write_u8(0x4d),
                    I32GeS => self.hasher.write_u8(0x4e),
                    I32GeU => self.hasher.write_u8(0x4f),

                    I64Eq => self.hasher.write_u8(0x51),
                    I64Ne => self.hasher.write_u8(0x52),
                    I64LtS => self.hasher.write_u8(0x53),
                    I64LtU => self.hasher.write_u8(0x54),
                    I64GtS => self.hasher.write_u8(0x55),
                    I64GtU => self.hasher.write_u8(0x56),
                    I64LeS => self.hasher.write_u8(0x57),
                    I64LeU => self.hasher.write_u8(0x58),
                    I64GeS => self.hasher.write_u8(0x59),
                    I64GeU => self.hasher.write_u8(0x5a),

                    F32Eq => self.hasher.write_u8(0x5b),
                    F32Ne => self.hasher.write_u8(0x5c),
                    F32Lt => self.hasher.write_u8(0x5d),
                    F32Gt => self.hasher.write_u8(0x5e),
                    F32Le => self.hasher.write_u8(0x5f),
                    F32Ge => self.hasher.write_u8(0x60),

                    F64Eq => self.hasher.write_u8(0x61),
                    F64Ne => self.hasher.write_u8(0x62),
                    F64Lt => self.hasher.write_u8(0x63),
                    F64Gt => self.hasher.write_u8(0x64),
                    F64Le => self.hasher.write_u8(0x65),
                    F64Ge => self.hasher.write_u8(0x66),

                    I32Add => self.hasher.write_u8(0x6a),
                    I32Sub => self.hasher.write_u8(0x6b),
                    I32Mul => self.hasher.write_u8(0x6c),
                    I32DivS => self.hasher.write_u8(0x6d),
                    I32DivU => self.hasher.write_u8(0x6e),
                    I32RemS => self.hasher.write_u8(0x6f),
                    I32RemU => self.hasher.write_u8(0x70),
                    I32And => self.hasher.write_u8(0x71),
                    I32Or => self.hasher.write_u8(0x72),
                    I32Xor => self.hasher.write_u8(0x73),
                    I32Shl => self.hasher.write_u8(0x74),
                    I32ShrS => self.hasher.write_u8(0x75),
                    I32ShrU => self.hasher.write_u8(0x76),
                    I32Rotl => self.hasher.write_u8(0x77),
                    I32Rotr => self.hasher.write_u8(0x78),

                    I64Add => self.hasher.write_u8(0x7c),
                    I64Sub => self.hasher.write_u8(0x7d),
                    I64Mul => self.hasher.write_u8(0x7e),
                    I64DivS => self.hasher.write_u8(0x7f),
                    I64DivU => self.hasher.write_u8(0x80),
                    I64RemS => self.hasher.write_u8(0x81),
                    I64RemU => self.hasher.write_u8(0x82),
                    I64And => self.hasher.write_u8(0x83),
                    I64Or => self.hasher.write_u8(0x84),
                    I64Xor => self.hasher.write_u8(0x85),
                    I64Shl => self.hasher.write_u8(0x86),
                    I64ShrS => self.hasher.write_u8(0x87),
                    I64ShrU => self.hasher.write_u8(0x88),
                    I64Rotl => self.hasher.write_u8(0x89),
                    I64Rotr => self.hasher.write_u8(0x8a),

                    F32Add => self.hasher.write_u8(0x92),
                    F32Sub => self.hasher.write_u8(0x93),
                    F32Mul => self.hasher.write_u8(0x94),
                    F32Div => self.hasher.write_u8(0x95),
                    F32Min => self.hasher.write_u8(0x96),
                    F32Max => self.hasher.write_u8(0x97),
                    F32Copysign => self.hasher.write_u8(0x98),

                    F64Add => self.hasher.write_u8(0xa0),
                    F64Sub => self.hasher.write_u8(0xa1),
                    F64Mul => self.hasher.write_u8(0xa2),
                    F64Div => self.hasher.write_u8(0xa3),
                    F64Min => self.hasher.write_u8(0xa4),
                    F64Max => self.hasher.write_u8(0xa5),
                    F64Copysign => self.hasher.write_u8(0xa6),

                    I8x16ReplaceLane { idx } => self.hasher.write(&[0xfd, 23, idx]),
                    I16x8ReplaceLane { idx } => self.hasher.write(&[0xfd, 26, idx]),
                    I32x4ReplaceLane { idx } => self.hasher.write(&[0xfd, 28, idx]),
                    I64x2ReplaceLane { idx } => self.hasher.write(&[0xfd, 30, idx]),
                    F32x4ReplaceLane { idx } => self.hasher.write(&[0xfd, 32, idx]),
                    F64x2ReplaceLane { idx } => self.hasher.write(&[0xfd, 34, idx]),

                    I8x16Eq => self.simd(0x23),
                    I8x16Ne => self.simd(0x24),
                    I8x16LtS => self.simd(0x25),
                    I8x16LtU => self.simd(0x26),
                    I8x16GtS => self.simd(0x27),
                    I8x16GtU => self.simd(0x28),
                    I8x16LeS => self.simd(0x29),
                    I8x16LeU => self.simd(0x2a),
                    I8x16GeS => self.simd(0x2b),
                    I8x16GeU => self.simd(0x2c),

                    I16x8Eq => self.simd(0x2d),
                    I16x8Ne => self.simd(0x2e),
                    I16x8LtS => self.simd(0x2f),
                    I16x8LtU => self.simd(0x30),
                    I16x8GtS => self.simd(0x31),
                    I16x8GtU => self.simd(0x32),
                    I16x8LeS => self.simd(0x33),
                    I16x8LeU => self.simd(0x34),
                    I16x8GeS => self.simd(0x35),
                    I16x8GeU => self.simd(0x36),

                    I32x4Eq => self.simd(0x37),
                    I32x4Ne => self.simd(0x38),
                    I32x4LtS => self.simd(0x39),
                    I32x4LtU => self.simd(0x3a),
                    I32x4GtS => self.simd(0x3b),
                    I32x4GtU => self.simd(0x3c),
                    I32x4LeS => self.simd(0x3d),
                    I32x4LeU => self.simd(0x3e),
                    I32x4GeS => self.simd(0x3f),
                    I32x4GeU => self.simd(0x40),

                    I64x2Eq => self.simd(214),
                    I64x2Ne => self.simd(215),
                    I64x2LtS => self.simd(216),
                    I64x2GtS => self.simd(217),
                    I64x2LeS => self.simd(218),
                    I64x2GeS => self.simd(219),

                    F32x4Eq => self.simd(0x41),
                    F32x4Ne => self.simd(0x42),
                    F32x4Lt => self.simd(0x43),
                    F32x4Gt => self.simd(0x44),
                    F32x4Le => self.simd(0x45),
                    F32x4Ge => self.simd(0x46),

                    F64x2Eq => self.simd(0x47),
                    F64x2Ne => self.simd(0x48),
                    F64x2Lt => self.simd(0x49),
                    F64x2Gt => self.simd(0x4a),
                    F64x2Le => self.simd(0x4b),
                    F64x2Ge => self.simd(0x4c),

                    V128And => self.simd(0x4e),
                    V128AndNot => self.simd(0x4f),
                    V128Or => self.simd(0x50),
                    V128Xor => self.simd(0x51),

                    I8x16NarrowI16x8S => self.simd(0x65),
                    I8x16NarrowI16x8U => self.simd(0x66),
                    I8x16Shl => self.simd(0x6b),
                    I8x16ShrS => self.simd(0x6c),
                    I8x16ShrU => self.simd(0x6d),
                    I8x16Add => self.simd(0x6e),
                    I8x16AddSatS => self.simd(0x6f),
                    I8x16AddSatU => self.simd(0x70),
                    I8x16Sub => self.simd(0x71),
                    I8x16SubSatS => self.simd(0x72),
                    I8x16SubSatU => self.simd(0x73),
                    I8x16MinS => self.simd(0x76),
                    I8x16MinU => self.simd(0x77),
                    I8x16MaxS => self.simd(0x78),
                    I8x16MaxU => self.simd(0x79),
                    I8x16RoundingAverageU => self.simd(0x7b),

                    I16x8NarrowI32x4S => self.simd(0x85),
                    I16x8NarrowI32x4U => self.simd(0x86),
                    I16x8Shl => self.simd(0x8b),
                    I16x8ShrS => self.simd(0x8c),
                    I16x8ShrU => self.simd(0x8d),
                    I16x8Add => self.simd(0x8e),
                    I16x8AddSatS => self.simd(0x8f),
                    I16x8AddSatU => self.simd(0x90),
                    I16x8Sub => self.simd(0x91),
                    I16x8SubSatS => self.simd(0x92),
                    I16x8SubSatU => self.simd(0x93),
                    I16x8Mul => self.simd(0x95),
                    I16x8MinS => self.simd(0x96),
                    I16x8MinU => self.simd(0x97),
                    I16x8MaxS => self.simd(0x98),
                    I16x8MaxU => self.simd(0x99),
                    I16x8RoundingAverageU => self.simd(0x9b),

                    I32x4Shl => self.simd(0xab),
                    I32x4ShrS => self.simd(0xac),
                    I32x4ShrU => self.simd(0xad),
                    I32x4Add => self.simd(0xae),
                    I32x4Sub => self.simd(0xb1),
                    I32x4Mul => self.simd(0xb5),
                    I32x4MinS => self.simd(0xb6),
                    I32x4MinU => self.simd(0xb7),
                    I32x4MaxS => self.simd(0xb8),
                    I32x4MaxU => self.simd(0xb9),

                    I64x2Shl => self.simd(0xcb),
                    I64x2ShrS => self.simd(0xcc),
                    I64x2ShrU => self.simd(0xcd),
                    I64x2Add => self.simd(0xce),
                    I64x2Sub => self.simd(0xd1),
                    I64x2Mul => self.simd(0xd5),

                    F32x4Add => self.simd(0xe4),
                    F32x4Sub => self.simd(0xe5),
                    F32x4Mul => self.simd(0xe6),
                    F32x4Div => self.simd(0xe7),
                    F32x4Min => self.simd(0xe8),
                    F32x4Max => self.simd(0xe9),
                    F32x4PMin => self.simd(0xea),
                    F32x4PMax => self.simd(0xeb),

                    F64x2Add => self.simd(0xf0),
                    F64x2Sub => self.simd(0xf1),
                    F64x2Mul => self.simd(0xf2),
                    F64x2Div => self.simd(0xf3),
                    F64x2Min => self.simd(0xf4),
                    F64x2Max => self.simd(0xf5),
                    F64x2PMin => self.simd(0xf6),
                    F64x2PMax => self.simd(0xf7),

                    I32x4DotI16x8S => self.simd(0xba),

                    I16x8Q15MulrSatS => self.simd(130),
                    I16x8ExtMulLowI8x16S => self.simd(156),
                    I16x8ExtMulHighI8x16S => self.simd(157),
                    I16x8ExtMulLowI8x16U => self.simd(158),
                    I16x8ExtMulHighI8x16U => self.simd(159),
                    I32x4ExtMulLowI16x8S => self.simd(188),
                    I32x4ExtMulHighI16x8S => self.simd(189),
                    I32x4ExtMulLowI16x8U => self.simd(190),
                    I32x4ExtMulHighI16x8U => self.simd(191),
                    I64x2ExtMulLowI32x4S => self.simd(220),
                    I64x2ExtMulHighI32x4S => self.simd(221),
                    I64x2ExtMulLowI32x4U => self.simd(222),
                    I64x2ExtMulHighI32x4U => self.simd(223),
                }
            }

            Unop(e) => {
                use walrus::ir::UnaryOp::*;

                match e.op {
                    I32Eqz => self.hasher.write_u8(0x45),
                    I32Clz => self.hasher.write_u8(0x67),
                    I32Ctz => self.hasher.write_u8(0x68),
                    I32Popcnt => self.hasher.write_u8(0x69),

                    I64Eqz => self.hasher.write_u8(0x50),
                    I64Clz => self.hasher.write_u8(0x79),
                    I64Ctz => self.hasher.write_u8(0x7a),
                    I64Popcnt => self.hasher.write_u8(0x7b),

                    F32Abs => self.hasher.write_u8(0x8b),
                    F32Neg => self.hasher.write_u8(0x8c),
                    F32Ceil => self.hasher.write_u8(0x8d),
                    F32Floor => self.hasher.write_u8(0x8e),
                    F32Trunc => self.hasher.write_u8(0x8f),
                    F32Nearest => self.hasher.write_u8(0x90),
                    F32Sqrt => self.hasher.write_u8(0x91),

                    F64Abs => self.hasher.write_u8(0x99),
                    F64Neg => self.hasher.write_u8(0x9a),
                    F64Ceil => self.hasher.write_u8(0x9b),
                    F64Floor => self.hasher.write_u8(0x9c),
                    F64Trunc => self.hasher.write_u8(0x9d),
                    F64Nearest => self.hasher.write_u8(0x9e),
                    F64Sqrt => self.hasher.write_u8(0x9f),

                    I32WrapI64 => self.hasher.write_u8(0xa7),
                    I32TruncSF32 => self.hasher.write_u8(0xa8),
                    I32TruncUF32 => self.hasher.write_u8(0xa9),
                    I32TruncSF64 => self.hasher.write_u8(0xaa),
                    I32TruncUF64 => self.hasher.write_u8(0xab),
                    I64ExtendSI32 => self.hasher.write_u8(0xac),
                    I64ExtendUI32 => self.hasher.write_u8(0xad),
                    I64TruncSF32 => self.hasher.write_u8(0xae),
                    I64TruncUF32 => self.hasher.write_u8(0xaf),
                    I64TruncSF64 => self.hasher.write_u8(0xb0),
                    I64TruncUF64 => self.hasher.write_u8(0xb1),

                    F32ConvertSI32 => self.hasher.write_u8(0xb2),
                    F32ConvertUI32 => self.hasher.write_u8(0xb3),
                    F32ConvertSI64 => self.hasher.write_u8(0xb4),
                    F32ConvertUI64 => self.hasher.write_u8(0xb5),
                    F32DemoteF64 => self.hasher.write_u8(0xb6),
                    F64ConvertSI32 => self.hasher.write_u8(0xb7),
                    F64ConvertUI32 => self.hasher.write_u8(0xb8),
                    F64ConvertSI64 => self.hasher.write_u8(0xb9),
                    F64ConvertUI64 => self.hasher.write_u8(0xba),
                    F64PromoteF32 => self.hasher.write_u8(0xbb),

                    I32ReinterpretF32 => self.hasher.write_u8(0xbc),
                    I64ReinterpretF64 => self.hasher.write_u8(0xbd),
                    F32ReinterpretI32 => self.hasher.write_u8(0xbe),
                    F64ReinterpretI64 => self.hasher.write_u8(0xbf),

                    I32Extend8S => self.hasher.write_u8(0xc0),
                    I32Extend16S => self.hasher.write_u8(0xc1),
                    I64Extend8S => self.hasher.write_u8(0xc2),
                    I64Extend16S => self.hasher.write_u8(0xc3),
                    I64Extend32S => self.hasher.write_u8(0xc4),

                    I8x16Splat => self.simd(15),
                    I16x8Splat => self.simd(16),
                    I32x4Splat => self.simd(17),
                    I64x2Splat => self.simd(18),
                    F32x4Splat => self.simd(19),
                    F64x2Splat => self.simd(20),
                    I8x16ExtractLaneS { idx } => {
                        self.simd(21);
                        self.hasher.write_u8(idx);
                    }
                    I8x16ExtractLaneU { idx } => {
                        self.simd(22);
                        self.hasher.write_u8(idx);
                    }
                    I16x8ExtractLaneS { idx } => {
                        self.simd(24);
                        self.hasher.write_u8(idx);
                    }
                    I16x8ExtractLaneU { idx } => {
                        self.simd(25);
                        self.hasher.write_u8(idx);
                    }
                    I32x4ExtractLane { idx } => {
                        self.simd(27);
                        self.hasher.write_u8(idx);
                    }
                    I64x2ExtractLane { idx } => {
                        self.simd(29);
                        self.hasher.write_u8(idx);
                    }
                    F32x4ExtractLane { idx } => {
                        self.simd(31);
                        self.hasher.write_u8(idx);
                    }
                    F64x2ExtractLane { idx } => {
                        self.simd(33);
                        self.hasher.write_u8(idx);
                    }

                    V128Not => self.simd(0x4d),

                    V128AnyTrue => self.simd(0x53),

                    I8x16Abs => self.simd(0x60),
                    I8x16Popcnt => self.simd(98),
                    I8x16Neg => self.simd(0x61),
                    I8x16AllTrue => self.simd(99),
                    I8x16Bitmask => self.simd(0x64),

                    I16x8Abs => self.simd(0x80),
                    I16x8Neg => self.simd(0x81),
                    I16x8AllTrue => self.simd(131),
                    I16x8Bitmask => self.simd(0x84),
                    I16x8WidenLowI8x16S => self.simd(0x87),
                    I16x8WidenHighI8x16S => self.simd(0x88),
                    I16x8WidenLowI8x16U => self.simd(0x89),
                    I16x8WidenHighI8x16U => self.simd(0x8a),

                    I32x4Abs => self.simd(0xa0),
                    I32x4Neg => self.simd(0xa1),
                    I32x4AllTrue => self.simd(163),
                    I32x4Bitmask => self.simd(0xa4),
                    I32x4WidenLowI16x8S => self.simd(0xa7),
                    I32x4WidenHighI16x8S => self.simd(0xa8),
                    I32x4WidenLowI16x8U => self.simd(0xa9),
                    I32x4WidenHighI16x8U => self.simd(0xaa),

                    I64x2Abs => self.simd(192),
                    I64x2Neg => self.simd(193),
                    I64x2AllTrue => self.simd(195),
                    I64x2Bitmask => self.simd(196),

                    F32x4Abs => self.simd(224),
                    F32x4Neg => self.simd(225),
                    F32x4Sqrt => self.simd(227),
                    F32x4Ceil => self.simd(103),
                    F32x4Floor => self.simd(104),
                    F32x4Trunc => self.simd(105),
                    F32x4Nearest => self.simd(106),

                    F64x2Abs => self.simd(236),
                    F64x2Neg => self.simd(237),
                    F64x2Sqrt => self.simd(239),
                    F64x2Ceil => self.simd(116),
                    F64x2Floor => self.simd(117),
                    F64x2Trunc => self.simd(122),
                    F64x2Nearest => self.simd(148),

                    I32x4TruncSatF32x4S => self.simd(248),
                    I32x4TruncSatF32x4U => self.simd(249),
                    F32x4ConvertI32x4S => self.simd(250),
                    F32x4ConvertI32x4U => self.simd(251),

                    I32TruncSSatF32 => self.hasher.write(&[0xfc, 0x00]),
                    I32TruncUSatF32 => self.hasher.write(&[0xfc, 0x01]),
                    I32TruncSSatF64 => self.hasher.write(&[0xfc, 0x02]),
                    I32TruncUSatF64 => self.hasher.write(&[0xfc, 0x03]),
                    I64TruncSSatF32 => self.hasher.write(&[0xfc, 0x04]),
                    I64TruncUSatF32 => self.hasher.write(&[0xfc, 0x05]),
                    I64TruncSSatF64 => self.hasher.write(&[0xfc, 0x06]),
                    I64TruncUSatF64 => self.hasher.write(&[0xfc, 0x07]),

                    I16x8ExtAddPairwiseI8x16S => self.simd(124),
                    I16x8ExtAddPairwiseI8x16U => self.simd(125),
                    I32x4ExtAddPairwiseI16x8S => self.simd(126),
                    I32x4ExtAddPairwiseI16x8U => self.simd(127),
                    I64x2ExtendLowI32x4S => self.simd(199),
                    I64x2ExtendHighI32x4S => self.simd(200),
                    I64x2ExtendLowI32x4U => self.simd(201),
                    I64x2ExtendHighI32x4U => self.simd(202),
                    I32x4TruncSatF64x2SZero => self.simd(252),
                    I32x4TruncSatF64x2UZero => self.simd(253),
                    F64x2ConvertLowI32x4S => self.simd(254),
                    F64x2ConvertLowI32x4U => self.simd(255),
                    F32x4DemoteF64x2Zero => self.simd(94),
                    F64x2PromoteLowF32x4 => self.simd(95),
                }
            }

            Select(e) => {
                match e.ty {
                    Some(ty) => {
                        self.hasher.write_u8(0x1c);
                        self.hasher.write_u8(0x01);
                        ty.hash(self.hasher);
                    }
                    None => {
                        self.hasher.write_u8(0x1b); // select
                    }
                }
            }

            Unreachable(_) => {
                self.hasher.write_u8(0x00); // unreachable
            }

            Br(e) => {
                let target = self.branch_target(e.block);
                self.hasher.write_u8(0x0c); // br
                self.hasher.write_u32(target);
            }

            BrIf(e) => {
                let target = self.branch_target(e.block);
                self.hasher.write_u8(0x0d); // br_if
                self.hasher.write_u32(target);
            }

            Call(_e) => {
                self.hasher.write_u8(0x10); // call
            }

            CallIndirect(_e) => {
                self.hasher.write_u8(0x11); // call_indirect
            }

            LocalGet(_e) => {
                self.hasher.write_u8(0x20); // local.get
            }

            LocalSet(_e) => {
                self.hasher.write_u8(0x21); // local.set
            }

            LocalTee(_e) => {
                self.hasher.write_u8(0x22); // local.tee
            }

            GlobalGet(_e) => {
                self.hasher.write_u8(0x23); // global.get
            }

            GlobalSet(_e) => {
                self.hasher.write_u8(0x24); // global.set
            }

            Load(e) => {
                use walrus::ir::ExtendedLoad::*;
                use walrus::ir::LoadKind::*;
                match e.kind {
                    I32 { atomic: false } => self.hasher.write_u8(0x28), // i32.load
                    I32 { atomic: true } => self.hasher.write(&[0xfe, 0x10]), // i32.atomic.load
                    I64 { atomic: false } => self.hasher.write_u8(0x29), // i64.load
                    I64 { atomic: true } => self.hasher.write(&[0xfe, 0x11]), // i64.atomic.load
                    F32 => self.hasher.write_u8(0x2a),                   // f32.load
                    F64 => self.hasher.write_u8(0x2b),                   // f64.load
                    V128 => self.simd(0),
                    I32_8 { kind: SignExtend } => self.hasher.write_u8(0x2c),
                    I32_8 { kind: ZeroExtend } => self.hasher.write_u8(0x2d),
                    I32_8 {
                        kind: ZeroExtendAtomic,
                    } => self.hasher.write(&[0xfe, 0x12]),
                    I32_16 { kind: SignExtend } => self.hasher.write_u8(0x2e),
                    I32_16 { kind: ZeroExtend } => self.hasher.write_u8(0x2f),
                    I32_16 {
                        kind: ZeroExtendAtomic,
                    } => self.hasher.write(&[0xfe, 0x13]),
                    I64_8 { kind: SignExtend } => self.hasher.write_u8(0x30),
                    I64_8 { kind: ZeroExtend } => self.hasher.write_u8(0x31),
                    I64_8 {
                        kind: ZeroExtendAtomic,
                    } => self.hasher.write(&[0xfe, 0x14]),
                    I64_16 { kind: SignExtend } => self.hasher.write_u8(0x32),
                    I64_16 { kind: ZeroExtend } => self.hasher.write_u8(0x33),
                    I64_16 {
                        kind: ZeroExtendAtomic,
                    } => self.hasher.write(&[0xfe, 0x15]),
                    I64_32 { kind: SignExtend } => self.hasher.write_u8(0x34),
                    I64_32 { kind: ZeroExtend } => self.hasher.write_u8(0x35),
                    I64_32 {
                        kind: ZeroExtendAtomic,
                    } => self.hasher.write(&[0xfe, 0x16]),
                }
            }

            Store(e) => {
                use walrus::ir::StoreKind::*;
                match e.kind {
                    I32 { atomic: false } => self.hasher.write_u8(0x36), // i32.store
                    I32 { atomic: true } => self.hasher.write(&[0xfe, 0x17]), // i32.atomic.store
                    I64 { atomic: false } => self.hasher.write_u8(0x37), // i64.store
                    I64 { atomic: true } => self.hasher.write(&[0xfe, 0x18]), // i64.atomic.store
                    F32 => self.hasher.write_u8(0x38),                   // f32.store
                    F64 => self.hasher.write_u8(0x39),                   // f64.store
                    V128 => self.simd(11),                               // v128.store
                    I32_8 { atomic: false } => self.hasher.write_u8(0x3a), // i32.store8
                    I32_8 { atomic: true } => self.hasher.write(&[0xfe, 0x19]), // i32.atomic.store8
                    I32_16 { atomic: false } => self.hasher.write_u8(0x3b), // i32.store16
                    I32_16 { atomic: true } => self.hasher.write(&[0xfe, 0x1a]), // i32.atomic.store16
                    I64_8 { atomic: false } => self.hasher.write_u8(0x3c),       // i64.store8
                    I64_8 { atomic: true } => self.hasher.write(&[0xfe, 0x1b]), // i64.atomic.store8
                    I64_16 { atomic: false } => self.hasher.write_u8(0x3d),     // i64.store16
                    I64_16 { atomic: true } => self.hasher.write(&[0xfe, 0x1c]), // i64.atomic.store16
                    I64_32 { atomic: false } => self.hasher.write_u8(0x3e),      // i64.store32
                    I64_32 { atomic: true } => self.hasher.write(&[0xfe, 0x1d]), // i64.atomic.store32
                }
            }

            AtomicRmw(e) => {
                use walrus::ir::AtomicOp::*;
                use walrus::ir::AtomicWidth::*;

                self.hasher.write_u8(0xfe);
                self.hasher.write_u8(match (e.op, e.width) {
                    (Add, I32) => 0x1e,
                    (Add, I64) => 0x1f,
                    (Add, I32_8) => 0x20,
                    (Add, I32_16) => 0x21,
                    (Add, I64_8) => 0x22,
                    (Add, I64_16) => 0x23,
                    (Add, I64_32) => 0x24,

                    (Sub, I32) => 0x25,
                    (Sub, I64) => 0x26,
                    (Sub, I32_8) => 0x27,
                    (Sub, I32_16) => 0x28,
                    (Sub, I64_8) => 0x29,
                    (Sub, I64_16) => 0x2a,
                    (Sub, I64_32) => 0x2b,

                    (And, I32) => 0x2c,
                    (And, I64) => 0x2d,
                    (And, I32_8) => 0x2e,
                    (And, I32_16) => 0x2f,
                    (And, I64_8) => 0x30,
                    (And, I64_16) => 0x31,
                    (And, I64_32) => 0x32,

                    (Or, I32) => 0x33,
                    (Or, I64) => 0x34,
                    (Or, I32_8) => 0x35,
                    (Or, I32_16) => 0x36,
                    (Or, I64_8) => 0x37,
                    (Or, I64_16) => 0x38,
                    (Or, I64_32) => 0x39,

                    (Xor, I32) => 0x3a,
                    (Xor, I64) => 0x3b,
                    (Xor, I32_8) => 0x3c,
                    (Xor, I32_16) => 0x3d,
                    (Xor, I64_8) => 0x3e,
                    (Xor, I64_16) => 0x3f,
                    (Xor, I64_32) => 0x40,

                    (Xchg, I32) => 0x41,
                    (Xchg, I64) => 0x42,
                    (Xchg, I32_8) => 0x43,
                    (Xchg, I32_16) => 0x44,
                    (Xchg, I64_8) => 0x45,
                    (Xchg, I64_16) => 0x46,
                    (Xchg, I64_32) => 0x47,
                });
            }

            Cmpxchg(e) => {
                use walrus::ir::AtomicWidth::*;

                self.hasher.write_u8(0xfe);
                self.hasher.write_u8(match e.width {
                    I32 => 0x48,
                    I64 => 0x49,
                    I32_8 => 0x4a,
                    I32_16 => 0x4b,
                    I64_8 => 0x4c,
                    I64_16 => 0x4d,
                    I64_32 => 0x4e,
                });
            }

            AtomicNotify(_e) => {
                self.hasher.write_u8(0xfe);
                self.hasher.write_u8(0x00);
            }

            AtomicWait(e) => {
                self.hasher.write_u8(0xfe);
                self.hasher.write_u8(if e.sixty_four { 0x02 } else { 0x01 });
            }

            AtomicFence(_e) => {
                self.hasher.write_u8(0xfe);
                self.hasher.write_u8(0x03);
                self.hasher.write_u8(0x00);
            }

            TableGet(_e) => {
                self.hasher.write_u8(0x25);
            }
            TableSet(_e) => {
                self.hasher.write_u8(0x26);
            }
            TableGrow(_e) => {
                self.hasher.write(&[0xfc, 0x0f]);
            }
            TableSize(_e) => {
                self.hasher.write(&[0xfc, 0x10]);
            }
            TableFill(_e) => {
                self.hasher.write(&[0xfc, 0x11]);
            }
            RefNull(e) => {
                self.hasher.write_u8(0xd0);
                e.ty.hash(self.hasher);
            }
            RefIsNull(_e) => {
                self.hasher.write_u8(0xd1);
            }
            RefFunc(_e) => {
                self.hasher.write_u8(0xd2);
            }

            V128Bitselect(_) => {
                self.simd(0x52);
            }
            I8x16Shuffle(e) => {
                self.simd(13);
                self.hasher.write(&e.indices);
            }
            I8x16Swizzle(_) => {
                self.simd(14);
            }
            LoadSimd(e) => {
                match e.kind {
                    LoadSimdKind::V128Load8x8S => self.simd(1),
                    LoadSimdKind::V128Load8x8U => self.simd(2),
                    LoadSimdKind::V128Load16x4S => self.simd(3),
                    LoadSimdKind::V128Load16x4U => self.simd(4),
                    LoadSimdKind::V128Load32x2S => self.simd(5),
                    LoadSimdKind::V128Load32x2U => self.simd(6),
                    LoadSimdKind::Splat8 => self.simd(7),
                    LoadSimdKind::Splat16 => self.simd(8),
                    LoadSimdKind::Splat32 => self.simd(9),
                    LoadSimdKind::Splat64 => self.simd(10),
                    LoadSimdKind::V128Load32Zero => self.simd(92),
                    LoadSimdKind::V128Load64Zero => self.simd(93),
                    LoadSimdKind::V128Load8Lane(_) => self.simd(84),
                    LoadSimdKind::V128Load16Lane(_) => self.simd(85),
                    LoadSimdKind::V128Load32Lane(_) => self.simd(86),
                    LoadSimdKind::V128Load64Lane(_) => self.simd(87),
                    LoadSimdKind::V128Store8Lane(_) => self.simd(88),
                    LoadSimdKind::V128Store16Lane(_) => self.simd(89),
                    LoadSimdKind::V128Store32Lane(_) => self.simd(90),
                    LoadSimdKind::V128Store64Lane(_) => self.simd(91),
                }
                match e.kind {
                    LoadSimdKind::V128Load8Lane(l)
                    | LoadSimdKind::V128Load16Lane(l)
                    | LoadSimdKind::V128Load32Lane(l)
                    | LoadSimdKind::V128Load64Lane(l)
                    | LoadSimdKind::V128Store8Lane(l)
                    | LoadSimdKind::V128Store16Lane(l)
                    | LoadSimdKind::V128Store32Lane(l)
                    | LoadSimdKind::V128Store64Lane(l) => self.hasher.write_u8(l),
                    _ => {}
                }
            }
            TableInit(_e) => {
                self.hasher.write(&[0xfc, 0x0c]);
            }
            TableCopy(_e) => {
                self.hasher.write(&[0xfc, 0x0e]);
            }
            ElemDrop(_e) => {
                self.hasher.write(&[0xfc, 0x0d]);
            }
        }
    }
}

impl<H: Hasher> Emit<'_, '_, H> {
    fn branch_target(&self, block: InstrSeqId) -> u32 {
        self.blocks.iter().rev().position(|b| *b == block).expect(
            "attempt to branch to invalid block; bad transformation pass introduced bad branching?",
        ) as u32
    }

    fn block_type(&mut self, ty: InstrSeqType) {
        match ty {
            InstrSeqType::Simple(None) => self.hasher.write_u8(0x40),
            InstrSeqType::Simple(Some(ty)) => ty.hash(self.hasher),
            InstrSeqType::MultiValue(ty) => self.module.types.get(ty).hash(self.hasher),
        }
    }

    fn simd(&mut self, opcode: u32) {
        self.hasher.write_u8(0xfd);
        self.hasher.write_u32(opcode);
    }
}
