const std = @import("std");

/// --------- Utilities ---------
/// 64-bit FNV-1a (deterministic "fast hash" for small strings).
pub fn fastHash64(bytes: []const u8) u64 {
    var hash: u64 = 0xcbf29ce484222325;
    const prime: u64 = 0x00000100000001B3;
    for (bytes) |b| {
        hash ^= @as(u64, b);
        hash *%= prime;
    }
    return hash;
}

/// --------- Basic IDs & Type Stubs (tune as needed) ---------
pub const VariableId = u32;

/// A (temporary) value type model. Replace with your richer system when ready.
pub const ValueType = enum(u8) {
    any = 0,
    bool,
    number,
    string,
    null_,
    undefined,
    object,
    function,
};

/// If you distinguish constants from runtime values, define a richer type.
/// For now, treat constants as the same set as `ValueMHIR`.
pub const ConstantMHIR = ValueMHIR;

/// --------- Name (auto-hashed string) ---------
/// Borrowed-name + precomputed hash. Make an owning counterpart if desired.
pub const Name = struct {
    value: []const u8,
    hash: u64,

    pub inline fn init(value: []const u8) Name {
        return .{ .value = value, .hash = fastHash64(value) };
    }

    pub inline fn slice(self: *const Name) []const u8 {
        return self.value;
    }

    pub inline fn getHash(self: *const Name) u64 {
        return self.hash;
    }
};

/// --------- Values ---------
/// Matches Rust's #[repr(u8)] + payload variants.
pub const ValueMHIR = union(enum(u8)) {
    Undefined, // 0
    Null, // 1
    Boolean: bool, // 2
    Number: f64, // 3
    String: []const u8, // 4  (borrowed; switch to owning if needed)

    pub fn tag(self: ValueMHIR) u8 {
        return @intFromEnum(@as(@TypeOf(self.EnumTag), self));
    }
};

/// --------- Operators ---------
pub const BinaryOperator = enum(u8) {
    Add = 0, // +
    Sub = 1, // -
    Mul = 2, // *
    Div = 3, // /
    Mod = 4, // %
    Pow = 5, // **
    And = 6, // &
    Or = 7, // |
    Xor = 8, // ^
    Shl = 9, // <<
    Shr = 10, // >>
    Sar = 11, // >>>
    Sal = 12, // <<<
    AndBool = 13, // &&
    OrBool = 14, // ||
    Eq = 15, // ==
    Ne = 16, // !=
    Lt = 17, // <
    Gt = 18, // >
    Le = 19, // <=
    Ge = 20, // >=
    Id = 21, // ===
    Ni = 22, // !==
};

pub const UnaryOperator = enum(u8) {
    Neg = 0, // -
    Pos = 1, // +
    Inc = 2, // ++
    Dec = 3, // --
    LogicalNot = 4, // !
    ToBoolean = 5, // !!
    BitwiseNot = 6, // ~
    Rol = 7, // <<~
    Ror = 8, // ~>>
    Await = 9, // await
};

/// --------- Instruction Operands ---------
pub const RegisterType = i8;
pub const RegisterParentHolder = ?i16;
pub const RegisterId = i16;

pub const RegisterRef = struct {
    typ: RegisterType,
    parent: RegisterParentHolder,
    id: RegisterId,
};

pub const InstructionOperator = union(enum(u8)) {
    LayeredMap: Name,
    Register: RegisterRef,
    ConstantValue: ValueMHIR,
};

/// --------- Instructions ---------
/// We assign explicit tag values where Rust used `= N`.
/// Everything else follows a stable order (you can renumber if you need ABI stability later).
pub const InstructionTag = enum(u16) {
    // Variable management
    DeclareNewVar = 0,
    AssignToExistingVar = 1,

    // Basic ops
    BinaryOperation = 10,
    UnaryOperation = 11,

    // Functions & early-form returns
    DeclareFunction = 200,
    ReturnLegacy = 201, // Rust earlier form: Option<ValueMHIR>

    LoadConstant = 300,
    MoveValue = 301,

    // Blocks & conditionals
    RunBlock = 450,
    RunIfChain = 460,

    // Calls
    CallFunction = 500,
    CallConstructor = 501,
    CallDestructor = 502,
    CallSuper = 503,
    CallObjectFunction = 504,

    // Exceptions
    ThrowException = 702,
    Try = 703,

    // Loops
    LoopFor = 750,
    LoopWhile = 751,
    LoopForEach = 752,

    // Classes & objects
    NewClass = 950,
    NewInterface = 951,
    NewEnum = 952,
    NewTypeAlias = 953,
    CreateNewObject = 954,
    CreateNewObjectFromClass = 955,
    CreateNewObjectFromInterface = 956,

    // Property ops
    GetProperty = 1000,
    SetProperty = 1001,
    DeleteProperty = 1005,
    HasProperty = 1006,
    GetSuper = 1007,
    SetSuper = 1008,

    // Control flow
    Break = 1202,
    BreakNamed = 1203,
    Continue = 1204,
    ContinueNamed = 1205,
    ReturnVoid = 1206,
    Return = 1207, // newer return: src: InstructionOperator

    // Arrays
    CreateArray = 1300,
    GetIndex = 1301,
    SetIndex = 1302,

    // Built-ins
    Print = 1400,
    Assert = 1401,
};

pub const IfBranch = struct {
    condition: InstructionOperator,
    body: []InstructionMHIR,
};

pub const KVPair = struct {
    key: InstructionOperator,
    value: InstructionOperator,
};

pub const InstructionMHIR = union(InstructionTag) {
    // Variable Management
    DeclareNewVar: struct {
        var_id: InstructionOperator,
        typ: ValueType,
    },
    AssignToExistingVar: struct {
        dest: InstructionOperator,
        value: ValueMHIR,
    },

    // Operations
    BinaryOperation: struct {
        dest: VariableId,
        op: BinaryOperator,
        lhs: ValueMHIR,
        rhs: ValueMHIR,
    },
    UnaryOperation: struct {
        dest: VariableId,
        op: UnaryOperator,
        operand: ValueMHIR,
    },

    // Function Decls & early Return form
    DeclareFunction: struct {
        dest: InstructionOperator,
        params: ?[]InstructionOperator,
        return_type: ?ValueType,
        body: ?[]InstructionMHIR,
        captures: []Name, // captured variable names
    },
    ReturnLegacy: struct { // Rust's early `Return { value: Option<ValueMHIR> }`
        value: ?ValueMHIR,
    },

    LoadConstant: struct {
        dest: VariableId,
        constant: ConstantMHIR,
    },
    MoveValue: struct {
        dest: VariableId,
        value: ValueMHIR,
    },

    // Blocks
    RunBlock: struct {
        src: ?[]InstructionMHIR,
    },
    RunIfChain: struct {
        branches: []IfBranch,
        else_block: ?[]InstructionMHIR,
    },

    // Calls
    CallFunction: struct {
        dest: InstructionOperator,
        func: InstructionOperator,
        args: []InstructionOperator,
    },
    CallConstructor: struct {
        dest: InstructionOperator,
        class: InstructionOperator,
        args: []InstructionOperator,
    },
    CallDestructor: struct {
        obj: InstructionOperator,
    },
    CallSuper: struct {
        dest: InstructionOperator,
        base: InstructionOperator,
        key: InstructionOperator,
        args: []InstructionOperator,
    },
    CallObjectFunction: struct {
        dest: InstructionOperator,
        func: InstructionOperator,
        this_arg: InstructionOperator,
        args: []InstructionOperator,
    },

    // Exceptions
    ThrowException: struct {
        src: InstructionOperator,
    },
    Try: struct {
        try_block: []InstructionMHIR,
        catch_identifier: ?InstructionOperator,
        catch_block: ?[]InstructionMHIR,
        finally_block: ?[]InstructionMHIR,
    },

    // Loops and iterators
    LoopFor: struct {
        init: ?[]InstructionMHIR,
        cond_prep: ?[]InstructionMHIR,
        condition: ?InstructionOperator,
        update: ?[]InstructionMHIR,
        body: []InstructionMHIR,
        name: ?[]const u8,
    },
    LoopWhile: struct {
        cond_prep: []InstructionMHIR,
        condition: InstructionOperator,
        body: []InstructionMHIR,
        name: ?[]const u8,
        is_do_while: bool,
    },
    LoopForEach: struct {
        iterable: InstructionOperator,
        current_iterator: InstructionOperator,
        body: ?[]InstructionMHIR,
        name: ?[]const u8,
    },

    // Classes and objects
    NewClass: struct {
        dest: InstructionOperator,
        name: InstructionOperator,
        constructor: ?InstructionOperator,
        destructor: ?InstructionOperator,
        extends: ?InstructionOperator,
        implements: ?[]InstructionOperator,
        properties: ?[]KVPair,
        methods: ?[]KVPair,
        getters: ?[]KVPair,
        setters: ?[]KVPair,
        decorators: ?[]InstructionOperator,
    },
    NewInterface: struct {
        dest: InstructionOperator,
        name: InstructionOperator,
        extends: ?[]InstructionOperator,
        properties: ?[]KVPair,
        methods: ?[]KVPair,
        call_signatures: ?[]InstructionOperator,
    },
    NewEnum: struct {
        dest: InstructionOperator,
        name: InstructionOperator,
        members: ?[]KVPair,
    },
    NewTypeAlias: struct {
        dest: InstructionOperator,
        name: InstructionOperator,
        aliased_type: InstructionOperator,
    },
    CreateNewObject: struct {
        dest: InstructionOperator,
        properties: ?[]KVPair,
    },
    CreateNewObjectFromClass: struct {
        dest: InstructionOperator,
        class: InstructionOperator,
        properties: ?[]KVPair,
    },
    CreateNewObjectFromInterface: struct {
        dest: InstructionOperator,
        interface: InstructionOperator,
        properties: ?[]KVPair,
    },

    // Property Operations
    GetProperty: struct {
        dest: InstructionOperator,
        obj: InstructionOperator,
        key: InstructionOperator,
    },
    SetProperty: struct {
        obj: InstructionOperator,
        key: InstructionOperator,
        value: InstructionOperator,
    },
    DeleteProperty: struct {
        dest: InstructionOperator,
        obj: InstructionOperator,
        key: InstructionOperator,
    },
    HasProperty: struct {
        dest: InstructionOperator,
        obj: InstructionOperator,
        key: InstructionOperator,
    },
    GetSuper: struct {
        dest: InstructionOperator,
        base: InstructionOperator,
    },
    SetSuper: struct {
        base: InstructionOperator,
        key: InstructionOperator,
        value: InstructionOperator,
    },

    // Control Flow
    Break: void,
    BreakNamed: struct { name: InstructionOperator },
    Continue: void,
    ContinueNamed: struct { name: InstructionOperator },
    ReturnVoid: void,
    Return: struct { src: InstructionOperator }, // newer return form

    // Arrays
    CreateArray: struct {
        dest: InstructionOperator,
        elements: []InstructionOperator,
    },
    GetIndex: struct {
        dest: InstructionOperator,
        array: InstructionOperator,
        index: InstructionOperator,
    },
    SetIndex: struct {
        array: InstructionOperator,
        index: InstructionOperator,
        value: InstructionOperator,
    },

    // Built-ins
    Print: struct { value: ValueMHIR },
    Assert: struct { value: ValueMHIR },
};
