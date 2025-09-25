mod tokenizer;

use std::fmt;

// --- Bytecode Definition ---

/// Represents the different instructions our VM can execute.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    /// Load a constant from the constant pool into a register.
    /// Operand: destination register, constant index
    Constant,
    /// Add the values in two registers and store the result in a third register.
    /// Operands: source register 1, source register 2, destination register
    Add,
    /// Subtract the value in the second register from the first and store the result.
    /// Operands: source register 1, source register 2, destination register
    Subtract,
    /// Multiply the values in two registers and store the result.
    /// Operands: source register 1, source register 2, destination register
    Multiply,
    /// Divide the value in the first register by the second and store the result.
    /// Operands: source register 1, source register 2, destination register
    Divide,
    /// Halts the execution of the VM.
    Halt,
}

impl From<u8> for OpCode {
    fn from(byte: u8) -> Self {
        unsafe { std::mem::transmute(byte) }
    }
}

/// Represents a chunk of bytecode and its associated data.
pub struct Chunk {
    pub code: Vec<u8>,
    pub constants: Vec<Value>,
}

impl Chunk {
    pub fn new() -> Self {
        Chunk {
            code: Vec::new(),
            constants: Vec::new(),
        }
    }

    /// Writes a byte to the bytecode chunk.
    pub fn write(&mut self, byte: u8) {
        self.code.push(byte);
    }

    /// Adds a constant to the constant pool and returns its index.
    pub fn add_constant(&mut self, value: Value) -> u8 {
        self.constants.push(value);
        (self.constants.len() - 1) as u8
    }
}

/// Represents a value in our language. For now, we only support numbers.
#[derive(Debug, Clone, Copy)]
pub enum Value {
    Number(f64),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Number(n) => write!(f, "{}", n),
        }
    }
}

// --- Virtual Machine ---

const NUM_REGISTERS: usize = 256;

/// The virtual machine that executes the bytecode.
pub struct VM<'a> {
    chunk: &'a Chunk,
    ip: usize, // instruction pointer
    registers: [Value; NUM_REGISTERS],
}

impl<'a> VM<'a> {
    pub fn new(chunk: &'a Chunk) -> Self {
        VM {
            chunk,
            ip: 0,
            registers: [Value::Number(0.0); NUM_REGISTERS],
        }
    }

    /// The main execution loop of the interpreter.
    pub fn run(&mut self) -> Result<(), String> {
        loop {
            let instruction = self.read_byte();
            match OpCode::from(instruction) {
                OpCode::Constant => {
                    let dest = self.read_byte() as usize;
                    let const_index = self.read_byte() as usize;
                    self.registers[dest] = self.chunk.constants[const_index];
                }
                OpCode::Add => {
                    let a_reg = self.read_byte() as usize;
                    let b_reg = self.read_byte() as usize;
                    let dest_reg = self.read_byte() as usize;
                    if let (Value::Number(a), Value::Number(b)) = (self.registers[a_reg], self.registers[b_reg]) {
                        self.registers[dest_reg] = Value::Number(a + b);
                    } else {
                        return Err("Operands must be numbers.".to_string());
                    }
                }
                OpCode::Subtract => {
                    let a_reg = self.read_byte() as usize;
                    let b_reg = self.read_byte() as usize;
                    let dest_reg = self.read_byte() as usize;
                    if let (Value::Number(a), Value::Number(b)) = (self.registers[a_reg], self.registers[b_reg]) {
                        self.registers[dest_reg] = Value::Number(a - b);
                    } else {
                        return Err("Operands must be numbers.".to_string());
                    }
                }
                OpCode::Multiply => {
                    let a_reg = self.read_byte() as usize;
                    let b_reg = self.read_byte() as usize;
                    let dest_reg = self.read_byte() as usize;
                    if let (Value::Number(a), Value::Number(b)) = (self.registers[a_reg], self.registers[b_reg]) {
                        self.registers[dest_reg] = Value::Number(a * b);
                    } else {
                        return Err("Operands must be numbers.".to_string());
                    }
                }
                OpCode::Divide => {
                    let a_reg = self.read_byte() as usize;
                    let b_reg = self.read_byte() as usize;
                    let dest_reg = self.read_byte() as usize;
                    if let (Value::Number(a), Value::Number(b)) = (self.registers[a_reg], self.registers[b_reg]) {
                        self.registers[dest_reg] = Value::Number(a / b);
                    } else {
                        return Err("Operands must be numbers.".to_string());
                    }
                }
                OpCode::Halt => {
                    return Ok(());
                }
            }
        }
    }

    /// Reads a single byte from the bytecode and advances the instruction pointer.
    fn read_byte(&mut self) -> u8 {
        let byte = self.chunk.code[self.ip];
        self.ip += 1;
        byte
    }
}

// --- Main Execution ---

fn main() {
    let mut chunk = Chunk::new();

    // Example: (1.2 + 3.4) * 5.6 / 2.0
    // Load constants
    let c1 = chunk.add_constant(Value::Number(1.2));
    chunk.write(OpCode::Constant as u8);
    chunk.write(0); // destination register
    chunk.write(c1);

    let c2 = chunk.add_constant(Value::Number(3.4));
    chunk.write(OpCode::Constant as u8);
    chunk.write(1); // destination register
    chunk.write(c2);

    // Add
    chunk.write(OpCode::Add as u8);
    chunk.write(0); // source 1
    chunk.write(1); // source 2
    chunk.write(2); // destination

    // Load more constants
    let c3 = chunk.add_constant(Value::Number(5.6));
    chunk.write(OpCode::Constant as u8);
    chunk.write(3);
    chunk.write(c3);

    // Multiply
    chunk.write(OpCode::Multiply as u8);
    chunk.write(2);
    chunk.write(3);
    chunk.write(4);

    let c4 = chunk.add_constant(Value::Number(2.0));
    chunk.write(OpCode::Constant as u8);
    chunk.write(5);
    chunk.write(c4);

    // Divide
    chunk.write(OpCode::Divide as u8);
    chunk.write(4);
    chunk.write(5);
    chunk.write(6);

    chunk.write(OpCode::Halt as u8);

    let mut vm = VM::new(&chunk);
    match vm.run() {
        Ok(()) => {
            println!("Execution finished successfully.");
            println!("Result: {}", vm.registers[6]);
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}