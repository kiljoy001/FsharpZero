// F# to x86-64 Code Generator
// Based on Intel 64 and IA-32 Architectures Software Developer's Manual
// Converts F# AST to native x86-64 machine code

module FSharpCodeGen

open FSharpAST
open System
open System.Collections.Generic

// ==================== x86-64 INSTRUCTION ENCODING ====================
// Based on Intel 64 manual section 2.1

type Register =
    | RAX = 0 | RCX = 1 | RDX = 2 | RBX = 3
    | RSP = 4 | RBP = 5 | RSI = 6 | RDI = 7
    | R8 = 8  | R9 = 9  | R10 = 10 | R11 = 11
    | R12 = 12 | R13 = 13 | R14 = 14 | R15 = 15

type Instruction =
    // Move instructions - Intel manual Table 2-4
    | MOV_REG_IMM64 of reg: Register * imm: int64    // 48 B8+r mov RAX, imm64
    | MOV_REG_REG of dst: Register * src: Register   // 48 89 /r mov r/m64, r64
    | MOV_MEM_REG of addr: Register * src: Register  // 48 89 /r mov [addr], src
    | MOV_MEM_IMM16 of addr: Register * imm: int16   // 66 C7 /0 mov word [addr], imm16
    
    // Arithmetic instructions - Intel manual Section 4.1
    | ADD_REG_REG of dst: Register * src: Register   // 48 01 /r add r/m64, r64
    | SUB_REG_REG of dst: Register * src: Register   // 48 29 /r sub r/m64, r64
    | MUL_REG of reg: Register                       // 48 F7 /4 mul r/m64
    | DIV_REG of reg: Register                       // 48 F7 /6 div r/m64
    
    // Compare and jump - Intel manual Section 4.1
    | CMP_REG_REG of reg1: Register * reg2: Register // 48 39 /r cmp r/m64, r64
    | JE_REL32 of offset: int32                      // 0F 84 cd je rel32
    | JMP_REL32 of offset: int32                     // E9 cd jmp rel32
    
    // Stack operations - Intel manual Section 4.2
    | PUSH_REG of reg: Register                      // 50+r push r64
    | POP_REG of reg: Register                       // 58+r pop r64
    
    // Function calls - Intel manual Section 4.3
    | CALL_REL32 of offset: int32                    // E8 cd call rel32
    | RET                                            // C3 ret

// ==================== MACHINE CODE ENCODING ====================
// Direct implementation of Intel 64 instruction formats

/// REX prefix for 64-bit operations (Intel manual Section 2.2.1)
let rexPrefix (w: bool) (r: bool) (x: bool) (b: bool) : byte =
    let mutable prefix = 0x40uy
    if w then prefix <- prefix ||| 0x08uy  // REX.W bit
    if r then prefix <- prefix ||| 0x04uy  // REX.R bit  
    if x then prefix <- prefix ||| 0x02uy  // REX.X bit
    if b then prefix <- prefix ||| 0x01uy  // REX.B bit
    prefix

/// ModR/M byte encoding (Intel manual Section 2.1.5)
let modrmByte (mode: byte) (reg: byte) (rm: byte) : byte =
    (mode <<< 6) ||| (reg <<< 3) ||| rm

/// Encode register number with REX handling
let encodeRegister (reg: Register) : byte * bool =
    let regNum = byte (int reg)
    if regNum >= 8uy then
        (regNum - 8uy, true)  // Extended register, needs REX.R or REX.B
    else
        (regNum, false)

/// Convert 64-bit immediate to little-endian bytes
let int64ToBytes (value: int64) : byte array =
    BitConverter.GetBytes(value)

/// Convert 32-bit immediate to little-endian bytes  
let int32ToBytes (value: int32) : byte array =
    BitConverter.GetBytes(value)

/// Encode single instruction to machine code
let encodeInstruction (instr: Instruction) : byte array =
    match instr with
    
    // MOV r64, imm64 - Intel manual: 48 B8+r mov RAX,imm64
    | MOV_REG_IMM64(reg, imm) ->
        let (regNum, needsRexB) = encodeRegister reg
        let rex = rexPrefix true false false needsRexB  // REX.W=1 for 64-bit
        let opcode = 0xB8uy + regNum
        Array.concat [|
            [| rex; opcode |]
            int64ToBytes imm
        |]
    
    // MOV r/m64, r64 - Intel manual: 48 89 /r
    | MOV_REG_REG(dst, src) ->
        let (dstNum, needsRexB) = encodeRegister dst
        let (srcNum, needsRexR) = encodeRegister src
        let rex = rexPrefix true needsRexR false needsRexB
        let modrm = modrmByte 3uy srcNum dstNum  // mode=11 (register direct)
        [| rex; 0x89uy; modrm |]
    
    // MOV [addr], src - Intel manual: 48 89 /r
    | MOV_MEM_REG(addr, src) ->
        let (addrNum, needsRexB) = encodeRegister addr
        let (srcNum, needsRexR) = encodeRegister src
        let rex = rexPrefix true needsRexR false needsRexB
        let modrm = modrmByte 0uy srcNum addrNum  // mode=00 (memory indirect)
        [| rex; 0x89uy; modrm |]
    
    // MOV word [addr], imm16 - Intel manual: 66 C7 /0
    | MOV_MEM_IMM16(addr, imm) ->
        let (addrNum, needsRexB) = encodeRegister addr
        let rex = rexPrefix false false false needsRexB
        let modrm = modrmByte 0uy 0uy addrNum  // mode=00, reg=000 for immediate
        Array.concat [|
            [| 0x66uy; rex; 0xC7uy; modrm |]  // 16-bit prefix + instruction
            BitConverter.GetBytes(imm).[0..1]  // 16-bit immediate
        |]
    
    // ADD r/m64, r64 - Intel manual: 48 01 /r
    | ADD_REG_REG(dst, src) ->
        let (dstNum, needsRexB) = encodeRegister dst
        let (srcNum, needsRexR) = encodeRegister src
        let rex = rexPrefix true needsRexR false needsRexB
        let modrm = modrmByte 3uy srcNum dstNum
        [| rex; 0x01uy; modrm |]
    
    // SUB r/m64, r64 - Intel manual: 48 29 /r
    | SUB_REG_REG(dst, src) ->
        let (dstNum, needsRexB) = encodeRegister dst
        let (srcNum, needsRexR) = encodeRegister src
        let rex = rexPrefix true needsRexR false needsRexB
        let modrm = modrmByte 3uy srcNum dstNum
        [| rex; 0x29uy; modrm |]
    
    // CMP r/m64, r64 - Intel manual: 48 39 /r
    | CMP_REG_REG(reg1, reg2) ->
        let (reg1Num, needsRexB) = encodeRegister reg1
        let (reg2Num, needsRexR) = encodeRegister reg2
        let rex = rexPrefix true needsRexR false needsRexB
        let modrm = modrmByte 3uy reg2Num reg1Num
        [| rex; 0x39uy; modrm |]
    
    // Conditional jump JE rel32 - Intel manual: 0F 84 cd
    | JE_REL32(offset) ->
        Array.concat [|
            [| 0x0Fuy; 0x84uy |]
            int32ToBytes offset
        |]
    
    // Unconditional jump JMP rel32 - Intel manual: E9 cd
    | JMP_REL32(offset) ->
        Array.concat [|
            [| 0xE9uy |]
            int32ToBytes offset
        |]
    
    // PUSH r64 - Intel manual: 50+r
    | PUSH_REG(reg) ->
        let (regNum, needsRexB) = encodeRegister reg
        if needsRexB then
            let rex = rexPrefix false false false true
            [| rex; 0x50uy + regNum |]
        else
            [| 0x50uy + regNum |]
    
    // POP r64 - Intel manual: 58+r
    | POP_REG(reg) ->
        let (regNum, needsRexB) = encodeRegister reg
        if needsRexB then
            let rex = rexPrefix false false false true
            [| rex; 0x58uy + regNum |]
        else
            [| 0x58uy + regNum |]
    
    // CALL rel32 - Intel manual: E8 cd
    | CALL_REL32(offset) ->
        Array.concat [|
            [| 0xE8uy |]
            int32ToBytes offset
        |]
    
    // RET - Intel manual: C3
    | RET ->
        [| 0xC3uy |]
    
    // MUL and DIV need more complex encoding - simplified for now
    | MUL_REG(reg) ->
        let (regNum, needsRexB) = encodeRegister reg
        let rex = rexPrefix true false false needsRexB
        let modrm = modrmByte 3uy 4uy regNum  // /4 for MUL
        [| rex; 0xF7uy; modrm |]
    
    | DIV_REG(reg) ->
        let (regNum, needsRexB) = encodeRegister reg
        let rex = rexPrefix true false false needsRexB
        let modrm = modrmByte 3uy 6uy regNum  // /6 for DIV
        [| rex; 0xF7uy; modrm |]

// ==================== CODE GENERATION CONTEXT ====================

type CodeGenContext = {
    Instructions: Instruction list
    Labels: Map<string, int>
    Relocations: (int * string) list  // (offset, label)
    NextRegister: int
    StackOffset: int
}

let emptyContext = {
    Instructions = []
    Labels = Map.empty
    Relocations = []
    NextRegister = 0
    StackOffset = 0
}

/// Allocate next available register
let allocRegister (ctx: CodeGenContext) : CodeGenContext * Register =
    let reg = enum<Register> (ctx.NextRegister % 16)
    let newCtx = { ctx with NextRegister = ctx.NextRegister + 1 }
    (newCtx, reg)

/// Emit instruction
let emit (ctx: CodeGenContext) (instr: Instruction) : CodeGenContext =
    { ctx with Instructions = instr :: ctx.Instructions }

/// Add label at current position
let addLabel (ctx: CodeGenContext) (label: string) : CodeGenContext =
    let position = List.length ctx.Instructions
    { ctx with Labels = Map.add label position ctx.Labels }

// ==================== F# AST TO x86-64 COMPILATION ====================

let rec compileExpression (ctx: CodeGenContext) (ast: FSharpAST) : CodeGenContext * Register =
    match ast with
    
    // Compile integer literal: mov reg, immediate
    | ASTLiteral(LitInt value) ->
        let (ctx2, reg) = allocRegister ctx
        let ctx3 = emit ctx2 (MOV_REG_IMM64(reg, value))
        (ctx3, reg)
    
    // Compile boolean literal: mov reg, 0/1
    | ASTLiteral(LitBool value) ->
        let (ctx2, reg) = allocRegister ctx
        let imm = if value then 1L else 0L
        let ctx3 = emit ctx2 (MOV_REG_IMM64(reg, imm))
        (ctx3, reg)
    
    // Compile variable reference (simplified - load from stack)
    | ASTIdent name ->
        let (ctx2, reg) = allocRegister ctx
        // TODO: Implement proper symbol table lookup
        let ctx3 = emit ctx2 (MOV_REG_IMM64(reg, 0L))  // Placeholder
        (ctx3, reg)
    
    // Compile binary operations
    | ASTBinaryOp(OpAdd, left, right) ->
        let (ctx2, leftReg) = compileExpression ctx left
        let (ctx3, rightReg) = compileExpression ctx2 right
        let ctx4 = emit ctx3 (ADD_REG_REG(leftReg, rightReg))
        (ctx4, leftReg)  // Result in left register
    
    | ASTBinaryOp(OpSubtract, left, right) ->
        let (ctx2, leftReg) = compileExpression ctx left
        let (ctx3, rightReg) = compileExpression ctx2 right
        let ctx4 = emit ctx3 (SUB_REG_REG(leftReg, rightReg))
        (ctx4, leftReg)
    
    // Compile function application: call convention
    | ASTApp(func, arg) ->
        // Simplified: compile argument, then function, then call
        let (ctx2, argReg) = compileExpression ctx arg
        let (ctx3, funcReg) = compileExpression ctx2 func
        // Move argument to RDI (first parameter register)
        let ctx4 = emit ctx3 (MOV_REG_REG(Register.RDI, argReg))
        let ctx5 = emit ctx4 (CALL_REL32(0))  // TODO: Proper function addresses
        let (ctx6, resultReg) = allocRegister ctx5
        let ctx7 = emit ctx6 (MOV_REG_REG(resultReg, Register.RAX))  // Result in RAX
        (ctx7, resultReg)
    
    // Compile if expression: compare + conditional jump
    | ASTIf(cond, thenExpr, elseExpr) ->
        let (ctx2, condReg) = compileExpression ctx cond
        let (ctx3, zeroReg) = allocRegister ctx2
        let ctx4 = emit ctx3 (MOV_REG_IMM64(zeroReg, 0L))
        let ctx5 = emit ctx4 (CMP_REG_REG(condReg, zeroReg))
        
        // Jump to else if condition is false (zero)
        let ctx6 = emit ctx5 (JE_REL32(0))  // Placeholder offset
        let elseJumpPos = List.length ctx6.Instructions - 1
        
        // Compile then branch
        let (ctx7, thenReg) = compileExpression ctx6 thenExpr
        let ctx8 = emit ctx7 (JMP_REL32(0))  // Jump over else
        let endJumpPos = List.length ctx8.Instructions - 1
        
        // Compile else branch
        let elseLabel = sprintf "else_%d" elseJumpPos
        let ctx9 = addLabel ctx8 elseLabel
        let (ctx10, elseReg) = compileExpression ctx9 elseExpr
        
        // Both results should be in same register for consistent output
        let (ctx11, resultReg) = allocRegister ctx10
        let ctx12 = emit ctx11 (MOV_REG_REG(resultReg, thenReg))
        let ctx13 = emit ctx12 (MOV_REG_REG(resultReg, elseReg))
        
        (ctx13, resultReg)
    
    // Compile lambda: create function prologue
    | ASTLambda(parameters, body) ->
        let funcLabel = sprintf "lambda_%d" (List.length ctx.Instructions)
        let ctx2 = addLabel ctx funcLabel
        let ctx3 = emit ctx2 (PUSH_REG(Register.RBP))
        let ctx4 = emit ctx3 (MOV_REG_REG(Register.RBP, Register.RSP))
        
        // Compile function body
        let (ctx5, bodyReg) = compileExpression ctx4 body
        let ctx6 = emit ctx5 (MOV_REG_REG(Register.RAX, bodyReg))  // Return value
        
        // Function epilogue
        let ctx7 = emit ctx6 (MOV_REG_REG(Register.RSP, Register.RBP))
        let ctx8 = emit ctx7 (POP_REG(Register.RBP))
        let ctx9 = emit ctx8 RET
        
        // Return function address (simplified)
        let (ctx10, funcPtrReg) = allocRegister ctx9
        let ctx11 = emit ctx10 (MOV_REG_IMM64(funcPtrReg, 0L))  // TODO: Actual address
        (ctx11, funcPtrReg)
    
    // Default case
    | _ ->
        let (ctx2, reg) = allocRegister ctx
        let ctx3 = emit ctx2 (MOV_REG_IMM64(reg, 0L))
        (ctx3, reg)

// ==================== MAIN COMPILATION FUNCTIONS ====================

/// Compile F# AST to x86-64 instructions
let compile (ast: FSharpAST) : Instruction list =
    let (finalCtx, _) = compileExpression emptyContext ast
    List.rev finalCtx.Instructions

/// Compile F# AST to machine code bytes
let compileToMachineCode (ast: FSharpAST) : byte array =
    let instructions = compile ast
    instructions
    |> List.map encodeInstruction
    |> Array.concat

/// Compile F# source code directly to machine code
let compileStringToMachineCode (source: string) : Result<byte array, string> =
    try
        let tokens = FSharpLexer.lex source
        if FSharpLexer.isValidTokenStream tokens then
            match FSharpParser.parse tokens with
            | Ok ast ->
                if FSharpAST.isWellFormed ast then
                    Ok (compileToMachineCode ast)
                else
                    Error "AST is not well-formed"
            | Error msg -> Error ("Parse error: " + msg)
        else
            Error "Invalid token stream"
    with
    | ex -> Error ("Compilation error: " + ex.Message)

// ==================== ELF BINARY GENERATION ====================
// Minimal ELF64 header for Linux x86-64

type ELF64Header = {
    Magic: byte array        // 0x7F + "ELF"
    Class: byte             // 64-bit
    Data: byte              // Little endian  
    Version: byte           // Current version
    OSABI: byte             // Linux
    ABIVersion: byte        // 0
    Padding: byte array     // 7 bytes padding
    Type: uint16            // Executable
    Machine: uint16         // x86-64
    Version32: uint32       // Current version
    Entry: uint64           // Entry point
    PhOff: uint64           // Program header offset
    ShOff: uint64           // Section header offset
    Flags: uint32           // Processor flags
    EhSize: uint16          // ELF header size
    PhEntSize: uint16       // Program header entry size
    PhNum: uint16           // Number of program headers
    ShEntSize: uint16       // Section header entry size
    ShNum: uint16           // Number of section headers
    ShStrNdx: uint16        // String table index
}

let createELFHeader (codeSize: int) : byte array =
    let header = [|
        // ELF magic
        0x7Fuy; 0x45uy; 0x4Cuy; 0x46uy  // 0x7F + "ELF"
        0x02uy                          // 64-bit
        0x01uy                          // Little endian
        0x01uy                          // Current version
        0x00uy                          // Linux ABI
        0x00uy                          // ABI version
        0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy; 0x00uy  // Padding
    |]
    
    let rest = [|
        0x02uy; 0x00uy                  // Executable file
        0x3Euy; 0x00uy                  // x86-64
        0x01uy; 0x00uy; 0x00uy; 0x00uy  // Version
    |]
    
    Array.concat [| header; rest |]

/// Generate complete executable ELF binary
let generateExecutable (machineCode: byte array) : byte array =
    let elfHeader = createELFHeader machineCode.Length
    let entryPoint = 0x400000UL + uint64 elfHeader.Length
    
    // Simplified: just concatenate header + code
    // Real implementation would need proper program headers, etc.
    Array.concat [| elfHeader; machineCode |]

// ==================== DEBUGGING AND ANALYSIS ====================

let disassembleInstruction (instr: Instruction) : string =
    match instr with
    | MOV_REG_IMM64(reg, imm) -> sprintf "mov %A, 0x%X" reg imm
    | MOV_REG_REG(dst, src) -> sprintf "mov %A, %A" dst src
    | MOV_MEM_REG(addr, src) -> sprintf "mov [%A], %A" addr src
    | MOV_MEM_IMM16(addr, imm) -> sprintf "mov word [%A], 0x%X" addr imm
    | ADD_REG_REG(dst, src) -> sprintf "add %A, %A" dst src
    | SUB_REG_REG(dst, src) -> sprintf "sub %A, %A" dst src
    | CMP_REG_REG(r1, r2) -> sprintf "cmp %A, %A" r1 r2
    | JE_REL32(offset) -> sprintf "je %+d" offset
    | JMP_REL32(offset) -> sprintf "jmp %+d" offset
    | PUSH_REG(reg) -> sprintf "push %A" reg
    | POP_REG(reg) -> sprintf "pop %A" reg
    | CALL_REL32(offset) -> sprintf "call %+d" offset
    | RET -> "ret"
    | MUL_REG(reg) -> sprintf "mul %A" reg
    | DIV_REG(reg) -> sprintf "div %A" reg

let disassemble (instructions: Instruction list) : string =
    instructions
    |> List.mapi (fun i instr -> sprintf "%04d: %s" i (disassembleInstruction instr))
    |> String.concat "\n"

/// Print compilation analysis
let analyzeCompilation (source: string) : unit =
    printfn "=== F# to x86-64 Compilation Analysis ==="
    printfn "Source: %s" source
    
    match compileStringToMachineCode source with
    | Ok machineCode ->
        let tokens = FSharpLexer.lex source
        let ast = FSharpParser.parse tokens |> function | Ok ast -> ast | Error _ -> ASTLiteral(LitInt 0L)
        let instructions = compile ast
        
        printfn "\n--- Generated Assembly ---"
        printfn "%s" (disassemble instructions)
        
        printfn "\n--- Machine Code (hex) ---"
        let hexBytes = machineCode |> Array.map (sprintf "%02X") |> String.concat " "
        printfn "%s" hexBytes
        
        printfn "\n--- Statistics ---"
        printfn "Instructions: %d" instructions.Length
        printfn "Machine code size: %d bytes" machineCode.Length
        printfn "Code density: %.2f bytes/instruction" (float machineCode.Length / float instructions.Length)
        
    | Error msg ->
        printfn "❌ Compilation failed: %s" msg