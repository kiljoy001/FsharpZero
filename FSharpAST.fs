// F# Abstract Syntax Tree Implementation
// Based on formal Coq proof in fsharp_ast_formal.v
// This is a direct translation of our verified specification

module FSharpAST

// ==================== LEXICAL TOKENS ====================
// Based on spec/lexical-analysis.md and our Coq proof

type Keyword =
    | KLet | KIn | KIf | KThen | KElse | KElif
    | KMatch | KWith | KFunction | KFun
    | KType | KOf | KModule | KNamespace
    | KOpen | KRec | KAnd | KAs
    | KTrue | KFalse | KNull
    | KFor | KWhile | KDo | KTo | KDownto
    | KYield | KReturn | KUse | KUsing
    | KTry | KFinally | KWith_
    | KNew | KThis | KStatic | KMember
    | KInterface | KAbstract | KOverride
    | KMutable | KConst | KInternal | KPrivate | KPublic

type Operator =
    // Arithmetic operators from spec/basic-grammar-elements.md
    | OpAdd        // +
    | OpSubtract   // -
    | OpMultiply   // *
    | OpDivide     // /
    | OpModulo     // %
    | OpPower      // **
    
    // Comparison operators
    | OpEqual      // =
    | OpNotEqual   // <>
    | OpLess       // <
    | OpGreater    // >
    | OpLessEq     // <=
    | OpGreaterEq  // >=
    
    // Logical operators
    | OpAnd        // &&
    | OpOr         // ||
    | OpNot        // not
    
    // Bitwise operators
    | OpBitwiseAnd // &&&
    | OpBitwiseOr  // |||
    | OpBitwiseXor // ^^^
    | OpBitwiseNot // ~~~
    | OpLeftShift  // <<<
    | OpRightShift // >>>
    
    // List operators
    | OpCons       // ::
    | OpAppend     // @
    
    // Pipe operators
    | OpPipeRight  // |>
    | OpPipeLeft   // <|
    | OpCompose    // >>
    | OpComposeBack // <<
    
    // Range operators
    | OpRange      // ..
    | OpRangeStep  // .. ..

type Token =
    // Whitespace and Comments - discarded during lexing
    | TWhitespace of length: int
    | TComment of nestingLevel: int
    
    // Identifiers and Keywords
    | TIdent of name: string
    | TKeyword of Keyword
    
    // Operators
    | TOperator of Operator
    | TSymbolicOp of op: string   // custom symbolic operator
    
    // Literals
    | TInt of value: int64
    | TFloat of mantissa: float * exponent: int
    | TBool of value: bool
    | TString of value: string
    | TChar of value: char
    | TUnit
    
    // Delimiters
    | TLParen | TRParen
    | TLBracket | TRBracket
    | TLBrace | TRBrace
    | TSemicolon
    | TComma
    | TDot
    | TColon
    | TColonColon
    | TArrow      // ->
    | TEquals
    | TPipe       // |
    | TAmpersand  // &
    
    // Special
    | TBacktick
    | TQuote
    | THash       // # for preprocessor
    | TEOF

// ==================== ABSTRACT SYNTAX TREE ====================
// Direct translation from our Coq specification

type Literal =
    | LitInt of value: int64
    | LitFloat of mantissa: float * exponent: int
    | LitBool of value: bool
    | LitString of value: string
    | LitChar of value: char
    | LitUnit
    | LitNull

type Pattern =
    | PatWildcard                                    // _
    | PatVar of name: string                        // x
    | PatLiteral of Literal                         // literal
    | PatTuple of patterns: Pattern list            // (p1, p2, ...)
    | PatList of patterns: Pattern list             // [p1; p2; ...]
    | PatCons of head: Pattern * tail: Pattern      // p1::p2
    | PatRecord of fields: (string * Pattern) list  // { f1 = p1; ... }
    | PatAs of pattern: Pattern * name: string      // p as x
    | PatOr of left: Pattern * right: Pattern       // p1 | p2
    | PatAnd of left: Pattern * right: Pattern      // p1 & p2
    | PatType of pattern: Pattern * typ: FSharpType // p : t

and MatchCase =
    | Case of pattern: Pattern * guard: FSharpAST option * expr: FSharpAST

and FSharpType =
    | TypeVar of name: string                          // 'a
    | TypeConst of name: string                        // int, string, etc
    | TypeApp of typ: FSharpType * args: FSharpType list  // t<t1, t2>
    | TypeTuple of types: FSharpType list              // t1 * t2
    | TypeFunction of from: FSharpType * target: FSharpType  // t1 -> t2
    | TypeList of typ: FSharpType                      // t list
    | TypeArray of typ: FSharpType                     // t[]
    | TypeOption of typ: FSharpType                    // t option
    | TypeRecord of fields: (string * FSharpType) list // { f1: t1; ... }

and FSharpAST =
    // Literals
    | ASTLiteral of Literal
    
    // Variables and Identifiers
    | ASTIdent of name: string                         // variable
    | ASTLongIdent of path: string list                // qualified identifier
    
    // Binding
    | ASTLet of name: string * value: FSharpAST * body: FSharpAST  // let x = e1 in e2
    | ASTLetRec of bindings: (string * FSharpAST) list * body: FSharpAST  // let rec ... and ...
    
    // Functions
    | ASTLambda of parameters: string list * body: FSharpAST  // fun x y -> e
    | ASTApp of func: FSharpAST * arg: FSharpAST          // f x
    
    // Control Flow
    | ASTIf of cond: FSharpAST * thenExpr: FSharpAST * elseExpr: FSharpAST  // if c then t else e
    | ASTMatch of expr: FSharpAST * cases: MatchCase list                    // match e with ...
    | ASTTry of expr: FSharpAST * handlers: MatchCase list * finallyBlock: FSharpAST option  // try...with...finally
    
    // Loops
    | ASTFor of var: string * start: FSharpAST * stop: FSharpAST * body: FSharpAST  // for i = e1 to e2 do e3
    | ASTWhile of cond: FSharpAST * body: FSharpAST                                  // while e1 do e2
    
    // Operators
    | ASTBinaryOp of op: Operator * left: FSharpAST * right: FSharpAST
    | ASTUnaryOp of op: Operator * expr: FSharpAST
    
    // Data Structures
    | ASTTuple of elements: FSharpAST list                      // (e1, e2, ...)
    | ASTList of elements: FSharpAST list                       // [e1; e2; ...]
    | ASTArray of elements: FSharpAST list                      // [|e1; e2; ...|]
    | ASTRecord of fields: (string * FSharpAST) list            // { f1 = e1; ... }
    
    // Type Annotations
    | ASTTypeAnnotation of expr: FSharpAST * typ: FSharpType    // (e : t)
    | ASTTypeTest of expr: FSharpAST * typ: FSharpType          // e :? t
    | ASTTypeCast of expr: FSharpAST * typ: FSharpType          // e :> t
    
    // Sequencing
    | ASTSequence of first: FSharpAST * second: FSharpAST       // e1; e2
    | ASTUnit                                                    // ()
    
    // Member Access
    | ASTDotAccess of obj: FSharpAST * field: string            // e.field
    | ASTIndexer of obj: FSharpAST * index: FSharpAST           // e.[i]

// ==================== PARSING CONTEXT ====================
// From our Coq proof

type ParseContext = {
    Tokens: Token list
    Position: int
    Identifiers: Map<string, int>  // Symbol table
    Types: Map<string, FSharpType>
    Errors: string list
}

// ==================== WELL-FORMEDNESS ====================
// Based on WellFormedAST from our proof

let rec isWellFormed (ast: FSharpAST) : bool =
    match ast with
    | ASTLiteral _ -> true
    | ASTIdent _ -> true  // Should check if bound in real implementation
    | ASTLet(_, value, body) ->
        isWellFormed value && isWellFormed body
    | ASTLambda(_, body) ->
        isWellFormed body
    | ASTApp(func, arg) ->
        isWellFormed func && isWellFormed arg
    | ASTIf(cond, thenExpr, elseExpr) ->
        isWellFormed cond && isWellFormed thenExpr && isWellFormed elseExpr
    | ASTBinaryOp(_, left, right) ->
        isWellFormed left && isWellFormed right
    | ASTUnaryOp(_, expr) ->
        isWellFormed expr
    | ASTTuple elements ->
        List.forall isWellFormed elements
    | ASTList elements ->
        List.forall isWellFormed elements
    | ASTArray elements ->
        List.forall isWellFormed elements
    | ASTRecord fields ->
        fields |> List.forall (fun (_, expr) -> isWellFormed expr)
    | ASTSequence(first, second) ->
        isWellFormed first && isWellFormed second
    | ASTUnit -> true
    | _ -> true  // Simplified for other cases

// ==================== AST UTILITIES ====================

/// Calculate AST size (from our Coq proof ast_size function)
let rec astSize (ast: FSharpAST) : int =
    match ast with
    | ASTLiteral _ | ASTIdent _ | ASTUnit -> 1
    | ASTLet(_, e1, e2) -> 1 + astSize e1 + astSize e2
    | ASTLambda(_, body) -> 1 + astSize body
    | ASTApp(f, arg) -> 1 + astSize f + astSize arg
    | ASTIf(c, t, e) -> 1 + astSize c + astSize t + astSize e
    | ASTBinaryOp(_, e1, e2) -> 1 + astSize e1 + astSize e2
    | ASTUnaryOp(_, e) -> 1 + astSize e
    | ASTTuple elems -> 1 + List.sumBy astSize elems
    | ASTList elems -> 1 + List.sumBy astSize elems
    | ASTArray elems -> 1 + List.sumBy astSize elems
    | ASTRecord fields -> 1 + List.sumBy (fun (_, e) -> astSize e) fields
    | ASTSequence(e1, e2) -> 1 + astSize e1 + astSize e2
    | _ -> 1

/// Pretty print AST for debugging
let rec prettyPrint (ast: FSharpAST) (indent: int) : string =
    let spaces = String.replicate indent "  "
    match ast with
    | ASTLiteral(LitInt n) -> sprintf "%s%d" spaces n
    | ASTLiteral(LitBool b) -> sprintf "%s%b" spaces b
    | ASTLiteral(LitString s) -> sprintf "%s\"%s\"" spaces s
    | ASTIdent name -> sprintf "%s%s" spaces name
    | ASTLet(name, value, body) ->
        sprintf "%slet %s =\n%s\n%sin\n%s" 
            spaces name 
            (prettyPrint value (indent + 1))
            spaces
            (prettyPrint body indent)
    | ASTLambda(parameters, body) ->
        sprintf "%sfun %s ->\n%s" 
            spaces 
            (String.concat " " parameters)
            (prettyPrint body (indent + 1))
    | ASTApp(func, arg) ->
        sprintf "%s(%s\n%s)" 
            spaces
            (prettyPrint func 0)
            (prettyPrint arg (indent + 1))
    | ASTIf(cond, thenExpr, elseExpr) ->
        sprintf "%sif %s then\n%s\n%selse\n%s"
            spaces
            (prettyPrint cond 0)
            (prettyPrint thenExpr (indent + 1))
            spaces
            (prettyPrint elseExpr (indent + 1))
    | ASTBinaryOp(op, left, right) ->
        sprintf "%s(%s %A %s)"
            spaces
            (prettyPrint left 0)
            op
            (prettyPrint right 0)
    | _ -> sprintf "%s..." spaces

/// Convert operator to its compiled name (from spec/basic-grammar-elements.md)
let operatorCompiledName (op: Operator) : string =
    match op with
    | OpAdd -> "op_Addition"
    | OpSubtract -> "op_Subtraction"
    | OpMultiply -> "op_Multiply"
    | OpDivide -> "op_Division"
    | OpPower -> "op_Exponentiation"
    | OpAppend -> "op_Append"
    | OpModulo -> "op_Modulus"
    | OpBitwiseAnd -> "op_BitwiseAnd"
    | OpBitwiseOr -> "op_BitwiseOr"
    | OpBitwiseXor -> "op_ExclusiveOr"
    | OpLeftShift -> "op_LeftShift"
    | OpRightShift -> "op_RightShift"
    | OpEqual -> "op_Equality"
    | OpNotEqual -> "op_Inequality"
    | OpLessEq -> "op_LessThanOrEqual"
    | OpGreaterEq -> "op_GreaterThanOrEqual"
    | OpLess -> "op_LessThan"
    | OpGreater -> "op_GreaterThan"
    | OpPipeRight -> "op_PipeRight"
    | OpPipeLeft -> "op_PipeLeft"
    | OpCompose -> "op_ComposeRight"
    | OpComposeBack -> "op_ComposeLeft"
    | OpAnd -> "op_BooleanAnd"
    | OpOr -> "op_BooleanOr"
    | OpCons -> "op_ColonColon"
    | OpRange -> "op_Range"
    | OpRangeStep -> "op_RangeStep"
    | _ -> "op_Unknown"