// F# Parser Implementation  
// Based on spec/expressions.md and our Coq proof
// Builds AST from token stream

module FSharpParser

open FSharpAST
open FSharpLexer

// ==================== PARSER STATE ====================

type ParseResult<'T> = Result<'T, string>

type ParserState = {
    Tokens: Token list
    Position: int
    Errors: string list
}

// ==================== PARSER COMBINATORS ====================

/// Peek at current token without consuming
let peek (state: ParserState) : Token option =
    if state.Position < state.Tokens.Length then
        Some state.Tokens.[state.Position]
    else
        None

/// Advance to next token
let advance (state: ParserState) : ParserState =
    { state with Position = state.Position + 1 }

/// Check if current token matches expected
let expect (state: ParserState) (expected: Token) : bool =
    match peek state with
    | Some token -> token = expected
    | None -> false

/// Consume expected token or return error
let consume (state: ParserState) (expected: Token) : ParseResult<ParserState> =
    match peek state with
    | Some token when token = expected ->
        Ok (advance state)
    | Some token ->
        Error (sprintf "Expected %A but got %A at position %d" expected token state.Position)
    | None ->
        Error (sprintf "Unexpected end of input, expected %A" expected)

/// Try to consume token, return new state if successful
let tryConsume (state: ParserState) (token: Token) : ParserState option =
    if expect state token then
        Some (advance state)
    else
        None

/// Parse with error recovery
let tryParse (parser: ParserState -> ParseResult<'T * ParserState>) (state: ParserState) : ParseResult<'T * ParserState> =
    parser state

// ==================== LITERAL PARSING ====================

let parseLiteral (state: ParserState) : ParseResult<Literal * ParserState> =
    match peek state with
    | Some (TInt n) ->
        Ok (LitInt n, advance state)
    | Some (TFloat (m, e)) ->
        Ok (LitFloat (m, e), advance state)  
    | Some (TBool b) ->
        Ok (LitBool b, advance state)
    | Some (TString s) ->
        Ok (LitString s, advance state)
    | Some (TChar c) ->
        Ok (LitChar c, advance state)
    | Some TUnit ->
        Ok (LitUnit, advance state)
    | Some (TKeyword KNull) ->
        Ok (LitNull, advance state)
    | Some token ->
        Error (sprintf "Expected literal but got %A" token)
    | None ->
        Error "Unexpected end of input in literal"

// ==================== PATTERN PARSING ====================

let rec parsePattern (state: ParserState) : ParseResult<Pattern * ParserState> =
    match peek state with
    | Some (TIdent "_") ->
        // Wildcard pattern
        Ok (PatWildcard, advance state)
    
    | Some (TIdent name) ->
        // Variable pattern
        Ok (PatVar name, advance state)
    
    | Some (TInt _) | Some (TFloat _) | Some (TBool _) | Some (TString _) | Some (TChar _) | Some TUnit ->
        // Literal pattern
        match parseLiteral state with
        | Ok (lit, newState) -> Ok (PatLiteral lit, newState)
        | Error msg -> Error msg
    
    | Some TLParen ->
        // Tuple pattern or parenthesized pattern
        parseTuplePattern (advance state)
    
    | Some TLBracket ->
        // List pattern
        parseListPattern (advance state)
    
    | _ ->
        Error "Expected pattern"

and parseTuplePattern (state: ParserState) : ParseResult<Pattern * ParserState> =
    // Parse first pattern
    match parsePattern state with
    | Error msg -> Error msg
    | Ok (firstPat, state1) ->
        // Check if it's just parenthesized or a tuple
        match peek state1 with
        | Some TComma ->
            // It's a tuple - parse remaining patterns
            parsePatternList (advance state1) [firstPat]
        | Some TRParen ->
            // Just parenthesized pattern
            Ok (firstPat, advance state1)
        | _ ->
            Error "Expected ',' or ')' in tuple pattern"

and parsePatternList (state: ParserState) (acc: Pattern list) : ParseResult<Pattern * ParserState> =
    match parsePattern state with
    | Error msg -> Error msg
    | Ok (pat, state1) ->
        let newAcc = pat :: acc
        match peek state1 with
        | Some TComma ->
            parsePatternList (advance state1) newAcc
        | Some TRParen ->
            Ok (PatTuple (List.rev newAcc), advance state1)
        | _ ->
            Error "Expected ',' or ')' in pattern list"

and parseListPattern (state: ParserState) : ParseResult<Pattern * ParserState> =
    // Parse patterns separated by semicolons
    let rec parseListItems state acc =
        match peek state with
        | Some TRBracket ->
            Ok (PatList (List.rev acc), advance state)
        | _ ->
            match parsePattern state with
            | Error msg -> Error msg
            | Ok (pat, state1) ->
                let newAcc = pat :: acc
                match peek state1 with
                | Some TSemicolon ->
                    parseListItems (advance state1) newAcc
                | Some TRBracket ->
                    Ok (PatList (List.rev newAcc), advance state1)
                | _ ->
                    Error "Expected ';' or ']' in list pattern"
    
    parseListItems state []

// ==================== EXPRESSION PARSING ====================

let rec parseExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    parseIfExpression state

and parseIfExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    match peek state with
    | Some (TKeyword KIf) ->
        // Parse: if condition then thenExpr else elseExpr
        let state1 = advance state
        match parseExpression state1 with
        | Error msg -> Error msg
        | Ok (cond, state2) ->
            match consume state2 (TKeyword KThen) with
            | Error msg -> Error msg
            | Ok state3 ->
                match parseExpression state3 with
                | Error msg -> Error msg
                | Ok (thenExpr, state4) ->
                    match consume state4 (TKeyword KElse) with
                    | Error msg -> Error msg
                    | Ok state5 ->
                        match parseExpression state5 with
                        | Error msg -> Error msg
                        | Ok (elseExpr, state6) ->
                            Ok (ASTIf (cond, thenExpr, elseExpr), state6)
    | _ ->
        parseLetExpression state

and parseLetExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    match peek state with
    | Some (TKeyword KLet) ->
        // Parse: let name = value in body
        let state1 = advance state
        match peek state1 with
        | Some (TIdent name) ->
            let state2 = advance state1
            match consume state2 TEquals with
            | Error msg -> Error msg
            | Ok state3 ->
                match parseExpression state3 with
                | Error msg -> Error msg
                | Ok (value, state4) ->
                    match consume state4 (TKeyword KIn) with
                    | Error msg -> Error msg
                    | Ok state5 ->
                        match parseExpression state5 with
                        | Error msg -> Error msg
                        | Ok (body, state6) ->
                            Ok (ASTLet (name, value, body), state6)
        | _ ->
            Error "Expected identifier after 'let'"
    | _ ->
        parseLambdaExpression state

and parseLambdaExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    match peek state with
    | Some (TKeyword KFun) ->
        // Parse: fun param1 param2 -> body
        let state1 = advance state
        
        let rec parseParams state acc =
            match peek state with
            | Some (TIdent name) ->
                parseParams (advance state) (name :: acc)
            | Some TArrow ->
                (List.rev acc, advance state)
            | _ ->
                (List.rev acc, state)
        
        let (parameters, state2) = parseParams state1 []
        
        match parseExpression state2 with
        | Error msg -> Error msg
        | Ok (body, state3) ->
            Ok (ASTLambda (parameters, body), state3)
    | _ ->
        parseApplicationExpression state

and parseApplicationExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    // Parse function application (left-associative)
    match parseAtomicExpression state with
    | Error msg -> Error msg
    | Ok (func, state1) ->
        let rec parseApplications func state =
            match parseAtomicExpression state with
            | Ok (arg, state2) ->
                parseApplications (ASTApp (func, arg)) state2
            | Error _ ->
                (func, state)
        
        let (result, finalState) = parseApplications func state1
        Ok (result, finalState)

and parseAtomicExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    match peek state with
    | Some (TInt _) | Some (TFloat _) | Some (TBool _) | Some (TString _) | Some (TChar _) | Some TUnit ->
        // Literal expression
        match parseLiteral state with
        | Ok (lit, newState) -> Ok (ASTLiteral lit, newState)
        | Error msg -> Error msg
    
    | Some (TIdent name) ->
        // Variable reference
        Ok (ASTIdent name, advance state)
    
    | Some TLParen ->
        // Parenthesized expression or tuple
        parseParenthesizedExpression (advance state)
    
    | Some TLBracket ->
        // List expression
        parseListExpression (advance state)
    
    | Some TUnit ->
        // Unit literal
        Ok (ASTUnit, advance state)
    
    | _ ->
        Error "Expected atomic expression"

and parseParenthesizedExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    match parseExpression state with
    | Error msg -> Error msg
    | Ok (expr, state1) ->
        match peek state1 with
        | Some TComma ->
            // Tuple expression
            parseTupleExpression (advance state1) [expr]
        | Some TRParen ->
            // Just parenthesized
            Ok (expr, advance state1)
        | _ ->
            Error "Expected ',' or ')' in parenthesized expression"

and parseTupleExpression (state: ParserState) (acc: FSharpAST list) : ParseResult<FSharpAST * ParserState> =
    match parseExpression state with
    | Error msg -> Error msg
    | Ok (expr, state1) ->
        let newAcc = expr :: acc
        match peek state1 with
        | Some TComma ->
            parseTupleExpression (advance state1) newAcc
        | Some TRParen ->
            Ok (ASTTuple (List.rev newAcc), advance state1)
        | _ ->
            Error "Expected ',' or ')' in tuple expression"

and parseListExpression (state: ParserState) : ParseResult<FSharpAST * ParserState> =
    let rec parseListItems state acc =
        match peek state with
        | Some TRBracket ->
            Ok (ASTList (List.rev acc), advance state)
        | _ ->
            match parseExpression state with
            | Error msg -> Error msg
            | Ok (expr, state1) ->
                let newAcc = expr :: acc
                match peek state1 with
                | Some TSemicolon ->
                    parseListItems (advance state1) newAcc
                | Some TRBracket ->
                    Ok (ASTList (List.rev newAcc), advance state1)
                | _ ->
                    Error "Expected ';' or ']' in list expression"
    
    parseListItems state []

// ==================== MAIN PARSING FUNCTIONS ====================

/// Parse token stream into AST
let parse (tokens: Token list) : ParseResult<FSharpAST> =
    let initialState = {
        Tokens = tokens
        Position = 0
        Errors = []
    }
    
    match parseExpression initialState with
    | Ok (ast, finalState) ->
        // Check for remaining tokens
        if finalState.Position >= finalState.Tokens.Length - 1 then  // -1 for EOF
            Ok ast
        else
            Error (sprintf "Unexpected tokens remaining at position %d" finalState.Position)
    | Error msg ->
        Error msg

/// Parse string input directly
let parseString (input: string) : ParseResult<FSharpAST> =
    let tokens = lex input
    if isValidTokenStream tokens then
        parse tokens
    else
        Error "Invalid token stream"

// ==================== PARSER VALIDATION ====================
// Based on our Coq proof parser_preserves_wellformedness

let validateParsedAST (ast: FSharpAST) : bool =
    isWellFormed ast

/// Parse with validation
let parseWithValidation (tokens: Token list) : ParseResult<FSharpAST> =
    match parse tokens with
    | Ok ast ->
        if validateParsedAST ast then
            Ok ast
        else
            Error "Parsed AST is not well-formed"
    | Error msg -> Error msg

// ==================== DEBUGGING UTILITIES ====================

let parseDebug (input: string) : unit =
    printfn "=== LEXING ==="
    let tokens = lex input
    printTokens tokens
    
    printfn "\n=== PARSING ==="
    match parseString input with
    | Ok ast ->
        printfn "Successfully parsed:"
        printfn "%s" (prettyPrint ast 0)
        printfn "\nAST size: %d" (astSize ast)
        printfn "Well-formed: %b" (isWellFormed ast)
    | Error msg ->
        printfn "Parse error: %s" msg