#r "nuget: Scanrat"
open System
open ScanRat.ScanRat

type OptionBuilder () =
    member __.Bind(x, f) = Option.bind f x
    member __.Return(x) = Some x
    member __.ReturnFrom(x) = x
    member __.Zero() = None
let option = OptionBuilder()

type Var = string

type Store =
    | Empty
    | Block of Store * Var * int
    with
        override this.ToString() =
            match this with
            | Empty -> ""
            | Block(Empty, x, i) -> $"{x} = {i}"
            | Block(store, x, i) -> $"{store}, {x} = {i}"
module Store =
    let assign x i s =
        let rec inner = function
            | Block(s', x', _) when x = x' -> Block(s', x, i)
            | Block(s', y, j) -> Block(inner s', y, j)
            | Empty -> Block(s, x, i)
        inner s

type Prim = Plus | Minus | Times
    with
        override this.ToString() =
            match this with
            | Plus -> "+"
            | Minus -> "-"
            | Times -> "*"

type AExp =
    | Int of int
    | Var of Var
    | BinOp of AExp * Prim * AExp
    with
        override this.ToString() =
            let rec print = function
                | Int i -> $"{i}"
                | Var x -> $"{x}"
                | BinOp(_, op, _) as a -> "(" + printBinOp op a + ")"
            and printBinOp op = function
                | BinOp(a1, op', a2) when op = op' -> printBinOp op a1 + $" {op} " + printBinOp op a2
                | a -> print a
            print this

type LOp = And | Or
    with
        override this.ToString() =
            match this with
            | And -> "&&"
            | Or -> "||"

type Comp = Lt | Eq | Le
    with
        override this.ToString() =
            match this with
            | Lt -> "<"
            | Eq -> "="
            | Le -> "<="

type BExp =
    | Bool of bool
    | Not of BExp
    | LOp of BExp * LOp * BExp
    | Comp of AExp * Comp * AExp
    with
        override this.ToString() =
            let rec print = function
                | Bool true -> "true"
                | Bool false -> "false"
                | Not b -> $"!({b})"
                | LOp(_, op, _) as b -> "(" + printLOp op b + ")"
                | Comp(a1, op, a2) -> $"({a1} {op} {a2})"
            and printLOp op = function
                | LOp(b1, op', b2) when op = op' -> printLOp op b1 + $" {op} " + printLOp op b2
                | b -> print b
            print this

// 何の略？
type Com =
    | Skip
    (* x := a *)
    | Assign of Var * AExp
    (* c; c *)
    | Seq of Com * Com
    (* if b then c else c *)
    | If of BExp * Com * Com
    (* while(b) do c *)
    | While of BExp * Com
    with
        override this.ToString() =
            match this with
            | Skip -> "skip"
            | Assign(x, a) -> $"{x} := {a}"
            | Seq(c1, c2) -> $"{c1}; {c2}"
            | If(b, c1, c2) -> $"if {b} then {c1} else {c2}"
            | While(b, c) -> $"while ({b}) do {c}"

type Judge =
    (* c changes s1 to s2 *)
    | Changes of Com * Store * Store
    (* s |- a evalto i *)
    | EvalA of Store * AExp * int
    (* s |- b evalto bv *)
    | EvalB of Store * BExp * bool
    with
        override this.ToString() =
            let printStore = function
                | Block _ as s -> $"{s} "
                | Empty -> ""
            match this with
            | Changes(c, s1, s2) -> $"{c} changes {s1} to {s2}"
            | EvalA(s, a, i) -> $"{printStore s}|- {a} evalto {i}"
            | EvalB(s, b, bv) ->
                let bv = if bv then "true" else "false"
                $"{printStore s}|- {b} evalto {bv}"
module Judge =
    let print (j: Judge) = j.ToString()

type Derivation =
    | Derivation of Judge * string * Derivation list
    | Incomplete of Judge

let printDerivation printJudge =
    let rec deriv level d =
        let spaces = String.replicate level "  "
        match d with
        | Derivation(judge, name, derivs) ->
            spaces + $"%s{printJudge judge} by {rule level name derivs}"
        | Incomplete judge ->
            spaces + $"%s{printJudge judge} ?;"
    and rule level name l =
        match l with
        | [] -> $"%s{name} {{}};"
        | l ->
            let children = l |> List.fold (fun pre d -> pre + deriv (level + 1) d + "\n") ""
            $"%s{name} {{\n" + children + String.replicate level "  " + "};"
    fun derivation -> deriv 0 derivation

module Parser =
    let digitChars = "0123456789"
    let identifierFirstChars =
        let lower = "abcdefghijklmnopqrstuvwxyz"
        lower + lower.ToUpper() + "_"
    let identifierChars = identifierFirstChars + digitChars + "'"
    let keywords = [| "skip"; "if"; "then"; "else"; "while"; "do"; "changes"; "to"; "evalto" |]

    let space = oneOf " \t\n"
    let sp = production "sp"
    sp.rule
        <- sp + space --> ignore
        |- space --> ignore
        |- ~~"" --> ignore
    let sp1 = space +. sp

    let digit = oneOf digitChars --> fun d -> int(d) - int('0')
    let digits = production "digits"
    digits.rule
        <- ~~"-" +. digits --> (~-)
        |- digits + digit --> fun (a, b) -> a * 10 + b 
        |- digit
    let bool = (~~"true" --> fun _ -> true) |- (~~"false" --> fun _ -> false)

    let ident =
        ScanRat.Combinators.pMatch "ident"
            <| fun text index ->
                if identifierFirstChars.IndexOf(text.[index]) = -1 then None
                else
                    let c = 1
                    let rec count c =
                        if
                            index + c >= text.Length || identifierChars.IndexOf(text.[index + c]) = -1
                        then c else count (c + 1)
                    let c = count c
                    let s = text.Substring(index, c)
                    if Array.IndexOf(keywords, s) <> -1 then None
                    else
                        Some c

    let store = production "store"
    let block = ident .+ sp .+ ~~"=" .+ sp + digit
    store.rule
        <- store .+ sp .+ ~~"," .+ sp + block --> fun (s, (x, i)) -> Block(s, x, i)
        |- block --> fun (x, i) -> Block(Empty, x, i)
        |- ~~"" --> fun _ -> Empty
    
    let aexp = production "aexp"
    let aterm =
        ~~"(" +. sp +. aexp .+ sp .+ ~~")"
        |- digit --> AExp.Int
        |- ident --> AExp.Var
    let times = production "atimes"
    times.rule
        <- times .+ sp .+ ~~"*" .+ sp + aterm --> fun (a1, a2) -> AExp.BinOp(a1, Prim.Times, a2)
        |- aterm
    let plus = production "plus"
    plus.rule
        <- plus .+ sp .+ ~~"+" .+ sp + times --> fun (a1, a2) -> AExp.BinOp(a1, Prim.Plus, a2)
        |- plus .+ sp .+ ~~"-" .+ sp + times --> fun (a1, a2) -> AExp.BinOp(a1, Prim.Minus, a2)
        |- times
    aexp.rule
        <- plus

    let bexp = production "bexp"
    let bterm = production "bterm"
    let comp = (~~"<" --> fun _ -> Comp.Lt) |- (~~"=" --> fun _ -> Comp.Eq) |- (~~"<=" --> fun _ -> Comp.Le)
    bterm.rule
        <- ~~"(" +. sp +. bexp .+ sp .+ ~~")"
        |- ~~"!" +. sp +. bterm --> BExp.Not
        |- bool --> BExp.Bool
        |- aexp .+ sp + comp .+ sp + aexp --> fun ((a1, comp), a2) -> BExp.Comp(a1, comp, a2)
    let lop = production "lop"
    lop.rule
        <- lop .+ sp .+ ~~"&&" .+ sp + bterm --> fun (b1, b2) -> BExp.LOp(b1, LOp.And, b2)
        |- lop .+ sp .+ ~~"||" .+ sp + bterm --> fun (b1, b2) -> BExp.LOp(b1, LOp.Or, b2)
        |- bterm
    bexp.rule
        <- lop

    let com = production "com"
    let cterm =
        ~~"skip" --> fun _ -> Com.Skip
        |- ident .+ sp .+ ~~":=" .+ sp + aexp --> fun (x, a) -> Com.Assign(x, a)
        |- ~~"if" +. sp1 +. bexp .+ sp1 .+ ~~"then" .+ sp1 + com .+ sp1 .+ ~~"else" .+ sp1 + com --> fun ((b, c1), c2) -> Com.If(b, c1, c2)
        |- ~~"while" +. sp +. ~~"(" +. sp +. bexp .+ sp .+ ~~")" .+ sp .+ ~~"do" .+ sp + com --> Com.While
    com.rule
        <- cterm .+ sp .+ ~~";" .+ sp + com --> Com.Seq
        |- cterm
    
    let judge =
        com .+ sp1 .+ ~~"changes" .+ sp1 + store .+ sp1 .+ ~~"to" .+ sp1 + store --> fun ((c, s1), s2) -> Judge.Changes(c, s1, s2)

let rec derive judge =
    let incomplete = Derivation.Incomplete judge
    match judge with
    | EvalA(s, a, i) ->
        match deriveA s a with
        | Some(i', (Derivation _ as d)) when i = i' -> d
        | _ -> incomplete
    | EvalB(s, b, bv) ->
        match deriveB s b with
        | Some(bv', (Derivation _ as d)) when bv = bv' -> d
        | _ -> incomplete
    | Changes(c, s1, s2) ->
        match deriveC c s1 with
        | Some(s2', (Derivation _ as d)) when s2 = s2' -> d
        | _ -> incomplete
and deriveA s a =
    let conclude i name derivs = Some(i, Derivation(EvalA(s, a, i), name, derivs))

    match s, a with
    | _, Int i -> conclude i "A-Const" []
    | s, BinOp(a1, op, a2) ->
        option {
            let! (i1, d1) = deriveA s a1
            let! (i2, d2) = deriveA s a2
            let ds = [d1; d2]
            match op with
            | Plus -> return! conclude (i1 + i2) "A-Plus" ds
            | Minus -> return! conclude (i1 - i2) "A-Minus" ds
            | Times -> return! conclude (i1 * i2) "A-Times" ds
        }
    | s, Var x -> 
        let rec inner = function
            | Block(_, x', i) when x = x' -> conclude i "A-Var" []
            | Block(s, _, _) -> inner s
            | Empty -> None
        inner s

and deriveB s b =
    let conclude bv name derivs = Some(bv, Derivation(EvalB(s, b, bv), name, derivs))

    match s, b with
    | _, Bool bv -> conclude bv "B-Const" []
    | s, Not b ->
        option {
            let! bv, d = deriveB s b
            return! conclude (not bv) "B-Not" [d]
        }
    | s, LOp(b1, op, b2) ->
        option {
            let! bv1, d1 = deriveB s b1
            let! bv2, d2 = deriveB s b2
            let ds = [d1; d2]
            match op with
            | And -> return! conclude (bv1 && bv2) "B-And" ds
            | Or -> return! conclude (bv1 || bv2) "B-Or" ds
        }
    | s, Comp(a1, op, a2) ->
        option {
            let! (i1, d1) = deriveA s a1
            let! (i2, d2) = deriveA s a2
            let ds = [d1; d2]
            match op with
            | Lt -> return! conclude (i1 < i2) "B-Lt" ds
            | Eq -> return! conclude (i1 = i2) "B-Eq" ds
            | Le -> return! conclude (i1 <= i2) "B-Le" ds
        }

and deriveC c s1 =
    let conclude s2 name derivs = Some(s2, Derivation(Changes(c, s1, s2), name, derivs))

    match c, s1 with
    | Skip, s -> conclude s "C-Skip" []
    | Assign(x, a), s1 ->
        option {
            let! (i, d) = deriveA s1 a
            let s2 = s1 |> Store.assign x i
            return! conclude s2 "C-Assign" [d]
        }
    | Seq(c1, c2), s1 ->
        option {
            let! (s2, d1) = deriveC c1 s1
            let! (s3, d2) = deriveC c2 s2
            return! conclude s3 "C-Seq" [d1; d2]
        }
    | If(b, c1, c2), s1 ->
        option {
            let! (bv, d1) = deriveB s1 b
            let name, c = if bv then "C-IfT", c1 else "C-IfF", c2
            let! (s2, d2) = deriveC c s1
            return! conclude s2 name [d1; d2]
        }
    | (While(b, c) as c0), s1 ->
        option {
            let! (bv, d1) = deriveB s1 b
            if bv then
                let! (s2, d2) = deriveC c s1
                let! (s3, d3) = deriveC c0 s2
                return! conclude s3 "C-WhileT" [d1; d2; d3]
            else
                return! conclude s1 "C-WhileF" [d1]
        }

"while (0 < x && 0 < y) do if y < x then x := x - 1 else y := y - 1
changes x = 2, y = 2 to x = 1, y = 0"
|> parse Parser.judge
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> eprintfn "%A" t; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"