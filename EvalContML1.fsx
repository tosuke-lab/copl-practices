#r "nuget: ScanRat"
open System
open ScanRat.ScanRat

type Value =
    | Int of int
    | Bool of bool
    with
        override this.ToString() =
            match this with
            | Int i -> string i
            | Bool true -> "true"
            | Bool false -> "false"

type Op = Plus | Minus | Times | Lt
    with
        override this.ToString() =
            match this with
            | Plus -> "+"
            | Minus -> "-"
            | Times -> "*"
            | Lt -> "<"

type Expr =
    | Int of int
    | Bool of bool
    | BinOp of Expr * Op * Expr
    | If of Expr * Expr * Expr
    with
        override this.ToString() =
            let rec print = function
                | Int i -> (Value.Int i).ToString()
                | Bool b -> (Value.Bool b).ToString()
                | BinOp(_, op, _) as e -> "(" + printBinop op e + ")"
                | If(e1, e2, e3) -> $"(if {print e1} then {print e2} else {print e3})"
            and printBinop op = function
                | BinOp(e1, op', e2) when op = op' -> printBinop op e1 + $" {op} " + printBinop op e2
                | e -> print e
            print this

type Cont =
    | Ret
    (* {_ op e} >> k *)
    | BinOpL of Op * Expr * Cont
    (* {v op _} >> k *)
    | BinOpR of Value * Op * Cont
    (* {if _ then e else e} >> k *)
    | If of Expr * Expr * Cont
    with
        override this.ToString() =
            let rec print = function
                | Ret -> "_"
                | BinOpL(op, e, k) -> $"{{_ {op} {e}}} >> {print k}"
                | BinOpR(v, op, k) -> $"{{{v} {op} _}} >> {print k}"
                | If(e1, e2, k) -> $"{{if _ then {e1} else {e2}}} >> {print k}"
            print this

type Judge =
    (* e >> k evalto v *)
    | EvalE of Expr * Cont * Value
    (* v1 => k evalto v2 *)
    | EvalV of Value * Cont * Value
    | Plus of int * int * int
    | Minus of int * int * int
    | Times of int * int * int
    | Lt of int * int * bool
    with
        override this.ToString() =
            match this with
            | EvalE(e, k, v) -> $"{e} >> {k} evalto {v}"
            | EvalV(v1, k, v2) -> $"{v1} => {k} evalto {v2}"
            | Plus(i1, i2, i3) -> $"{i1} plus {i2} is {i3}"
            | Minus(i1, i2, i3) -> $"{i1} minus {i2} is {i3}"
            | Times(i1, i2, i3) -> $"{i1} times {i2} is {i3}"
            | Lt(i1, i2, b3) -> $"{i1} less than {i2} is {Value.Bool b3}"
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

    let value = (digits --> Value.Int) |- (bool --> Value.Bool)

    let expr = production "expr"
    let term =
        ~~"(" +. sp +. expr .+ sp .+ ~~")"
        |- digits --> Expr.Int
        |- bool --> Expr.Bool
    let times = production "times"
    times.rule
        <- times .+ sp .+ ~~"*" .+ sp + term --> fun (e1, e2) -> Expr.BinOp(e1, Op.Times, e2)
        |- term
    let plus = production "plus"
    plus.rule
        <- plus .+ sp + ((~~"+" --> fun _ -> Op.Plus) |- (~~"-" --> fun _ -> Op.Minus)) .+ sp + times
            --> fun ((e1, op), e2) -> Expr.BinOp(e1, op, e2)
        |- times
    let lessThan = production "lessThan"
    lessThan.rule
        <- lessThan .+ sp .+ ~~"<" .+ sp + plus --> fun (e1, e2) -> Expr.BinOp(e1, Op.Lt, e2)
        |- plus
    expr.rule
        <- ~~"if" +. sp1 +. expr .+ sp1 .+ ~~"then" .+ sp1 + expr .+ sp1 .+ ~~"else" .+ sp1 + expr
            --> fun ((e1, e2), e3) -> Expr.If(e1, e2, e3)
        |- lessThan
    
    let cont = production "cont"
    let op = (~~"+" --> fun _ -> Op.Plus) |- (~~"-" --> fun _ -> Op.Minus) |- (~~"*" --> fun _ -> Op.Times) |- (~~"<" --> fun _ -> Op.Lt)
    let contTail = (~~">>" +. sp +. cont) |- (~~"" --> fun _ -> Cont.Ret)
    cont.rule
        <- ~~"{" +. sp +. ~~"_" +. sp +. op .+ sp + expr .+ sp .+ ~~"}" .+ sp + contTail
            --> fun ((op, e), k) -> Cont.BinOpL(op, e, k) 
        |- ~~"{" +. sp +. value .+ sp + op .+ sp .+ ~~"_" .+ sp .+ ~~"}" .+ sp + contTail
            --> fun ((v, op), k) -> Cont.BinOpR(v, op, k)
        |- ~~"{" +. sp +. ~~"if" +. sp1 +. ~~"_" +. sp1 +. ~~"then" +. sp1 +. expr .+ sp1 .+ ~~"else" .+ sp1 + expr .+ ~~"}" .+ sp + contTail
            --> fun ((e1, e2), k) -> Cont.If(e1, e2, k)
        |- ~~"_" --> fun _ -> Cont.Ret

    let judge =
        expr .+ sp + contTail .+ sp .+ ~~"evalto" .+ sp1 + value --> fun ((e, k), v) -> Judge.EvalE(e, k, v)

let rec evalE e k =
    match e, k with
    | Expr.Int i, k -> evalV (Value.Int i) k
    | Expr.Bool b, k -> evalV (Value.Bool b) k
    | Expr.BinOp(e1, op, e2), k -> evalE e1 (Cont.BinOpL(op, e2, k))
    | Expr.If(e1, e2, e3), k -> evalE e1 (Cont.If(e2, e3, k))
and evalV v k =
    match v, k with
    | v, Cont.Ret -> v
    | v, Cont.BinOpL(op, e, k) -> evalE e (Cont.BinOpR(v, op, k))
    | Value.Int i2, Cont.BinOpR(Value.Int i1, op, k) ->
        let v3 =
            match op with
            | Op.Plus -> Value.Int (i1 + i2)
            | Op.Minus -> Value.Int (i1 - i2)
            | Op.Times -> Value.Int (i1 * i2)
            | Op.Lt -> Value.Bool (i1 < i2)
        evalV v3 k
    | Value.Bool true, Cont.If(e, _, k) -> evalE e k
    | Value.Bool false, Cont.If(_, e, k) -> evalE e k

let rec derive judge =
    let conclude name derivs = Derivation(judge, name, derivs)

    match judge with
    | EvalE(Expr.Int i, k, v) -> conclude "E-Int" [derive <| EvalV(Value.Int i, k, v)]
    | EvalE(Expr.Bool b, k, v) -> conclude "E-Bool" [derive <| EvalV(Value.Bool b, k, v)]
    | EvalE(Expr.BinOp(e1, op, e2), k, v) -> conclude "E-BinOp" [derive <| EvalE(e1, Cont.BinOpL(op, e2, k), v)]
    | EvalE(Expr.If(e1, e2, e3), k, v) -> conclude "E-If" [derive <| EvalE(e1, Cont.If(e2, e3, k), v)]
    | EvalV(v, Cont.Ret, v') when v = v' -> conclude "C-Ret" []
    | EvalV(v1, Cont.BinOpL(op, e, k), v2) -> conclude "C-EvalR" [derive <| EvalE(e, Cont.BinOpR(v1, op, k), v2)]
    | EvalV(Value.Int i2, Cont.BinOpR(Value.Int i1, op, k), v) ->
        let (name, j, v3) =
            match op with
            | Op.Plus -> "C-Plus", Judge.Plus(i1, i2, i1 + i2), Value.Int(i1 + i2)
            | Op.Minus -> "C-Minus", Judge.Minus(i1, i2, i1 - i2), Value.Int(i1 - i2)
            | Op.Times -> "C-Times", Judge.Times(i1, i2, i1 * i2), Value.Int(i1 * i2)
            | Op.Lt -> "C-Lt", Judge.Lt(i1, i2, i1 < i2), Value.Bool(i1 < i2)
        conclude name [
            derive <| j;
            derive <| EvalV(v3, k, v)
        ]
    | EvalV(Value.Bool true, Cont.If(e, _, k), v) -> conclude "C-IfT" [derive <| EvalE(e, k, v)]
    | EvalV(Value.Bool false, Cont.If(_, e, k), v) -> conclude "C-IfF" [derive <| EvalE(e, k, v)]
    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude "B-Plus" []
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude "B-Minus" []
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude "B-Times" []
    | Lt   (i1, i2, b3) when b3 = (i1 < i2) -> conclude "B-Lt" []
    | j ->
        Derivation.Incomplete j

"3 + (if -3 < -2 * 8 then 8 else 2) + 4 evalto 9"
|> parse Parser.judge
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> printfn "%A" t; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"