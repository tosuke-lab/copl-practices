#r "nuget: ScanRat"
open System
open ScanRat.ScanRat

type Expr =
    | Int of int
    | Bool of bool
    | Plus of Expr * Expr
    | Minus of Expr * Expr
    | Times of Expr * Expr
    | LT of Expr * Expr
    | If of Expr * Expr * Expr
    with
        override this.ToString() =
            let rec print = function
                | Int i -> string i
                | Bool true -> "true"
                | Bool false -> "false"
                | (Plus _) as e -> "(" + printPlus e + ")"
                | (Minus _) as e -> "(" + printMinus e + ")"
                | (Times _) as e -> "(" + printTimes e + ")"
                | LT(e1, e2) -> "(" + (print e1) + " < " + (print e2) + ")"
                | If(e, et, ef) -> "(if " + (print e) + " then " + (print et) + " else " + (print ef) + ")"
            and printPlus = function
                | Plus(e1, e2) -> (printPlus e1) + " + " + (printPlus e2)
                | e -> print e
            and printMinus = function
                | Minus(e1, e2) -> (printMinus e1) + " - " + (printMinus e2)
                | e -> print e
            and printTimes = function
                | Times(e1, e2) -> (printTimes e1) + " * " + (printTimes e2)
                | e -> print e
            print this

type Value =
    | Int of int
    | Bool of bool
    with
        override this.ToString() =
            match this with
            | Int i -> string i
            | Bool true -> "true"
            | Bool false -> "false"

type Judge =
    (* e evalto v *)
    | Eval of Expr * Value
    (* e evalto error *)
    | EvalErr of Expr
    (* i1 plus i2 is i3 *)
    | Plus of int * int * int
    (* i1 minus i2 is i3 *)
    | Minus of int * int * int
    (* i1 times i2 is i3 *)
    | Times of int * int * int
    (* i1 less than i2 is b3 *)
    | Lt of int * int * bool
    with
        override this.ToString() =
            match this with
            | Eval(e, v) -> $"{e} evalto {v}"
            | EvalErr e -> $"{e} evalto error"
            | Plus(i1, i2, i3) -> $"{i1} plus {i2} is {i3}"
            | Minus(i1, i2, i3) -> $"{i1} minus {i2} is {i3}"
            | Times(i1, i2, i3) -> $"{i1} times {i2} is {i3}"
            | Lt(i1, i2, b3) -> $"{i1} less than {i2} is {Value.Bool b3}"
module Judge =
    let print (j: Judge) = j.ToString()

type Rule =
    (* i evalto i *)
    | EInt
    (* b evalto b *)
    | EBool
    (* e1 evalto true /\ e2 evalto v => if e1 then e2 else e3 evalto v *)
    | EIfT of Derivation * Derivation
    (* e1 evalto false /\ e3 evalto v => if e1 then e2 else e3 evalto v *)
    | EIfF of Derivation * Derivation
    (* e1 evalto i1 /\ e2 evalto i2 /\ i1 plus i2 is i3 => e1 + e2 evalto i3 *)
    | EPlus of Derivation * Derivation * Derivation
    (* e1 evalto i1 /\ e2 evalto i2 /\ i1 minus i2 is i3 => e1 - e2 evalto i3 *)
    | EMinus of Derivation * Derivation * Derivation
    (* e1 evalto i1 /\ e2 evalto i2 /\ i1 times i2 is i3 => e1 * e2 evalto i3 *)
    | ETimes of Derivation * Derivation * Derivation
    (* e1 evalto i1 /\ e2 evalto i2 /\ i1 less than i2 is b3 => e1 < e2 evalto b3 *)
    | ELt of Derivation * Derivation * Derivation
    (* i1 plus i2 is i3 *)
    | BPlus
    (* i1 minus i2 is i3 *)
    | BMinus
    (* i1 times i2 is i3 *)
    | BTimes
    (* i1 less than i2 is b3 *)
    | BLt
    | EPlusBoolL of Derivation
    | EPlusBoolR of Derivation
    | EPlusErrorL of Derivation
    | EPlusErrorR of Derivation
    | EMinusBoolL of Derivation
    | EMinusBoolR of Derivation
    | EMinusErrorL of Derivation
    | EMinusErrorR of Derivation
    | ETimesBoolL of Derivation
    | ETimesBoolR of Derivation
    | ETimesErrorL of Derivation
    | ETimesErrorR of Derivation
    | ELTBoolL of Derivation
    | ELTBoolR of Derivation
    | ELTErrorL of Derivation
    | ELTErrorR of Derivation
    | EIfInt of Derivation
    | EIfError of Derivation
    | EIfTError of Derivation * Derivation
    | EIfFError of Derivation * Derivation
and Derivation = Judge * Rule
module Rule =
    let mapRule = function
        | EInt -> "E-Int", []
        | EBool -> "E-Bool", []
        | EIfT(d1, d2) -> "E-IfT", [d1; d2]
        | EIfF(d1, d2) -> "E-IfF", [d1; d2]
        | EPlus (d1, d2, d3) -> "E-Plus" , [d1; d2; d3]
        | EMinus(d1, d2, d3) -> "E-Minus", [d1; d2; d3]
        | ETimes(d1, d2, d3) -> "E-Times", [d1; d2; d3]
        | ELt   (d1, d2, d3) -> "E-Lt"   , [d1; d2; d3]
        | BPlus -> "B-Plus", []
        | BMinus -> "B-Minus", []
        | BTimes -> "B-Times", []
        | BLt -> "B-Lt", []
        | EPlusBoolL d -> "E-PlusBoolL", [d] 
        | EPlusBoolR d -> "E-PlusBoolR", [d] 
        | EPlusErrorL d -> "E-PlusErrorL", [d] 
        | EPlusErrorR d -> "E-PlusErrorR", [d] 
        | EMinusBoolL d -> "E-MinusBoolL", [d]
        | EMinusBoolR d -> "E-MinusBoolR", [d]
        | EMinusErrorL d -> "E-MinusErrorL", [d]
        | EMinusErrorR d -> "E-MinusErrorR", [d]
        | ETimesBoolL d -> "E-TimesBoolL", [d]
        | ETimesBoolR d -> "E-TimesBoolR", [d]
        | ETimesErrorL d -> "E-TimesErrorL", [d]
        | ETimesErrorR d -> "E-TimesErrorR", [d]
        | ELTBoolL d -> "E-LtBoolL", [d]
        | ELTBoolR d -> "E-LtBoolR", [d]
        | ELTErrorL d -> "E-LtErrorL", [d]
        | ELTErrorR d -> "E-LtErrorR", [d]
        | EIfInt d -> "E-IfInt", [d]
        | EIfError d -> "E-IfError", [d]
        | EIfTError(d1, d2) -> "E-IfTError", [d1; d2]
        | EIfFError(d1, d2) -> "E-IfFError", [d1; d2]

let printDerivation printJudge mapRule =
    let rec deriv level (judge, by) =
        String.replicate level "  " + $"%s{printJudge judge} by {mapRule by |> rule level}"
    and rule level (name, l) =
        match l with
        | [] -> $"%s{name} {{}};"
        | l ->
            let children = l |> List.fold (fun pre d -> pre + deriv (level + 1) d + "\n") ""
            $"%s{name} {{\n" + children + String.replicate level "  " + "};"
    fun derivation -> deriv 0 derivation

let rec eval = function
    | Expr.Int i -> Some <| Value.Int i
    | Expr.Bool b -> Some <| Value.Bool b
    | Expr.Plus(e1, e2) ->
        match (eval e1, eval e2) with
        | (Some(Value.Int i1), Some(Value.Int i2)) -> Some <| Value.Int(i1 + i2)
        | _ -> None
    | Expr.Minus(e1, e2) ->
        match (eval e1, eval e2) with
        | (Some(Value.Int i1), Some(Value.Int i2)) -> Some <| Value.Int(i1 - i2)
        | _ -> None
    | Expr.Times(e1, e2) ->
        match (eval e1, eval e2) with
        | (Some(Value.Int i1), Some(Value.Int i2)) -> Some <| Value.Int(i1 * i2)
        | _ -> None
    | Expr.LT(e1, e2) ->
        match (eval e1, eval e2) with
        | (Some(Value.Int i1), Some(Value.Int i2)) -> Some <| Value.Bool(i1 < i2)
        | _ -> None
    | Expr.If(e, et, ef) ->
        match (eval e) with
        | Some(Value.Bool true) -> eval et
        | Some(Value.Bool false) -> eval ef
        | _ -> None


let rec derive judge =
    let conclude by = (judge, by)

    let deriveBinOp rule judge e1 e2 r =
        match (eval e1, eval e2) with
        | (Some((Value.Int i1) as v1), Some((Value.Int i2) as v2)) ->
            conclude <| rule(
                derive <| Judge.Eval(e1, v1),
                derive <| Judge.Eval(e2, v2),
                derive <| judge(i1, i2, r)
            )
        | _ -> failwith "invalid type"

    let deriveEvalErr eboolL eboolR eerrorL eerrorR e1 e2 =
        match (eval e1, eval e2) with
        | (Some(Value.Bool _ as b), _) -> conclude <| eboolL(derive <| Judge.Eval(e1, b))
        | (_, Some(Value.Bool _ as b)) -> conclude <| eboolR(derive <| Judge.Eval(e2, b))
        | (None, _) -> conclude <| eerrorL(derive <| Judge.EvalErr(e1))
        | (_, None) -> conclude <| eerrorR(derive <| Judge.EvalErr(e2))
        | (Some(Value.Int _), Some(Value.Int _)) -> failwith "valid...?"

    match judge with
    | Eval(Expr.Int(i), Value.Int(i')) when i = i' -> conclude EInt
    | Eval(Expr.Bool(b), Value.Bool(b')) when b = b' -> conclude EBool
    | Eval(Expr.If(e, et, ef), v) ->
        match (eval e) with
        | Some(Value.Bool true) ->
            conclude <| Rule.EIfT(
                derive <| Judge.Eval(e, Value.Bool true),
                derive <| Judge.Eval(et, v)
            )
        | Some(Value.Bool false) ->
            conclude <| Rule.EIfF(
                derive <| Judge.Eval(e, Value.Bool false),
                derive <| Judge.Eval(ef, v)
            )
        | _ -> failwith "invalid type"
    | EvalErr(Expr.If(e, et, ef)) ->
        match (eval e) with
        | Some((Value.Int _ as i)) ->
            conclude <| Rule.EIfInt(derive <| Judge.Eval(e, i))
        | None ->
            conclude <| Rule.EIfError(derive <| Judge.EvalErr(e))
        | Some(Value.Bool true) ->
            conclude <| Rule.EIfTError(
                derive <| Judge.Eval(e, Value.Bool true),
                derive <| Judge.EvalErr(et)
            )
        | Some(Value.Bool false) ->
            conclude <| Rule.EIfFError(
                derive <| Judge.Eval(e, Value.Bool false),
                derive <| Judge.EvalErr(ef)
            )
    | Eval(Expr.Plus(e1, e2), Value.Int(i3)) ->
        deriveBinOp Rule.EPlus Judge.Plus e1 e2 i3
    | EvalErr(Expr.Plus(e1, e2)) ->
        deriveEvalErr Rule.EPlusBoolL Rule.EPlusBoolR Rule.EPlusErrorL Rule.EPlusErrorR e1 e2
    | Eval(Expr.Minus(e1, e2), Value.Int(i3)) ->
        deriveBinOp Rule.EMinus Judge.Minus e1 e2 i3
    | EvalErr(Expr.Minus(e1, e2)) ->
        deriveEvalErr Rule.EMinusBoolL Rule.EMinusBoolR Rule.EMinusErrorL Rule.EMinusErrorR e1 e2
    | Eval(Expr.Times(e1, e2), Value.Int(i3)) ->
        deriveBinOp Rule.ETimes Judge.Times e1 e2 i3
    | EvalErr(Expr.Times(e1, e2)) ->
        deriveEvalErr Rule.ETimesBoolL Rule.ETimesBoolR Rule.ETimesErrorL Rule.ETimesErrorR e1 e2
    | Eval(Expr.LT(e1, e2), Value.Bool(b3)) ->
        deriveBinOp Rule.ELt Judge.Lt e1 e2 b3
    | EvalErr(Expr.LT(e1, e2)) ->
        deriveEvalErr Rule.ELTBoolL Rule.ELTBoolR Rule.ELTErrorL Rule.ELTErrorR e1 e2 
    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude <| Rule.BPlus
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude <| Rule.BMinus
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude <| Rule.BTimes
    | Lt(i1, i2, b3)    when b3 = (i1 < i2) -> conclude <| Rule.BLt
    | r ->
        failwithf "Invalid input(maybe unimplemented): %A" r

module Parser =
    let digit = oneOf "0123456789" --> fun d -> int(d) - int('0')
    let digits = production "digits"
    digits.rule
        <- ~~"-" +. digits --> (~-)
        |- digits + digit --> fun (a, b) -> a * 10 + b
        |- digit
    let bool = (~~"true" --> fun _ -> true) |- (~~"false" --> fun _ -> false)

    let term = production "term"

    let times = production "times"
    times.rule
        <- times .+ ~~" * " + term --> Expr.Times
        |- term

    let plusMinus = production "plusMinus"
    plusMinus.rule
        <- plusMinus .+ ~~" + " + times --> Expr.Plus
        |- plusMinus .+ ~~" - " + times --> Expr.Minus
        |- times
    
    let comparison = production "comparison"
    comparison.rule
        <- comparison .+ ~~" < " + plusMinus --> Expr.LT
        |- plusMinus
    
    let expr = production "expr"
    expr.rule
        <- comparison
    term.rule
        <- ~~"(" +. expr .+ ~~")"
        |- (~~"if " +. expr .+ ~~" then " + expr .+ ~~" else " + expr) --> fun ((e, et), ef) -> Expr.If(e, et, ef)
        |- digits --> Expr.Int
        |- bool --> Expr.Bool
    
    let value = (digits --> Value.Int) |- (bool --> Value.Bool)

    let eval = (expr .+ ~~" evalto " + value --> Judge.Eval) |- (expr .+ ~~" evalto error" --> Judge.EvalErr)

"if 3 < 4 then 1 < true else 3 - false evalto error"
|> parse Parser.eval
|> function
    | Success s -> s.Value
    | Failure e -> failwith (sprintf "%A" e)
|> derive
|> printDerivation Judge.print Rule.mapRule
|> printfn "%s"