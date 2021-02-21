#r "nuget: ScanRat"
open System
open ScanRat.ScanRat;

type Value =
    | Int of int
    | Bool of bool
    with
        override this.ToString() =
            match this with
            | Int i -> string i
            | Bool true -> "true"
            | Bool false -> "false"

type Var = string

type Expr =
    | Value of Value
    | Var of Var
    | Plus of Expr * Expr
    | Minus of Expr * Expr
    | Times of Expr * Expr
    | Lt of Expr * Expr
    (* if e then et else ef *)
    | If of Expr * Expr * Expr
    (* let x = e1 in e2 *)
    | Let of Var * Expr * Expr
    with
        override this.ToString() =
            let rec print = function
                | Value v -> v.ToString()
                | Var x -> x
                | (Plus _) as e -> "(" + printPlus e + ")"
                | (Minus _) as e -> "(" + printMinus e + ")"
                | (Times _) as e -> "(" + printTimes e + ")"
                | Lt(e1, e2) -> "(" + (print e1) + " < " + (print e2) + ")"
                | If(e, et, ef) -> $"(if {print e} then {print et} else {print ef})"
                | Let(x, e1, e2) -> $"(let {x} = {print e1} in {print e2})"
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

type Env =
    Env of (Var * Value) list
    with
        override this.ToString() =
            let rec print = function
                | [] -> ""
                | [(x, v)] -> $"{x} = {v}"
                | (x, v)::l -> (print l) + $", {x} = {v}"
            let (Env l) = this
            print l

type Judge =
    (* E |- e evalto v *)
    | Eval of Env * Expr * Value
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
            | Eval(E, e, v) -> $"{E} |- {e} evalto {v}"
            | Plus(i1, i2, i3) -> $"{i1} plus {i2} is {i3}"
            | Minus(i1, i2, i3) -> $"{i1} minus {i2} is {i3}"
            | Times(i1, i2, i3) -> $"{i1} times {i2} is {i3}"
            | Lt(i1, i2, b3) -> $"{i1} less than {i2} is {Value.Bool b3}"
module Judge =
    let print (j: Judge) = j.ToString()

type Rule =
    (* E |- i evalto i *)
    | EInt
    (* E |- b evalto b *)
    | EBool
    (* E, x = v |- x evalto v*)
    | EVar1
    (* (y != x) /\ E |- x evalto v2 => E, y = v1 |- x evalto v2 *)
    | EVar2 of Derivation
    (* E |- e1 evalto i1 /\ E |- e2 evalto i2 /\ i1 plus i2 is i3 => E |- e1 + e2 evalto i3 *)
    | EPlus of Derivation * Derivation * Derivation
    (* E |- e1 evalto i1 /\ E |- e2 evalto i2 /\ i1 minus i2 is i3 => E |- e1 - e2 evalto i3 *)
    | EMinus of Derivation * Derivation * Derivation
    (* E |- e1 evalto i1 /\ E |- e2 evalto i2 /\ i1 times i2 is i3 => E |- e1 * e2 evalto i3 *)
    | ETimes of Derivation * Derivation * Derivation
    (* E |- e1 evalto i1 /\ E |- e2 evalto i2 /\ i1 less than i2 is b3 => E |- e1 < e2 evalto b3 *)
    | ELt of Derivation * Derivation * Derivation
    (* E |- e1 evalto true /\ E |- e2 evalto v => E |- if e1 then e2 else e3 evalto v *)
    | EIfT of Derivation * Derivation
    (* E |- e1 evalto false /\ E |- e3 evalto v => E |- if e1 then e2 else e3 evalto v *)
    | EIfF of Derivation * Derivation
    (* E |- e1 evalto v1 /\ E, x = v1 |- e2 evalto v => E |- let x = e1 in e2 evalto v*)
    | ELet of Derivation * Derivation
    (* (i3 = i1 + i2) => i1 plus i2 is i3 *)
    | BPlus
    (* (i3 = i1 - i2) => i1 minus i2 is i3 *)
    | BMinus
    (* (i3 = i1 * i2) => i1 times i2 is i3 *)
    | BTimes
    (* (b3 = i1 < i2) => i1 less than i2 is b3 *)
    | BLt
and Derivation = Judge * Rule
module Rule =
    let mapRule = function
        | EInt -> "E-Int", []
        | EBool -> "E-Bool", []
        | EVar1 -> "E-Var1", []
        | EVar2 d -> "E-Var2", [d]
        | EPlus (d1, d2, d3) -> "E-Plus" , [d1; d2; d3]
        | EMinus(d1, d2, d3) -> "E-Minus", [d1; d2; d3]
        | ETimes(d1, d2, d3) -> "E-Times", [d1; d2; d3]
        | ELt   (d1, d2, d3) -> "E-Lt"   , [d1; d2; d3]
        | EIfT(d1, d2) -> "E-IfT", [d1; d2]
        | EIfF(d1, d2) -> "E-IfF", [d1; d2]
        | ELet(d1, d2) -> "E-Let", [d1; d2]
        | BPlus -> "B-Plus", []
        | BMinus -> "B-Minus", []
        | BTimes -> "B-Times", []
        | BLt -> "B-Lt", []

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

module Parser =
    let digitChars = "0123456789"
    let identifierFirstChars =
        let lower = "abcdefghijklmnopqrstuvwxyz"
        lower + lower.ToUpper() + "_'"
    let digit = oneOf digitChars --> fun d -> int(d) - int('0')
    let digits = production "digits"
    digits.rule
        <- ~~"-" +. digits --> (~-)
        |- digits + digit --> fun (a, b) -> a * 10 + b 
        |- digit
    let bool = (~~"true" --> fun _ -> true) |- (~~"false" --> fun _ -> false)
    let value = (digits --> Value.Int) |- (bool --> Value.Bool)
    
    let var = production "var"
    var.rule
        <- var + (oneOf (identifierFirstChars + digitChars)) --> fun (a, b) -> a + (string b)
        |- oneOf identifierFirstChars --> string
    
    let expr = production "expr"
    let term = production "term"
    term.rule
        <- ~~"(" +. expr .+ ~~")"
        |- value --> Expr.Value
        |- var --> Expr.Var
    let binop = production "binop"
    binop.rule
        <- binop .+ ~~" * " + term --> Expr.Times
        |- binop .+ ~~" + " + term --> Expr.Plus
        |- binop .+ ~~" - " + term --> Expr.Minus
        |- binop .+ ~~" < " + term --> Expr.Minus
        |- term
    expr.rule
        <- (~~"if " +. expr .+ ~~" then " + expr .+ ~~" else " + expr) --> fun ((e, et), ef) -> Expr.If(e, et, ef)
        |- (~~"let " +. var .+ ~~" = " + expr .+ ~~" in " + expr) --> fun ((x, e1), e2) -> Expr.Let(x, e1, e2)
        |- binop
    
    let env = production "env"
    let envDef = var .+ ~~" = " + value
    env.rule
        <- env .+ ~~", " + envDef --> fun (Env e1, d) -> Env(d::e1)
        |- envDef --> fun e -> Env[e]
        |- ~~"" --> fun _ -> Env[]
    
    let eval = env .+ ~~" |- " + expr .+ ~~" evalto " + value --> fun ((E, e), v) -> Judge.Eval(E, e, v)

let rec eval env expr =
    let evalIntBinop env e1 e2 op =
        match (eval env e1, eval env e2) with
        | (Int i1, Int i2) -> op i1 i2
        | (_, _) -> failwith "Invalid type"
    match expr with
    | Value v -> v
    | Var x ->
        let rec inner = function
            | Env((x', v)::_) when x' = x -> v
            | Env(_::l) -> inner (Env l)
            | Env[] -> failwith "Env is empty"
        inner env
    | Expr.Plus(e1, e2) -> evalIntBinop env e1 e2 (+) |> Value.Int
    | Expr.Minus(e1, e2) -> evalIntBinop env e1 e2 (-) |> Value.Int
    | Expr.Times(e1, e2) -> evalIntBinop env e1 e2 ( * ) |> Value.Int
    | Expr.Lt(e1, e2) -> evalIntBinop env e1 e2 (<) |> Value.Bool
    | If(e, et, ef) ->
        match (eval env e) with
        | Bool true -> eval env et
        | Bool false -> eval env ef
        | _ -> failwith "invalid type"
    | Let(x, e1, e2) ->
        let v = eval env e1
        let (Env l) = env
        eval (Env ((x, v)::l)) e2

let rec derive judge =
    let conclude by = (judge, by)

    let deriveIntBinOp rule judge env e1 e2 r =
        match (eval env e1, eval env e2) with
        | ((Int i1 as v1), (Int i2 as v2)) ->
            conclude <| rule(
                derive <| Judge.Eval(env, e1, v1),
                derive <| Judge.Eval(env, e2, v2),
                derive <| judge(i1, i2, r)
            )
        | _ -> failwith "Invalid type"

    match judge with
    | Eval(_, Value(Int i), Int i') when i = i' -> conclude EInt
    | Eval(_, Value(Bool b), Bool b') when b = b' -> conclude EBool
    | Eval(Env((x, v)::_), Var x', v') when x = x' && v = v' -> conclude EVar1
    | Eval(Env((y, _)::E), Var x, v) when y <> x ->
        conclude <| EVar2(derive <| Eval(Env E, Var x, v))
    | Eval(env, Expr.Plus(e1, e2), Int i3) ->
        deriveIntBinOp Rule.EPlus Judge.Plus env e1 e2 i3
    | Eval(env, Expr.Minus(e1, e2), Int i3) ->
        deriveIntBinOp Rule.EMinus Judge.Minus env e1 e2 i3
    | Eval(env, Expr.Times(e1, e2), Int i3) ->
        deriveIntBinOp Rule.ETimes Judge.Times env e1 e2 i3
    | Eval(env, Expr.Lt(e1, e2), Bool b3) ->
        deriveIntBinOp Rule.ELt Judge.Lt env e1 e2 b3
    | Eval(env, Expr.If(e, et, ef), v) ->
        match (eval env e) with
        | (Bool true) ->
            conclude <| Rule.EIfT(
                derive <| Judge.Eval(env, e, Bool true),
                derive <| Judge.Eval(env, et, v)
            )
        | (Bool false) ->
            conclude <| Rule.EIfF(
                derive <| Judge.Eval(env, e, Bool false),
                derive <| Judge.Eval(env, ef, v)
            )
        | _ -> failwith "Invalid type"
    | Eval((Env E as env), Expr.Let(x, e1, e2), v) ->
        let v1 = eval env e1
        conclude <| Rule.ELet(
            derive <| Judge.Eval(env, e1, v1),
            derive <| Judge.Eval(Env((x, v1)::E), e2, v)
        )
    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude <| Rule.BPlus
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude <| Rule.BMinus
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude <| Rule.BTimes
    | Lt(i1, i2, b3)    when b3 = (i1 < i2) -> conclude <| Rule.BLt
    | j ->
        failwithf "Invalid input(maybe unimplemented): %A" j

" |- let x = let y = 3 - 2 in y * y in let y = 4 in x + y evalto 5"
|> parse Parser.eval
|> function
    | Success s -> s.Value
    | Failure e -> failwith (sprintf "%A" e)
|> derive
|> printDerivation Judge.print Rule.mapRule
|> printfn "%s"