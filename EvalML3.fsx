#r "nuget: Scanrat"
open System
open ScanRat.ScanRat

type Var = string

type Value =
    | Int of int
    | Bool of bool
    (* (E)[fun x -> e] *)
    | Func of Env * Var * Expr
    (* (E)[rec x = fun y -> e] *)
    | FuncRec of Env * Var * Var * Expr
    with
        override this.ToString() =
            match this with
            | Int i -> string i
            | Bool true -> "true"
            | Bool false -> "false"
            | Func(env, x, e) -> $"({env})[fun {x} -> {e}]"
            | FuncRec(env, x, y, e) -> $"({env})[rec {x} = fun {y} -> {e}]"
and Expr =
    | Int of int
    | Bool of bool
    | Var of Var
    | Plus of Expr * Expr
    | Minus of Expr * Expr
    | Times of Expr * Expr
    | Lt of Expr * Expr
    (* if e then et else ef *)
    | If of Expr * Expr * Expr
    (* let x = e1 in e2 *)
    | Let of Var * Expr * Expr
    (* let rec x = fun y -> e1 in e2 *)
    | LetRec of Var * Var * Expr * Expr
    (* fun x -> e *)
    | Func of Var * Expr
    (* e e *)
    | App of Expr * Expr
    with
        override this.ToString() =
            let rec print = function
                | Int i -> string i
                | Bool true -> "true"
                | Bool false -> "false"
                | Var x -> x
                | (Plus _) as e -> "(" + printPlus e + ")"
                | (Minus _) as e -> "(" + printMinus e + ")"
                | (Times _) as e -> "(" + printTimes e + ")"
                | Lt(e1, e2) -> "(" + (print e1) + " < " + (print e2) + ")"
                | If(e, et, ef) -> $"(if {print e} then {print et} else {print ef})"
                | Let(x, e1, e2) -> $"(let {x} = {print e1} in {print e2})"
                | LetRec(x, y, e1, e2) -> $"(let rec {x} = fun {y} -> {print e1} in {print e2})"
                | Func(x, e) -> $"(fun {x} -> {e})"
                | App(e, e') -> $"({e} {e'})"
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
and Env =
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
            | Eval(env, e, v) ->
                let env = env.ToString()
                let space = if env = "" then "" else " "
                $"{env}{space}|- {e} evalto {v}"
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
    (* E |- fun x -> e evalto (E)[fun x -> e] *)
    | EFun
    (* E |- e1 evalto (E2)[fun x -> e0] /\ E |- e2 evalto v2 /\ E2,x=v2 |- e0 evalto v => E |- e1 e2 evalto v *)
    | EApp of Derivation * Derivation * Derivation
    (* E,x = (E)[rec x = fun y -> e1] |- e2 evalto v => E |- let rec x = fun y -> e1 in e2 evalto v *)
    | ELetRec of Derivation
    (* E |- e1 evalto (E2)[rec x = fun y -> e0] /\ E |- e2 evalto v2 /\ E2,x = (E2)[rec x = fun y -> e0],y=v2 |- e0 evalto v => E |- e1 e2 evalto v *)
    | EAppRec of Derivation * Derivation * Derivation
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
        | EFun -> "E-Fun", []
        | EApp(d1, d2, d3) -> "E-App", [d1; d2; d3]
        | ELetRec d -> "E-LetRec", [d]
        | EAppRec(d1, d2, d3) -> "E-AppRec", [d1; d2; d3]
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
        lower + lower.ToUpper() + "_"
    let identifierChars = identifierFirstChars + digitChars + "'"
    let spaceChars = " \t\n"

    let many p =
        let m = production $"many {p}"
        m.rule
            <- p + m --> fun (h, hs) -> h::hs
            |- ~~"" --> fun _ -> []
        m
    let many1 p = p + (many p) --> fun (h, hs) -> h::hs
    
    let space = oneOf spaceChars --> ignore
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
    
    let ident = production "ident"
    ident.rule
        <- (
            ident + (oneOf identifierChars) --> fun (s, c) -> s + string c
            |- oneOf identifierFirstChars --> string
        ) / (~~"if" |- ~~"then" |- ~~"else" |- ~~"let" |- ~~"rec" |- ~~"in" |- ~~"fun" |- ~~"evalto")
    
    let value = production "value"
    let expr = production "expr"
    let env = production "env"
    value.rule
        <- digits --> Value.Int
        |- bool --> Value.Bool
        |- (~~"(" +. sp +. env .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + expr .+ sp .+ ~~"]")
            --> fun ((env, x), e) -> Value.Func(env, x, e)
        |- (~~"(" +. sp +. env .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ sp .+ ~~"rec" .+ sp1 + ident .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + expr .+ sp .+ ~~"]")
            --> fun (((env, x), y), e) -> Value.FuncRec(env, x, y, e)
    let term = production "term"
    term.rule
        <- ~~"(" +. sp +. expr .+ sp .+ ~~")"
        |- digits --> Expr.Int
        |- bool --> Expr.Bool
        |- ident --> Expr.Var
    let app = production "app"
    app.rule
        <- app .+ ~~" " + term --> Expr.App
        |- term
    let binop = production "binop"
    binop.rule
        <- binop .+ sp .+ ~~"*" .+ sp + app --> Expr.Times
        |- binop .+ sp .+ ~~"+" .+ sp + app --> Expr.Plus
        |- binop .+ sp .+ ~~"-" .+ sp + app --> Expr.Minus
        |- binop .+ sp .+ ~~"<" .+ sp + app --> Expr.Lt
        |- app
    expr.rule
        <- (~~"if" +. sp1 +. expr .+ sp1 .+ ~~"then" .+ sp1 + expr .+ sp1 .+ ~~"else" .+ sp1 + expr) --> fun ((e, et), ef) -> Expr.If(e, et, ef)
        |- (~~"let" +. sp1 +. ~~"rec" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + expr .+ sp1 .+ ~~"in" .+ sp1 + expr)
            --> fun (((x, y), e1), e2) -> Expr.LetRec(x, y, e1, e2)
        |- (~~"let" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp + expr .+ sp1 .+ ~~"in" .+ sp1 + expr) --> fun ((x, e1), e2) -> Expr.Let(x, e1, e2)
        |- (~~"fun" +. sp1 +. ident .+ sp .+ ~~"->" .+ sp + expr) --> Expr.Func
        |- binop
    
    let bind = ident .+ sp .+ ~~"=" .+ sp + value
    env.rule
        <- env .+ sp .+ ~~"," .+ sp + bind --> fun (Env e1, d) -> Env(d::e1)
        |- bind --> fun e -> Env[e]
        |- ~~"" --> fun _ -> Env[]
    
    let eval = env .+ sp .+ ~~"|-" .+ sp + expr .+ sp1 .+ ~~"evalto" .+ sp1 + value --> fun ((E, e), v) -> Judge.Eval(E, e, v)

let rec eval env expr =
    let evalIntBinop env e1 e2 op =
        match (eval env e1, eval env e2) with
        | (Value.Int i1, Value.Int i2) -> op i1 i2
        | (_, _) -> failwith "Invalid type"
    match expr with
    | Int i -> Value.Int i
    | Bool b -> Value.Bool b
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
        | Value.Bool true -> eval env et
        | Value.Bool false -> eval env ef
        | _ -> failwith "invalid type"
    | Let(x, e1, e2) ->
        let v = eval env e1
        let (Env l) = env
        eval (Env ((x, v)::l)) e2
    | LetRec(x, y, e1, e2) ->
        let (Env l) = env
        eval (Env ((x, FuncRec(env, x, y, e1))::l)) e2 
    | Func(x, e) -> Value.Func(env, x, e)
    | App(e1, e2) ->
        match (eval env e1, eval env e2) with
        | (Value.Func(Env E2, x, e), v2) ->
            eval (Env((x, v2)::E2)) e
        | (Value.FuncRec(Env E2, x, y, e0) as v1, v2) ->
            let env' = Env((y, v2)::(x, v1)::E2)
            eval env' e0
        | (_, _) -> failwith "Invalid type(not func)"

let rec derive judge =
    let conclude by = (judge, by)

    let deriveIntBinOp rule judge env e1 e2 r =
        match (eval env e1, eval env e2) with
        | ((Value.Int i1 as v1), (Value.Int i2 as v2)) ->
            conclude <| rule(
                derive <| Judge.Eval(env, e1, v1),
                derive <| Judge.Eval(env, e2, v2),
                derive <| judge(i1, i2, r)
            )
        | _ -> failwith "Invalid type"
    
    match judge with
    | Eval(_, Expr.Int i, Value.Int i') when i = i' -> conclude EInt
    | Eval(_, Expr.Bool b, Value.Bool b') when b = b' -> conclude EBool
    | Eval(Env((x, v)::_), Var x', v') when x = x' && v = v' -> conclude EVar1
    | Eval(Env((y, _)::E), Var x, v) when y <> x ->
        conclude <| EVar2(derive <| Eval(Env E, Var x, v))
    | Eval(env, Expr.Plus(e1, e2), Value.Int i3) ->
        deriveIntBinOp Rule.EPlus Judge.Plus env e1 e2 i3
    | Eval(env, Expr.Minus(e1, e2), Value.Int i3) ->
        deriveIntBinOp Rule.EMinus Judge.Minus env e1 e2 i3
    | Eval(env, Expr.Times(e1, e2), Value.Int i3) ->
        deriveIntBinOp Rule.ETimes Judge.Times env e1 e2 i3
    | Eval(env, Expr.Lt(e1, e2), Value.Bool b3) ->
        deriveIntBinOp Rule.ELt Judge.Lt env e1 e2 b3
    | Eval(env, Expr.If(e, et, ef), v) ->
        match (eval env e) with
        | (Value.Bool true) ->
            conclude <| Rule.EIfT(
                derive <| Judge.Eval(env, e, Value.Bool true),
                derive <| Judge.Eval(env, et, v)
            )
        | (Value.Bool false) ->
            conclude <| Rule.EIfF(
                derive <| Judge.Eval(env, e, Value.Bool false),
                derive <| Judge.Eval(env, ef, v)
            )
        | _ -> failwith "Invalid type"
    | Eval((Env E as env), Expr.Let(x, e1, e2), v) ->
        let v1 = eval env e1
        conclude <| Rule.ELet(
            derive <| Judge.Eval(env, e1, v1),
            derive <| Judge.Eval(Env((x, v1)::E), e2, v)
        )
    | Eval((Env E as env), Expr.LetRec(x, y, e1, e2), v) ->
        conclude <| Rule.ELetRec(
            derive <| Judge.Eval(Env((x, Value.FuncRec(env, x, y, e1))::E), e2, v)
        )
    | Eval(env, Expr.Func(x, e), Value.Func(env', x', e')) when env = env' && x = x' && e = e' ->
        conclude <| Rule.EFun
    | Eval(env, Expr.App(e1, e2), v) ->
        match (eval env e1, eval env e2) with
        | ((Value.Func(Env E2, x, e0) as v1), v2) ->
            conclude <| Rule.EApp(
                derive <| Judge.Eval(env, e1, v1),
                derive <| Judge.Eval(env, e2, v2),
                derive <| Judge.Eval(Env((x, v2)::E2), e0, v)
            )
        | ((Value.FuncRec(Env E2, x, y, e0) as v1), v2) ->
            conclude <| Rule.EAppRec(
                derive <| Judge.Eval(env, e1, v1),
                derive <| Judge.Eval(env, e2, v2),
                derive <| Judge.Eval(Env((y, v2)::(x, v1)::E2), e0, v)
            )
        | (_, _) -> failwith "e1 must be function"
    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude <| Rule.BPlus
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude <| Rule.BMinus
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude <| Rule.BTimes
    | Lt(i1, i2, b3)    when b3 = (i1 < i2) -> conclude <| Rule.BLt
    | j ->
        failwithf "Invalid input(maybe unimplemented): %A" j

"|- let rec fib = fun n -> if n < 3 then 1 else fib (n - 1) + fib (n - 2) in
   fib 5
  evalto 5" 
|> parse Parser.eval
|> function
    | Success s -> s.Value
    | Failure e -> failwith (sprintf "%A" e)
|> fun t -> printfn "%A" t; t
(*|> eval (Env [])
|> fun v -> printfn $"{v}"*)
|> derive
|> printDerivation Judge.print Rule.mapRule
|> printfn "%s"