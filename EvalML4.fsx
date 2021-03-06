#r "nuget: Scanrat"
open System
open ScanRat.ScanRat

type Var = string

type Value =
    | Int of int
    | Bool of bool
    | Nil
    | Cons of Value * Value
    (* (E)[fun x -> e] *)
    | Func of Env * Var * Expr
    (* (E)[rec x = fun y -> e] *)
    | FuncRec of Env * Var * Var * Expr
    with
        override this.ToString() =
            let rec print = function
                | Int i -> string i
                | Bool true -> "true"
                | Bool false -> "false"
                | Nil -> "[]"
                | Cons((Cons _ as v1), v2) -> "(" + print v1 + ")::" + print v2
                | Cons(v1, v2) -> print v1 + "::" + print v2
                | Func(env, x, e) -> $"({env})[fun {x} -> {e}]"
                | FuncRec(env, x, y, e) -> $"({env})[rec {x} = fun {y} -> {e}]"
            print this
and Expr =
    | Int of int
    | Bool of bool
    | Nil
    | Cons of Expr * Expr
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
    (* match e1 with [] -> e2 | x::y -> e3 *)
    | Match of Expr * Expr * Var * Var * Expr
    with
        override this.ToString() =
            let rec print = function
                | Int i -> (Value.Int i).ToString()
                | Bool b -> (Value.Bool b).ToString()
                | Var x -> x
                | Nil -> "[]"
                | (Cons _) as e -> "(" + printCons e + ")"
                | (Plus _) as e -> "(" + printPlus e + ")"
                | (Minus _) as e -> "(" + printMinus e + ")"
                | (Times _) as e -> "(" + printTimes e + ")"
                | Lt(e1, e2) -> "(" + (print e1) + " < " + (print e2) + ")"
                | If(e, et, ef) -> $"(if {print e} then {print et} else {print ef})"
                | Let(x, e1, e2) -> $"(let {x} = {print e1} in {print e2})"
                | LetRec(x, y, e1, e2) -> $"(let rec {x} = fun {y} -> {print e1} in {print e2})"
                | Func(x, e) -> $"(fun {x} -> {e})"
                | App _ as e -> "(" + printApp e + ")"
                | Match(e1, e2, x, y, e3) -> $"(match {print e1} with [] -> {print e2} | {x}::{y} -> {print e3})"
            and printCons = function
                | Cons((Cons _ as e1), e2) -> (print e1) + "::" + (printCons e2)
                | Cons(e1, e2) -> (printCons e1) + "::" + (printCons e2)
                | e -> print e
            and printApp = function
                | App(e1, (App _ as e2)) -> printApp e1 + " " + print e2
                | App(e1, e2) -> printApp e1 + " " + printApp e2
                | e -> print e
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

type Derivation =
    | Derivation of Judge * string * Derivation list

let printDerivation printJudge =
    let rec deriv level (Derivation(judge, name, derivs)) =
        String.replicate level "  " + $"%s{printJudge judge} by {rule level name derivs}"
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
    let spaceChars = " \t\n"

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
        ) / (~~"if" |- ~~"then" |- ~~"else" |- ~~"let" |- ~~"rec" |- ~~"in" |- ~~"fun" |- ~~"match" |- ~~"with" |- ~~"evalto")
    
    let value = production "value"
    let expr = production "expr"
    let env = production "env"

    let valueTerm = production "valueTerm"
    valueTerm.rule
        <- digits --> Value.Int
        |- bool --> Value.Bool
        |- ~~"[" + sp + ~~"]" --> fun _ -> Value.Nil
        |- (~~"(" +. sp +. env .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + expr .+ sp .+ ~~"]")
            --> fun ((env, x), e) -> Value.Func(env, x, e)
        |- (~~"(" +. sp +. env .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ sp .+ ~~"rec" .+ sp1 + ident .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + expr .+ sp .+ ~~"]")
            --> fun (((env, x), y), e) -> Value.FuncRec(env, x, y, e)
    value.rule
        <- valueTerm .+ sp .+ ~~"::" .+ sp + value --> Value.Cons
        |- valueTerm

    let term = production "term"
    term.rule
        <- ~~"(" +. sp +. expr .+ sp .+ ~~")"
        |- digits --> Expr.Int
        |- bool --> Expr.Bool
        |- ident --> Expr.Var
        |- ~~"[" + sp + ~~"]" --> fun _ -> Expr.Nil
    let app = production "app"
    app.rule
        <- app .+ sp1 + term --> Expr.App
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
        |- (
            ~~"match" +. sp1 +. expr .+ sp1 .+ ~~"with" .+ sp1
            .+ ~~"[" .+ sp .+ ~~"]" .+ sp .+ ~~"->" .+ sp + expr
            .+ sp .+ ~~"|" .+ sp + ident .+ sp .+ ~~"::" .+ sp + ident .+ sp .+ ~~"->" .+ sp + expr
        ) --> fun ((((e1, e2), x), y), e3) -> Expr.Match(e1, e2, x, y, e3)
        |- term .+ sp .+ ~~"::" .+ sp + expr --> Expr.Cons
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
    | Expr.Int i -> Value.Int i
    | Expr.Bool b -> Value.Bool b
    | Expr.Nil -> Value.Nil
    | Expr.Cons(e1, e2) -> Value.Cons(eval env e1, eval env e2)
    | Expr.Var x ->
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
        | Value.Func(Env E2, x, e), v2 ->
            eval (Env((x, v2)::E2)) e
        | Value.FuncRec(Env E2, x, y, e0) as v1, v2 ->
            let env' = Env((y, v2)::(x, v1)::E2)
            eval env' e0
        | _, _ -> failwith "Invalid type(not func)"
    | Match(e1, e2, x, y, e3) ->
        match (eval env e1) with
        | Value.Nil -> eval env e2
        | Value.Cons(v1, v2) ->
            let (Env el) = env
            eval (Env((y, v2)::(x, v1)::el)) e3
        | _ -> failwith "Invalid type(not list)"


let rec derive judge =
    let conclude name derivs = Derivation(judge, name, derivs)

    let deriveIntBinop name judge env e1 e2 r =
        match(eval env e1, eval env e2) with
        | (Value.Int i1 as v1), (Value.Int i2 as v2) ->
            conclude name [
                derive <| Eval(env, e1, v1);
                derive <| Eval(env, e2, v2);
                derive <| judge(i1, i2, r)
            ]
        | _ -> failwith "Invalid type"
    
    match judge with
    | Eval(_, Expr.Int i, Value.Int i') when i = i' -> conclude "E-Int" []
    | Eval(_, Expr.Bool b, Value.Bool b') when b = b' -> conclude "E-Bool" []
    | Eval(_, Expr.Nil, Value.Nil) -> conclude "E-Nil" []
    | Eval(env, Expr.Cons(e1, e2), Value.Cons(v1, v2)) ->
        conclude "E-Cons" [
            derive <| Eval(env, e1, v1);
            derive <| Eval(env, e2, v2);
        ]
    | Eval(Env el, Var x, v) ->
        let _, v' = el |> List.find (fun (x', _) -> x' = x)
        if v = v' then conclude "E-Var" [] else failwith "invalid Env"
    | Eval(env, Expr.Plus(e1, e2), Value.Int i3) ->
        deriveIntBinop "E-Plus" Judge.Plus env e1 e2 i3
    | Eval(env, Expr.Minus(e1, e2), Value.Int i3) ->
        deriveIntBinop "E-Minus" Judge.Minus env e1 e2 i3
    | Eval(env, Expr.Times(e1, e2), Value.Int i3) ->
        deriveIntBinop "E-Times" Judge.Times env e1 e2 i3
    | Eval(env, Expr.Lt(e1, e2), Value.Bool b3) ->
        deriveIntBinop "E-Lt" Judge.Lt env e1 e2 b3
    | Eval(env, Expr.If(e1, e2, e3), v) ->
        let v1 = eval env e1
        match v1 with
        | Value.Bool true ->
            conclude "E-IfT" [
                derive <| Eval(env, e1, v1);
                derive <| Eval(env, e2, v);
            ]
        | Value.Bool false ->
            conclude "E-IfF" [
                derive <| Eval(env, e1, v1);
                derive <| Eval(env, e3, v);
            ]
        | _ -> failwith "Invalid type"
    | Eval((Env el as env), Expr.Let(x, e1, e2), v) ->
        let v1 = eval env e1
        conclude "E-Let" [
            derive <| Eval(env, e1, v1);
            derive <| Eval(Env((x, v1)::el), e2, v)
        ]
    | Eval(env, Expr.Func(x, e), Value.Func(env', x', e')) when env = env' && x = x' && e = e' -> conclude "E-Fun" []
    | Eval((Env el as env), Expr.LetRec(x, y, e1, e2), v) ->
        conclude "E-LetRec" [
            derive <| Eval(Env((x, Value.FuncRec(env, x, y, e1))::el), e2, v)
        ]
    | Eval(env, Expr.App(e1, e2), v) ->
        match (eval env e1, eval env e2) with
        | (Value.Func(Env el2, x, e0) as v1), v2 ->
            conclude "E-App" [
                derive <| Eval(env, e1, v1);
                derive <| Eval(env, e2, v2);
                derive <| Eval(Env((x, v2)::el2), e0, v)
            ]
        | (Value.FuncRec(Env el2, x, y, e0) as v1), v2 ->
            conclude "E-AppRec" [
                derive <| Eval(env, e1, v1);
                derive <| Eval(env, e2, v2);
                derive <| Eval(Env((y, v2)::(x, v1)::el2), e0, v)
            ]
        | _, _ -> failwith "Invalid type(e1 must be function)"
    | Eval((Env el as env), Expr.Match(e1, e2, x, y, e3), v) ->
        match (eval env e1) with
        | Value.Nil ->
            conclude "E-MatchNil" [
                derive <| Eval(env, e1, Value.Nil);
                derive <| Eval(env, e2, v);
            ]
        | Value.Cons(v1, v2) ->
            conclude "E-MatchCons" [
                derive <| Eval(env, e1, Value.Cons(v1, v2));
                derive <| Eval(Env((y, v2)::(x, v1)::el), e3, v);
            ]
        | _ -> failwith "Invalid type(e1 must be list)"
    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude "B-Plus" []
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude "B-Minus" []
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude "B-Times" []
    | Lt   (i1, i2, b3) when b3 = (i1 < i2) -> conclude "B-Lt" []
    | j -> 
        failwithf "Invalid input(maybe unimplemented): %A" j

"|- let rec apply = fun l -> fun x ->
      match l with [] -> x | f :: l -> apply l (f x) in
    apply ((fun x -> x * x) :: (fun y -> y + 3) :: []) 4 
   evalto 19"
|> parse Parser.eval
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> printfn "%A" t; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"