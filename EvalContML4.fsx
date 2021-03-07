#r "nuget: ScanRat"
open System
open ScanRat.ScanRat

type Var = string

type Op = Plus | Minus | Times | Lt
    with
        override this.ToString() =
            match this with
            | Plus -> "+"
            | Minus -> "-"
            | Times -> "*"
            | Lt -> "<"

type Value =
    | Int of int
    | Bool of bool
    (* [] *)
    | Nil
    (* v1::v2 *)
    | Cons of Value * Value
    (* (E)[fun x -> e] *)
    | Func of Env * Var * Expr
    (* (E)[rec x = fun y -> e] *)
    | FuncRec of Env * Var * Var * Expr
    (* [k] *)
    | Cont of Cont
    with
        override this.ToString() =
            match this with
                | Int i when i < 0 -> $"({i})"
                | Int i -> $"{i}"
                | Bool true -> "true"
                | Bool false -> "false"
                | Nil -> "[]"
                | Cons((Cons _ as v1), v2) -> $"({v1})::{v2}"
                | Cons(v1, v2) -> $"{v1}::{v2}"
                | Func(env, x, e) -> $"({env})[fun {x} -> {e}]"
                | FuncRec(env, x, y, e) -> $"({env})[rec {x} = fun {y} -> {e}]"
                | Cont k -> $"[{k}]"
            
and Expr =
    | Int of int
    | Bool of bool
    | Var of Var
    (* e1 op e2 *)
    | BinOp of Expr * Op * Expr
    (* if e1 then e2 else e3 *)
    | If of Expr * Expr * Expr
    (* let x = e1 in e2 *)
    | Let of Var * Expr * Expr
    (* fun x -> e *)
    | Func of Var * Expr
    (* e1 e2 *)
    | App of Expr * Expr
    (* let rec x = fun y -> e1 in e2 *)
    | LetRec of Var * Var * Expr * Expr
    (* [] *)
    | Nil
    (* e1::e2 *)
    | Cons of Expr * Expr
    (* match e1 with [] -> e2 | x::y -> e3 *)
    | Match of Expr * Expr * Var * Var * Expr
    (* letcc x in e *)
    | LetCc of Var * Expr
    with
        override this.ToString() =
            let rec print = function
                | Int i -> (Value.Int i).ToString()
                | Bool b -> (Value.Bool b).ToString()
                | Var x -> x
                | BinOp(_, op, _) as e -> "(" + printBinop op e + ")"
                | If(e1, e2, e3) -> $"(if {print e1} then {print e2} else {print e3})"
                | Let(x, e1, e2) -> $"(let {x} = {e1} in {e2})"
                | Func(x, e) -> $"(fun {x} -> {e})"
                | App _ as e -> "(" + printApp e + ")"
                | LetRec(x, y, e1, e2) -> $"(let rec {x} = fun {y} -> {e1} in {e2})"
                | Nil -> "[]"
                | Cons _ as e -> "(" + printCons e + ")"
                | Match(e1, e2, x, y, e3) -> $"(match {e1} with [] -> {e2} | {x}::{y} -> {e3})"
                | LetCc(x, e) -> $"(letcc {x} in {e})"
            and printBinop op = function
                | BinOp(e1, op', e2) when op = op' -> printBinop op e1 + $" {op} " + printBinop op e2
                | e -> print e
            and printApp = function
                | App(e1, (App _ as e2)) -> printApp e1 + " " + print e2
                | App(e1, e2) -> printApp e1 + " " + printApp e2
                | e -> print e
            and printCons = function
                | Cons((Cons _ as e1), e2) -> print e1 + "::" + printCons e2
                | Cons(e1, e2) -> printCons e1 + "::" + printCons e2
                | e -> print e
            print this

and Cont =
    | Ret
    (* {E |- _ op e} >> k *)
    | BinOpL of Env * Op * Expr * Cont
    (* {v op _} >> k *)
    | BinOpR of Value * Op * Cont
    (* {E |- if _ then e else e} >> k *)
    | If of Env * Expr * Expr * Cont
    (* {E |- let x = _ in e} >> k *)
    | Let of Env * Var * Expr * Cont
    (* {E |- _ e} >> k *)
    | AppL of Env * Expr * Cont
    (* {v _} >> k *)
    | AppR of Value * Cont
    (* {E |- _::e} >> k *)
    | ConsL of Env * Expr * Cont
    (* {v::_} >> k *)
    | ConsR of Value * Cont
    (* {E |- match _ with [] -> e1 | x::y -> e2} >> k *)
    | Match of Env * Expr * Var * Var * Expr * Cont
    with
        override this.ToString() =
            let printEnv env =
                let env = env.ToString()
                let s = if env = "" then "" else " "
                $"{env}{s}|-"
            match this with
            | Ret -> "_"
            | BinOpL(env, op, e, k) -> $"{{{printEnv env} _ {op} {e}}} >> {k}"
            | BinOpR(v, op, k) -> $"{{{v} {op} _}} >> {k}"
            | If(env, e1, e2, k) -> $"{{{printEnv env} if _ then {e1} else {e2}}} >> {k}"
            | Let(env, x, e, k) -> $"{{{printEnv env} let {x} = _ in {e}}} >> {k}"
            | AppL(env, e, k) -> $"{{{printEnv env} _ {e}}} >> {k}"
            | AppR(v, k) -> $"{{{v} _}} >> {k}"
            | ConsL(env, e, k) -> $"{{{printEnv env} _::{e}}} >> {k}"
            | ConsR(v, k) -> $"{{{v}::_}} >> {k}"
            | Match(env, e1, x, y, e2, k) -> $"{{{printEnv env} match _ with [] -> {e1} | {x}::{y} -> {e2}}} >> {k}"

and Env = Env of (Var * Value) list
    with
        override this.ToString() =
            let rec print = function
                | [] -> ""
                | [(x, v)] -> $"{x} = {v}"
                | (x, v)::l -> (print l) + $", {x} = {v}"
            let (Env l) = this
            print l

type Judge =
    (* E |- e >> k evalto v *)
    | EvalE of Env * Expr * Cont * Value
    (* v1 => k evalto v2 *)
    | EvalV of Value * Cont * Value
    | Plus of int * int * int
    | Minus of int * int * int
    | Times of int * int * int
    | Lt of int * int * bool
    with
        override this.ToString() =
            match this with
            | EvalE(env, e, k, v) ->
                let env = env.ToString()
                let s = if env = "" then "" else " "
                $"{env}{s}|- {e} >> {k} evalto {v}"
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
    let identifierFirstChars =
        let lower = "abcdefghijklmnopqrstuvwxyz"
        lower + lower.ToUpper() + "_"
    let identifierChars = identifierFirstChars + digitChars + "'"
    let keywords = ["if"; "then"; "else"; "let"; "rec"; "in"; "fun"; "match"; "with"; "letcc"; "evalto"]

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

    let ident = production "ident"
    ident.rule
        <- (
            ident + (oneOf identifierChars) --> fun (s, c) -> s + string c
            |- oneOf identifierFirstChars --> string
        ) / (keywords |> List.map (~~) |> List.reduce (|-))

    let value = production "value"
    let expr = production "expr"
    let cont = production "cont"
    let env = production "env"

    value.rule
        <- digits --> Value.Int
        |- bool --> Value.Bool
        |- ~~"[" +. sp +. cont .+ sp .+ ~~"]" --> Value.Cont

    let term =
        ~~"(" +. sp +. expr .+ sp .+ ~~")"
        |- digits --> Expr.Int
        |- bool --> Expr.Bool
        |- ident --> Expr.Var
        |- ~~"[" + sp + ~~"]" --> fun _ -> Expr.Nil
        |- ~~"if" +. sp1 +. expr .+ sp1 .+ ~~"then" .+ sp1 + expr .+ sp1 .+ ~~"else" .+ sp1 + expr
            --> fun ((e1, e2), e3) -> Expr.If(e1, e2, e3)
        |- ~~"let" +. sp1 +. ~~"rec" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + expr .+ sp1 .+ ~~"in" .+ sp1 + expr
            --> fun (((x, y), e1), e2) -> Expr.LetRec(x, y, e1, e2)
        |- ~~"let" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp + expr .+ sp1 .+ ~~"in" .+ sp1 + expr
            --> fun ((x, e1), e2) -> Expr.Let(x, e1, e2)
        |- ~~"fun" +. sp1 +. ident .+ sp .+ ~~"->" .+ sp + expr --> Expr.Func
        |- 
            ~~"match" +. sp1 +. expr .+ sp1 .+ ~~"with" .+ sp1
            .+ ~~"[" .+ sp .+ ~~"]" .+ sp .+ ~~"->" .+ sp + expr
            .+ sp .+ ~~"|" .+ sp + ident .+ sp .+ ~~"::" .+ sp + ident .+ sp .+ ~~"->" .+ sp + expr
            --> fun ((((e1, e2), x), y), e3) -> Expr.Match(e1, e2, x, y, e3)
        |- ~~"letcc" +. sp1 +. ident .+ sp1 .+ ~~"in" .+ sp1 + expr --> Expr.LetCc
    let app = production "app"
    app.rule
        <- app .+ sp1 + term --> Expr.App
        |- term
    let times = production "times"
    times.rule
        <- times .+ sp .+ ~~"*" .+ sp + app --> fun (e1, e2) -> Expr.BinOp(e1, Op.Times, e2)
        |- app
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
        <- term .+ sp .+ ~~"::" .+ sp + expr --> Expr.Cons
        |- lessThan
    
    let op = (~~"+" --> fun _ -> Op.Plus) |- (~~"-" --> fun _ -> Op.Minus) |- (~~"*" --> fun _ -> Op.Times) |- (~~"<" --> fun _ -> Op.Lt)
    let contTail = (~~">>" +. sp +. cont) |- (~~"" --> fun _ -> Cont.Ret)
    cont.rule
        <- ~~"{" +. sp +. value .+ sp + op .+ sp .+ ~~"_" .+ sp .+ ~~"}" .+ sp + contTail
            --> fun ((v, op), k) -> Cont.BinOpR(v, op, k)
        |- ~~"_" --> fun _ -> Cont.Ret
    
    let bind = ident .+ sp .+ ~~"=" .+ sp + value
    env.rule
        <- env .+ sp .+ ~~"," .+ sp + bind --> fun (Env l, b) -> Env(b::l)
        |- bind --> fun b -> Env[b]
        |- ~~"" --> fun _ -> Env []

    let judge =
        env .+ sp .+ ~~"|-" .+ sp + expr .+ sp + contTail .+ sp .+ ~~"evalto" .+ sp1 + value --> fun (((env, e), k), v) -> Judge.EvalE(env, e, k, v)

let rec derive judge =
    let conclude name derivs = Derivation(judge, name, derivs)

    match judge with
    | EvalE(_, Expr.Int i, k, v) -> conclude "E-Int" [derive <| EvalV(Value.Int i, k, v)]
    | EvalE(_, Expr.Bool b, k, v) -> conclude "E-Bool" [derive <| EvalV(Value.Bool b, k, v)]
    | EvalE(env, Expr.If(e1, e2, e3), k, v) ->
        conclude "E-If" [derive <| EvalE(env, e1, Cont.If(env, e2, e3, k), v)]
    | EvalE(env, Expr.BinOp(e1, op, e2), k, v) ->
        conclude "E-BinOp" [derive <| EvalE(env, e1, Cont.BinOpL(env, op, e2, k), v)]
    | EvalE(Env l, Expr.Var x, k, v2) ->
        match (l |> List.tryFind (fun (x', _) -> x' = x)) with
        | Some(_, v1) -> conclude "E-Var" [derive <| EvalV(v1, k, v2)]
        | None -> Derivation.Incomplete judge
    | EvalE(env, Expr.Let(x, e1, e2), k, v) ->
        conclude "E-Let" [derive <| EvalE(env, e1, Cont.Let(env, x, e2, k), v)]
    | EvalE(env, Expr.Func(x, e), k, v) ->
        conclude "E-Fun" [derive <| EvalV(Value.Func(env, x, e), k, v)]
    | EvalE(env, Expr.App(e1, e2), k, v) ->
        conclude "E-App" [derive <| EvalE(env, e1, Cont.AppL(env, e2, k), v)]
    | EvalE((Env l as env), Expr.LetRec(x, y, e1, e2), k, v) ->
        conclude "E-LetRec" [
            derive <| EvalE(Env((x, Value.FuncRec(env, x, y, e1))::l), e2, k, v)
        ]
    | EvalE(_, Expr.Nil, k, v) -> conclude "E-Nil" [derive <| EvalV(Value.Nil, k, v)]
    | EvalE(env, Expr.Cons(e1, e2), k, v) ->
        conclude "E-Cons" [derive <| EvalE(env, e1, Cont.ConsL(env, e2, k), v)]
    | EvalE(env, Expr.Match(e1, e2, x, y, e3), k, v) ->
        conclude "E-Match" [
            derive <| EvalE(env, e1, Cont.Match(env, e2, x, y, e3, k), v)
        ]
    | EvalE(Env l, Expr.LetCc(x, e), k, v) ->
        conclude "E-LetCc" [
            derive <| EvalE(Env((x, Value.Cont k)::l), e, k, v)
        ]

    | EvalV(v, Cont.Ret, v') when v = v' -> conclude "C-Ret" []
    | EvalV(v1, Cont.BinOpL(env, op, e, k), v2) ->
        conclude "C-EvalR" [derive <| EvalE(env, e, Cont.BinOpR(v1, op, k), v2)]
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
    | EvalV(Value.Bool true, Cont.If(env, e, _, k), v) ->
        conclude "C-IfT" [derive <| EvalE(env, e, k, v)]
    | EvalV(Value.Bool false, Cont.If(env, _, e, k), v) ->
        conclude "C-IfF" [derive <| EvalE(env, e, k, v)]
    | EvalV(v1, Cont.Let(Env l, x, e, k), v2) ->
        conclude "C-LetBody" [derive <| EvalE(Env((x, v1)::l), e, k, v2)]
    | EvalV(v1, Cont.AppL(env, e, k), v2) ->
        conclude "C-EvalArg" [derive <| EvalE(env, e, Cont.AppR(v1, k), v2)]
    | EvalV(v1, Cont.AppR(Value.Func(Env l, x, e), k), v2) ->
        conclude "C-EvalFun" [derive <| EvalE(Env((x, v1)::l), e, k, v2)]
    | EvalV(v1, Cont.AppR((Value.FuncRec(Env l, x, y, e) as v0), k), v2) ->
        conclude "C-EvalFunR" [
            derive <| EvalE(Env((y, v1)::(x, v0)::l), e, k, v2)
        ]
    | EvalV(v1, Cont.AppR(Value.Cont k, _), v2) -> conclude "C-EvalFunC" [derive <| EvalV(v1, k, v2)]
    | EvalV(v1, Cont.ConsL(env, e, k), v2) -> conclude "C-EvalConsR" [derive <| EvalE(env, e, Cont.ConsR(v1, k), v2)]
    | EvalV(v2, Cont.ConsR(v1, k), v3) -> conclude "C-Cons" [derive <| EvalV(Value.Cons(v1, v2), k, v3)]
    | EvalV(Value.Nil, Cont.Match(env, e1, _, _, _, k), v) -> conclude "C-MatchNil" [derive <| EvalE(env, e1, k, v)]
    | EvalV(Value.Cons(v1, v2), Cont.Match(Env l, _, x, y, e2, k), v) ->
        conclude "C-MatchCons" [
            derive <| EvalE(Env((y, v2)::(x, v1)::l), e2, k, v)
        ]

    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude "B-Plus" []
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude "B-Minus" []
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude "B-Times" []
    | Lt   (i1, i2, b3) when b3 = (i1 < i2) -> conclude "B-Lt" []
    | j ->
        Derivation.Incomplete j

"|- let findneg = fun l ->
     letcc k in
       let rec aux = fun l -> match l with 
         [] -> false 
       | x :: l -> if x < 0 then k true else aux l
     in aux l
   in findneg (1 :: 2 :: -3 :: 4 :: []) evalto true"
|> parse Parser.judge
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> eprintfn "%A" t; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"