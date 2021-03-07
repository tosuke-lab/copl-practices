#r "nuget: Scanrat"
open System
open ScanRat.ScanRat

type OptionBuilder () =
    member __.Bind(x, f) = Option.bind f x
    member __.Return(x) = Some x
    member __.Zero() = None
let option = OptionBuilder()

type Var = string
type Loc = string

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
    (* @l *)
    | Loc of Loc
    (* (E)[fun x -> e] *)
    | Fun of Env * Var * Exp
    (* (E)[rec x = fun y -> e] *)
    | FunRec of Env * Var * Var * Exp
    with
        override this.ToString() =
            match this with
                | Int i when i < 0 -> $"({i})"
                | Int i -> $"{i}"
                | Bool true -> "true"
                | Bool false -> "false"
                | Loc l -> $"@{l}"
                | Fun(env, x, e) -> $"({env})[fun {x} -> {e}]"
                | FunRec(env, x, y, e) -> $"({env})[rec {x} = fun {y} -> {e}]"
and Exp =
    | Int of int
    | Bool of bool
    | Var of Var
    (* e1 op e2 *)
    | BinOp of Exp * Op * Exp
    (* if e1 then e2 else e3 *)
    | If of Exp * Exp * Exp
    (* let x = e1 in e2 *)
    | Let of Var * Exp * Exp
    (* fun x -> e *)
    | Fun of Var * Exp
    (* e1 e2 *)
    | App of Exp * Exp
    (* let rec x = fun y -> e1 in e2 *)
    | LetRec of Var * Var * Exp * Exp
    (* ref e *)
    | Ref of Exp
    (* !e *)
    | Deref of Exp
    (* e1 := e2 *)
    | Assign of Exp * Exp
    with
        override this.ToString() =
            let rec print = function
                | Int i -> (Value.Int i).ToString()
                | Bool b -> (Value.Bool b).ToString()
                | Var x -> x
                | BinOp(_, op, _) as e -> "(" + printBinop op e + ")"
                | If(e1, e2, e3) -> $"if {print e1} then {print e2} else {print e3}"
                | Let(x, e1, e2) -> $"let {x} = {e1} in {e2}"
                | Fun(x, e) -> $"fun {x} -> {e}"
                | App _ as e -> "(" + printApp e + ")"
                | LetRec(x, y, e1, e2) -> $"let rec {x} = fun {y} -> {e1} in {e2}"
                | Ref e -> $"ref({e})"
                | Deref e -> $"!({e})"
                | Assign(e1, e2) -> $"{e1} := {e2}"
            and printBinop op = function
                | BinOp(e1, op', e2) when op = op' -> printBinop op e1 + $" {op} " + printBinop op e2
                | e -> print e
            and printApp = function
                | App(e1, (App _ as e2)) -> printApp e1 + " " + print e2
                | App(e1, e2) -> printApp e1 + " " + printApp e2
                | e -> print e
            print this


and Env =
    | Empty
    | Bind of Env * Var * Value
    with
        override this.ToString() =
            match this with
            | Empty -> ""
            | Bind(Empty, x, v) -> $"{x} = {v}"
            | Bind(env, x, v) -> $"{env}, {x} = {v}"
and Store =
    | EmptyS
    | Block of Store * Loc * Value
    with
         override this.ToString() =
            match this with
            | EmptyS -> ""
            | Block(EmptyS, l, v) -> $"@{l} = {v}"
            | Block(store, l, v) -> $"{store}, @{l} = {v}"

type Judge =
    (* S1 / E |- e evalto v / S2 *)
    | Eval of Store * Env * Exp * Value * Store
    | Plus of int * int * int
    | Minus of int * int * int
    | Times of int * int * int
    | Lt of int * int * bool
    with
        override this.ToString() =
            match this with
            | Eval(s1, env, e, v, s2) ->
                let s1 =
                    match s1 with
                    | Block _ -> $"{s1} / "
                    | EmptyS -> ""
                let env =
                    match env with
                    | Bind _ -> $"{env} |- "
                    | Empty -> $"|- "
                let s2 =
                    match s2 with
                    | Block _ -> $" / {s2}"
                    | EmptyS -> ""
                $"{s1}{env}{e} evalto {v}{s2}"
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
    let keywords = [| "if"; "then"; "else"; "let"; "rec"; "in"; "fun"; "ref"; "evalto" |]

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

    let value = production "value"
    let exp = production "exp"
    let env = production "env"
    let store = production "store"

    value.rule
        <- digits --> Value.Int
        |- bool --> Value.Bool
        |- ~~"@" +. ident --> Value.Loc
        |- ~~"(" +. sp +. env .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + exp .+ sp .+ ~~"]" --> fun ((env, x), e) -> Value.Fun(env, x, e)
    
    let term = production "term"
    term.rule
        <- ~~"(" +. sp +. exp .+ sp .+ ~~")"
        |- digits --> Exp.Int
        |- bool --> Exp.Bool
        |- ident --> Exp.Var
        |- ~~"if" +. sp1 +. exp .+ sp1 .+ ~~"then" .+ sp1 + exp .+ sp1 .+ ~~"else" .+ sp1 + exp
            --> fun ((e1, e2), e3) -> Exp.If(e1, e2, e3)
        |- ~~"let" +. sp1 +. ~~"rec" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + exp .+ sp1 .+ ~~"in" .+ sp1 + exp
            --> fun (((x, y), e1), e2) -> Exp.LetRec(x, y, e1, e2)
        |- ~~"let" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp + exp .+ sp1 .+ ~~"in" .+ sp1 + exp
            --> fun ((x, e1), e2) -> Exp.Let(x, e1, e2)
        |- ~~"fun" +. sp1 +. ident .+ sp .+ ~~"->" .+ sp + exp --> Exp.Fun
        |- ~~"ref" +. sp1 +. term  --> Exp.Ref
        |- ~~"!" +. sp +. term --> Exp.Deref
    let app = production "app"
    app.rule
        <- app .+ sp1 + term --> Exp.App
        |- term
    let times = production "times"
    times.rule
        <- times .+ sp .+ ~~"*" .+ sp + app --> fun (e1, e2) -> Exp.BinOp(e1, Op.Times, e2)
        |- app
    let plus = production "plus"
    plus.rule
        <- plus .+ sp + ((~~"+" --> fun _ -> Op.Plus) |- (~~"-" --> fun _ -> Op.Minus)) .+ sp + times
            --> fun ((e1, op), e2) -> Exp.BinOp(e1, op, e2)
        |- times
    let lessThan = production "lessThan"
    lessThan.rule
        <- lessThan .+ sp .+ ~~"<" .+ sp + plus --> fun (e1, e2) -> Exp.BinOp(e1, Op.Lt, e2)
        |- plus
    exp.rule
        <- lessThan .+ sp .+ ~~":=" .+ sp + exp --> Exp.Assign
        |- lessThan
    
    let bind = ident .+ sp .+ ~~"=" .+ sp + value
    env.rule
        <- env .+ sp .+ ~~"," .+ sp + bind --> fun (env, (x, v)) -> Bind(env, x, v)
        |- bind --> fun (x, v) -> Bind(Empty, x, v)
        |- ~~"" --> fun _ -> Empty
    
    let block = ~~"@" +. ident .+ sp .+ ~~"=" .+ sp + value
    store.rule
        <- store .+ sp .+ ~~"," .+ sp + block --> fun (store, (l, v)) -> Block(store, l, v)
        |- block --> fun (l, v) -> Block(EmptyS, l, v) 
        |- ~~"" --> fun _ -> EmptyS
    
    let judge =
        ((store .+ sp .+ ~~"/" .+ sp) |- (~~"" --> fun _ -> EmptyS)) + env .+ sp .+ ~~"|-" .+ sp + exp .+ sp1 .+ ~~"evalto" .+ sp1 + value .+ sp .+ ~~"/" .+ sp + store
        --> fun ((((s1, env), e), v), s2) -> Judge.Eval(s1, env, e, v, s2)

let rec eval fl env = function
    | s, Exp.Int i -> Some(fl, s, Value.Int i)
    | s, Exp.Bool b -> Some(fl, s, Value.Bool b)
    | s1, Exp.If(e1, e2, e3) ->
        eval fl env (s1, e1)
        |> Option.bind(
            function
            | fl, s2, Value.Bool true -> eval fl env (s2, e2)
            | fl, s2, Value.Bool false -> eval fl env (s2, e3)
            | _, _, _ -> None
        )
    | s1, Exp.BinOp(e1, op, e2) ->
        option {
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! (fl, s3, v2) = eval fl env (s2, e2)
            let! v3 =
                match (v1, op, v2) with
                | Value.Int i1, Op.Plus , Value.Int i2 -> Some(Value.Int(i1 + i2))
                | Value.Int i1, Op.Minus, Value.Int i2 -> Some(Value.Int(i1 - i2))
                | Value.Int i1, Op.Times, Value.Int i2 -> Some(Value.Int(i1 * i2))
                | Value.Int i1, Op.Lt   , Value.Int i2 -> Some(Value.Bool(i1 < i2))
                | _, _, _ -> None
            return fl, s3, v3
        }
    | s, Exp.Var x ->
        let rec find = function
            | Bind(env, y, v) -> if x = y then Some(fl, s, v) else find env
            | Empty -> None
        find env
    | s1, Exp.Let(x, e1, e2) ->
        option {
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! (fl, s3, v) = eval fl (Env.Bind(env, x, v1)) (s2, e2)
            return fl, s3, v
        }
    | s, Exp.Fun(x, e) -> Some(fl, s, Value.Fun(env, x, e))
    | s1, Exp.LetRec(x, y, e1, e2) ->
        eval fl (Env.Bind(env, x, Value.FunRec(env, x, y, e1))) (s1, e2)
    | s1, Exp.App(e1, e2) ->
        option {
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! (fl, s3, v2) = eval fl env (s2, e2)
            let! (fl, s4, v) =
                match v1 with
                | Value.Fun(env2, x, e0) -> eval fl (Env.Bind(env2, x, v2)) (s3, e0)
                | Value.FunRec(env2, x, y, e0) -> eval fl (Env.Bind(Env.Bind(env2, x, v1), y, v2)) (s3, e0)
                | _ -> None
            return fl, s4, v
        }
    | s1, Exp.Ref e ->
        option {
            let! (l, fl) = match fl with [] -> None | l::fl -> Some(l, fl)
            let! (fl, s2, v) = eval fl env (s1, e)
            return fl, Block(s2, l, v), Value.Loc l
        }
    | s1, Exp.Deref e ->
        option {
            let! (fl, s2, v1) = eval fl env (s1, e)
            let! l = match v1 with Value.Loc l -> Some l | _ -> None
            let rec find = function
                | Block(s, l', v) -> if l = l' then Some v else find s
                | EmptyS -> None
            let! v = find s2
            return fl, s2, v
        }
    | s1, Exp.Assign(e1, e2) ->
        option {
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! l = match v1 with Value.Loc l -> Some l | _ -> None
            let! (fl, s3, v) = eval fl env (s2, e2)
            let rec update = function
                | Block(s, l', v') ->
                    if l = l' then
                        Some(Block(s, l, v))
                    else
                        update s |> Option.map (fun s -> Block(s, l', v')) 
                | EmptyS -> None
            let! s4 = update s3
            return fl, s4, v
        }

let diff s1 s2 =
    let rec aux lst = function
        | (Block(_, l1, _) as s1), Block(s2', l2, _) when l1 <> l2 -> aux (l2::lst) (s1, s2')
        | (EmptyS as s1), Block(s2', l2, _) -> aux (l2::lst) (s1, s2')
        | _, _ -> lst
    aux [] (s1, s2)

let rec derive judge =
    let conclude name derivs = Derivation(judge, name, derivs)
    let incomplete = Incomplete judge

    match judge with
    | Eval(s, _, Exp.Int i, Value.Int i', s') when s = s' && i = i' -> conclude "E-Int" []
    | Eval(s, _, Exp.Bool b, Value.Bool b', s') when s = s' && b = b' -> conclude "E-Bool" []
    | Eval(s1, env, Exp.If(e1, e2, e3), v, s3) ->
        option {
            let fl = diff s1 s3
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! name, e, (_, s3', v') =
                match v1 with
                | Value.Bool true -> eval fl env (s2, e2) |> Option.map (fun x -> "E-IfT", e2, x)
                | Value.Bool false -> eval fl env (s2, e3) |> Option.map (fun x -> "E-IfF", e3, x)
                | _ -> None
            if s3 = s3' && v = v' then
                return conclude name [
                    derive <| Eval(s1, env, e1, v1, s2);
                    derive <| Eval(s2, env, e, v, s3);
                ]
        } |> Option.defaultValue incomplete
    | Eval(s1, env, Exp.BinOp(e1, op, e2), v3, s3) ->
        option {
            let fl = diff s1 s3
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! (_, s3, v2) = eval fl env (s2, e2)
            let! (name, j, v3') =
                match v1, op, v2 with
                | Value.Int i1, Op.Plus , Value.Int i2 -> Some("E-Plus" , Judge.Plus(i1, i2, i1 + i2), Value.Int(i1 + i2))
                | Value.Int i1, Op.Minus, Value.Int i2 -> Some("E-Minus", Judge.Minus(i1, i2, i1 - i2), Value.Int(i1 - i2))
                | Value.Int i1, Op.Times, Value.Int i2 -> Some("E-Mult", Judge.Times(i1, i2, i1 * i2), Value.Int(i1 * i2))
                | Value.Int i1, Op.Lt   , Value.Int i2 -> Some("E-Lt", Judge.Lt(i1, i2, i1 < i2), Value.Bool(i1 < i2))
                | _, _, _ -> None
            if v3 = v3' then
                return (
                    conclude name [
                        derive <| Eval(s1, env, e1, v1, s2);
                        derive <| Eval(s2, env, e2, v2, s3);
                        derive <| j
                    ]
                )
        } |> Option.defaultValue incomplete
    | Eval(s, env, Exp.Var x, v, s') when s = s' ->
        option {
            let! (_, s'', v') = eval [] env (s, Exp.Var x)
            if s'' = s && v' = v then
                return conclude "E-Var" []
        } |> Option.defaultValue incomplete
    | Eval(s1, env, Exp.Let(x, e1, e2), v, s3) ->
        option {
            let fl = diff s1 s3
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let env' = Bind(env, x, v1)
            let! (_, s3', v') = eval fl (Bind(env, x, v1)) (s2, e2)
            if s3' = s3 && v' = v then
                return conclude "E-Let" [
                    derive <| Eval(s1, env, e1, v1, s2);
                    derive <| Eval(s2, env', e2, v, s3);
                ]
        } |> Option.defaultValue incomplete
    | Eval(s, env, Exp.Fun(x, e), Value.Fun(env', x', e'), s') when s = s' && env = env' && x = x' && e = e -> conclude "E-Fun" [] 
    | Eval(s1, env, Exp.LetRec(x, y, e1, e2), v, s2) ->
        conclude "E-LetRec" [
            derive <| Eval(s1, Bind(env, x, Value.FunRec(env, x, y, e1)), e2, v, s2)
        ]
    | Eval(s1, env, Exp.App(e1, e2), v, s4) ->
        option {
            let fl = diff s1 s4
            let! (fl, s2, v1) = eval fl env (s1, e1)
            let! (fl, s3, v2) = eval fl env (s2, e2)
            match v1 with
            | Value.Fun(env2, x, e0) ->
                let env2' = Bind(env2, x, v2)
                let! (_, s4', v') = eval fl env2' (s3, e0)
                if s4 = s4' && v = v' then
                    return conclude "E-App" [
                        derive <| Eval(s1, env, e1, v1, s2);
                        derive <| Eval(s2, env, e2, v2, s3);
                        derive <| Eval(s3, env2', e0, v, s4);
                    ]
            | Value.FunRec(env2, x, y, e0) ->
                let env2' = Bind(Bind(env2, x, v1), y, v2)
                let! (_, s4', v') = eval fl env2' (s3, e0)
                if s4 = s4' && v = v' then
                    return conclude "E-AppRec" [
                        derive <| Eval(s1, env, e1, v1, s2);
                        derive <| Eval(s2, env, e2, v2, s3);
                        derive <| Eval(s3, env2', e0, v, s4);
                    ]
            | _ -> return incomplete
        } |> Option.defaultValue incomplete
    | Eval(s1, env, Exp.Ref e, Loc l, Block(s2, l', v)) when l = l' ->
        option {
            let fl = diff s1 s2
            let! (_, s2', v') = eval fl env (s1, e)
            if s2' = s2 && v' = v then
                return conclude "E-Ref" [derive <| Eval(s1, env, e, v, s2)]
        } |> Option.defaultValue incomplete
    | Eval(s1, env, Exp.Deref e, v, s2) ->
        option {
            let fl = diff s1 s2
            let! (_, _, l) = eval fl env (s1, e)
            let! (_, s2', v') = eval fl env (s1, Exp.Deref e)
            if s2' = s2 && v' = v then
                return conclude "E-Deref" [derive <| Eval(s1, env, e, l, s2)]
            
        } |> Option.defaultValue incomplete
    | Eval(s1, env, Exp.Assign(e1, e2), v, s4) ->
        option {
            let fl = diff s1 s4
            let! (fl, s2, l) = eval fl env (s1, e1)
            let! (fl, s3, v') = eval fl env (s2, e2)
            if v = v' then
                return conclude "E-Assign" [
                    derive <| Eval(s1, env, e1, l, s2);
                    derive <| Eval(s2, env, e2, v, s3);
                ]
        } |> Option.defaultValue incomplete

    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude "B-Plus" []
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude "B-Minus" []
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude "B-Mult" []
    | Lt   (i1, i2, b3) when b3 = (i1 < i2) -> conclude "B-Lt" []
    | _ -> incomplete

"|- let rec do = fun f -> fun i ->
     if i < 1 then 0
     else let x = f i in do f (i - 1) in 
   let x = ref 0 in 
   let sum = fun i -> x := !x + i in
   let y = do sum 3 in !x 
  evalto 6 / @l = 6"
|> parse Parser.judge
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> eprintfn "%A" t; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"
