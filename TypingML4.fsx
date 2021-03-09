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

type 't TypeS =
    | Term of 't
    | Fun of 't TypeS * 't TypeS
    | List of 't TypeS
    with
        override this.ToString() =
            let rec print = function
                | Term t -> $"{t}"
                | Fun _ as t -> printFun t
                | List (Term t) -> $"{t} list"
                | List t -> $"({t}) list"
            and printFun = function
                | Fun((Fun _ as t1), t2) -> "(" + printFun t1 + ") -> " + printFun t2
                | Fun(t1, t2) -> printFun t1 + " -> " + printFun t2
                | t -> print t
            print this
module TypeS =
    let rec convert convertT t =
        let conv = convert convertT
        match t with
        | Term t -> Term (convertT t)
        | Fun(t1, t2) -> Fun(conv t1, conv t2)
        | List t -> List (conv t)

type TypeTerm = Int | Bool
    with
        override this.ToString() =
            match this with
            | Int -> "int"
            | Bool -> "bool"
type Type = TypeTerm TypeS

type 't EnvS =
    | Empty
    | Bind of 't EnvS * Var * 't
    with
        override this.ToString() =
            match this with
            | Empty -> ""
            | Bind(Empty, x, t) -> $"{x}: {t}"
            | Bind(env, x, t) -> $"{env}, {x}: {t}"
module EnvS =
    let rec convert convertT = function
        | Empty -> Empty
        | Bind(env, x, t) -> Bind(convert convertT env, x, convertT t)

type Env = Type EnvS

type Prim = Plus | Minus | Times | Lt
    with
        override this.ToString() =
            match this with
            | Plus -> "+"
            | Minus -> "-"
            | Times -> "*"
            | Lt -> "<"

(* 式の「構造」 *)
type ExpS<'v, 't> =
    | Term of 't
    (* e1 op e2 *)
    | BinOp of ExpS<'v, 't> * Prim * ExpS<'v, 't>
    (* if e1 then e2 else e3 *)
    | If of ExpS<'v, 't> * ExpS<'v, 't> * ExpS<'v, 't>
    (* let x = e1 in e2 *)
    | Let of 'v * ExpS<'v, 't> * ExpS<'v, 't>
    (* fun x -> e *)
    | Fun of 'v * ExpS<'v, 't>
    (* e1 e2 *)
    | App of ExpS<'v, 't> * ExpS<'v, 't>
    (* let rec x = fun y -> e1 in e2 *)
    | LetRec of 'v * 'v * ExpS<'v, 't> * ExpS<'v, 't>
    (* e1::e2 *)
    | Cons of ExpS<'v, 't> * ExpS<'v, 't>
    (* match e1 with [] -> e2 | x::y -> e3 *)
    | Match of ExpS<'v, 't> * ExpS<'v, 't> * 'v * 'v * ExpS<'v, 't>
    with
        override this.ToString() =
            let rec print = function
                | Term et -> $"{et}"
                | BinOp(_, op, _) as e -> "(" + printBinop op e + ")"
                | If(e1, e2, e3) -> $"if {e1} then {e2} else {e3}"
                | Let(x, e1, e2) -> $"let {x} = {e1} in {e2}"
                | Fun(x, e) -> $"(fun {x} -> {e})"
                | App _ as e -> "(" + printApp e + ")"
                | LetRec(x, y, e1, e2) -> $"let rec {x} = fun {y} -> {e1} in {e2}"
                | Cons _ as e -> "(" + printCons e + ")"
                | Match(e1, e2, x, y, e3) -> $"match {e1} with [] -> {e2} | {x}::{y} -> {e3}"
            and printBinop op = function
                | BinOp(e1, op', e2) when op = op' -> printBinop op e1 + $" {op} " + printBinop op e2
                | e -> print e
            and printApp = function
                | App(e1, (App _ as e2)) -> printApp e1 + " (" + printApp e2 + ")"
                | App(e1, e2) -> printApp e1 + " " + printApp e2
                | e -> print e
            and printCons = function
                | Cons((Cons _ as e1), e2) -> "(" + printCons e1 + ")::" + printCons e2
                | Cons(e1, e2) -> printCons e1 + "::" + printCons e2
                | e -> print e
            print this
module ExpS =
    let rec convert convertV convertT exp =
        let conv = convert convertV convertT
        match exp with
        | Term t -> Term (convertT t)
        | BinOp(e1, op, e2) -> BinOp(conv e1, op, conv e2)
        | If(e1, e2, e3) -> If(conv e1, conv e2, conv e3)
        | Let(x, e1, e2) -> Let(convertV x, conv e1, conv e2)
        | Fun(x, e) -> Fun(convertV x, conv e)
        | App(e1, e2) -> App(conv e1, conv e2)
        | LetRec(x, y, e1, e2) -> LetRec(convertV x, convertV y, conv e1, conv e2)
        | Cons(e1, e2) -> Cons(conv e1, conv e2)
        | Match(e1, e2, x, y, e3) -> Match(conv e1, conv e2, convertV x, convertV y, conv e3)

(* 式の「末端」*)
type ExpTerm =
    | Int of int
    | Bool of bool
    | Var of Var
    | Nil
    with
        override this.ToString() =
            match this with
            | Int i when i < 0 -> $"({i})"
            | Int i -> $"{i}"
            | Bool true -> "true"
            | Bool false -> "false"
            | Var x -> x
            | Nil -> "[]"

(* 式 = 構造 + 引数 + 末端 *)
type Exp = ExpS<Var, ExpTerm>

type Judge = Type of Env * Exp * Type // env |- e: t
    with
        override this.ToString() =
            match this with
            | Type(env, e, t) ->
                let env =
                    match env with
                    | Empty -> ""
                    | Bind _ -> $"{env} "
                $"{env}|- {e}: {t}"
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
    let keywords = [| "if"; "then"; "else"; "let"; "in"; "fun"; "rec"; "match"; "with"; "int"; "bool"; "list" |]

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

    let ptype = production "type"
    let tterm = production "tterm"
    tterm.rule
        <- tterm .+ sp1 .+ ~~"list" --> Type.List
        |- ~~"(" +. sp +. ptype .+ sp .+ ~~")"
        |- ~~"int" --> fun _ -> TypeTerm.Int |> Type.Term
        |- ~~"bool" --> fun _ -> TypeTerm.Bool |> Type.Term
    ptype.rule
        <- tterm .+ sp .+ ~~"->" .+ sp + ptype --> Type.Fun
        |- tterm
    
    let env = production "env"
    let bind = ident .+ sp .+ ~~":" .+ sp + ptype
    env.rule
        <- env .+ sp .+ ~~"," .+ sp + bind --> fun (env, (x, t)) -> Env.Bind(env, x, t)
        |- bind --> fun (x, t) -> Env.Bind(Empty, x, t)
        |- ~~"" --> fun _ -> Env.Empty

    let exp = production "exp"
    let term =
        ~~"(" +. sp +. exp .+ sp .+ ~~")"
        |- digits --> (ExpTerm.Int >> ExpS.Term)
        |- bool --> (ExpTerm.Bool >> ExpS.Term)
        |- ident --> (ExpTerm.Var >> ExpS.Term)
        |- ~~"[" + sp + ~~"]" --> fun _ -> ExpTerm.Nil |> ExpS.Term
        |- ~~"if" +. sp1 +. exp .+ sp1 .+ ~~"then" .+ sp1 + exp .+ sp1 .+ ~~"else" .+ sp1 + exp
            --> fun ((e1, e2), e3) -> Exp.If(e1, e2, e3)
        |- ~~"let" +. sp1 +. ~~"rec" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 + ident .+ sp .+ ~~"->" .+ sp + exp .+ sp1 .+ ~~"in" .+ sp1 + exp
            --> fun (((x, y), e1), e2) -> Exp.LetRec(x, y, e1, e2)
        |- ~~"let" +. sp1 +. ident .+ sp .+ ~~"=" .+ sp + exp .+ sp1 .+ ~~"in" .+ sp1 + exp
            --> fun ((x, e1), e2) -> Exp.Let(x, e1, e2)
        |- ~~"fun" +. sp1 +. ident .+ sp .+ ~~"->" .+ sp + exp --> Exp.Fun
        |- 
            ~~"match" +. sp1 +. exp .+ sp1 .+ ~~"with" .+ sp1
            .+ ~~"[" .+ sp .+ ~~"]" .+ sp .+ ~~"->" .+ sp + exp
            .+ sp .+ ~~"|" .+ sp + ident .+ sp .+ ~~"::" .+ sp + ident .+ sp .+ ~~"->" .+ sp + exp
            --> fun ((((e1, e2), x), y), e3) -> Exp.Match(e1, e2, x, y, e3)
    let app = production "app"
    app.rule
        <- app .+ sp1 + term --> Exp.App
        |- term
    let times = production "times"
    times.rule
        <- times .+ sp .+ ~~"*" .+ sp + app --> fun (e1, e2) -> Exp.BinOp(e1, Times, e2)
        |- app
    let plus = production "plus"
    plus.rule
        <- plus .+ sp + ((~~"+" --> fun _ -> Plus) |- (~~"-" --> fun _ -> Minus)) .+ sp + times
            --> fun ((e1, op), e2) -> BinOp(e1, op, e2)
        |- times
    let lessThan = production "lessThan"
    lessThan.rule
        <- lessThan .+ sp .+ ~~"<" .+ sp + plus --> fun (e1, e2) -> BinOp(e1, Lt, e2)
        |- plus
    exp.rule
        <- lessThan .+ sp .+ ~~"::" .+ sp + exp --> fun (e1, e2) -> Cons(e1, e2)
        |- lessThan
    
    let judge =
        env .+ sp .+ ~~"|-" .+ sp + exp .+ sp1 .+ ~~":" .+ sp1 + ptype --> fun ((env, e), t) -> Judge.Type(env, e, t)

type 't TypedExpTerm = TypedExpTerm of ExpTerm * 't
    with
        override this.ToString() =
            match this with
            | TypedExpTerm(e, t) -> $"({e}: {t})"

type 't TypedVar = TypedVar of Var * 't
    with
        override this.ToString() =
            match this with
            | TypedVar(x, t) -> $"({x}: {t})"
type TypedExp = ExpS<TypedVar<Type>, TypedExpTerm<Type>>
let untyped e = ExpS.convert (fun (TypedVar(x, _)) -> x) (fun (TypedExpTerm(et, _)) -> et) e

(* Wrong Type *)
type WTypeTerm =
    | Unknown
    | Int
    | Bool
    | Var of int * (WTypeTerm TypeS) ref
    with
        override this.ToString() =
            match this with
            | Unknown -> "?"
            | Int -> "int"
            | Bool -> "bool"
            | Var(i, a) -> $"t{i}[{a.Value}]"
type WType = WTypeTerm TypeS
type WTExp = ExpS<TypedVar<WType>, TypedExpTerm<WType>>
type WEnv = WType EnvS
let wrongType t = TypeS.convert (fun tt -> match tt with TypeTerm.Int -> Int | TypeTerm.Bool -> Bool) t

let infer partial unknown env exp =
    let extract env e =
        let newVar =
            let ctr = ref (-1)
            fun () -> ctr.Value <- !ctr + 1; TypeS.Term(WTypeTerm.Var(!ctr, ref (TypeS.Term Unknown)))
        
        let rec extract' wenv e =
            let eq, t, wte =
                match wenv, e with
                | _, Exp.Term(ExpTerm.Int _ as tm) ->
                    let t = WType.Term(WTypeTerm.Int)
                    Set.empty, t, (WTExp.Term(TypedExpTerm(tm, t)))
                | _, Exp.Term(ExpTerm.Bool _ as tm) ->
                    let t = WType.Term(WTypeTerm.Bool)
                    Set.empty, t, (WTExp.Term(TypedExpTerm(tm, t)))
                | env, Exp.Term(ExpTerm.Var x as tm) ->
                    let rec find = function
                        | Bind(_, x', t) when x = x' -> t
                        | Bind(env, _, _) -> find env
                        | Empty -> WType.Term Unknown
                    let t = find env
                    Set.empty, t, (WTExp.Term(TypedExpTerm(tm, t)))
                | env, Exp.BinOp(e1, op, e2) ->
                    let eq1, t1, wte1 = extract' env e1
                    let eq2, t2, wte2 = extract' env e2
                    let eq3 =
                        Set.union eq1 eq2
                        |> Set.add (t1, TypeS.Term(Int))
                        |> Set.add (t2, TypeS.Term(Int))
                    let t3 =
                        match op with
                        | Plus | Minus | Times -> TypeS.Term(Int)
                        | Lt -> TypeS.Term(Bool)
                    eq3, t3, BinOp(wte1, op, wte2)
                | env, Exp.If(e1, e2, e3) ->
                    let eq1, t1, wte1 = extract' env e1
                    let eq2, t2, wte2 = extract' env e2
                    let eq3, t3, wte3 = extract' env e3
                    let eq4 =
                        Set.union (Set.union eq1 eq2) eq3
                        |> Set.add (t1, TypeS.Term Bool)
                        |> Set.add (t2, t3)
                    eq4, t2, If(wte1, wte2, wte3)
                | env, Exp.Let(x, e1, e2) ->
                    let eq1, t1, wte1 = extract' env e1
                    let eq2, t2, wte2 = extract' (Bind(env, x, t1)) e2
                    let eq3 = Set.union eq1 eq2
                    eq3, t2, Let(TypedVar(x, t1), wte1, wte2)
                | env, Exp.Fun(x, e) ->
                    let a = newVar ()
                    let eq, t, wte = extract' (Bind(env, x, a)) e
                    eq, TypeS.Fun(a, t), ExpS.Fun(TypedVar(x, a), wte)
                | env, Exp.App(e1, e2) ->
                    let eq1, t1, wte1 = extract' env e1
                    let eq2, t2, wte2 = extract' env e2
                    let a = newVar ()
                    let eq3 = Set.union eq1 eq2 |> Set.add (t1, TypeS.Fun(t2, a))
                    eq3, a, ExpS.App(wte1, wte2)
                | env, Exp.LetRec(x, y, e1, e2) ->
                    let a1, a2 = newVar (), newVar ()
                    let eq1, t1, wte1 = extract' (Bind(Bind(env, x, a1), y, a2)) e1
                    let eq2, t2, wte2 = extract' (Bind(env, x, a1)) e2
                    let eq3 = Set.union eq1 eq2 |> Set.add (a1, TypeS.Fun(a2, t1))
                    eq3, t2, ExpS.LetRec(TypedVar(x, a1), TypedVar(y, a2), wte1, wte2)
                | _, Exp.Term(ExpTerm.Nil as tm) ->
                    let a = newVar ()
                    Set.empty, TypeS.List a, ExpS.Term(TypedExpTerm(tm, TypeS.List a))
                | env, Exp.Cons(e1, e2) ->
                    let eq1, t1, wte1 = extract' env e1
                    let eq2, t2, wte2 = extract' env e2
                    let eq3 = Set.union eq1 eq2 |> Set.add (t2, TypeS.List t1)
                    eq3, t2, ExpS.Cons(wte1, wte2)
                | env, Exp.Match(e1, e2, x, y, e3) ->
                    let a = newVar ()
                    let eq1, t1, wte1 = extract' env e1
                    let eq2, t2, wte2 = extract' env e2
                    let eq3, t3, wte3 = extract' (Bind(Bind(env, x, a), y, List a)) e3
                    let eq4 =
                        Set.union (Set.union eq1 eq2) eq3
                        |> Set.add (t1, List a)
                        |> Set.add (t2, t3)
                    eq4, t2, ExpS.Match(wte1, wte2, TypedVar(x, a), TypedVar(y, List a), wte3)
            match (partial |> Map.tryFind (env, e)) with
            | Some t' ->
                (eq |> Set.add (t, wrongType t')), t, wte
            | None -> eq, t, wte
        
        let wenv = EnvS.convert wrongType env
        let eq, _, wte = extract' wenv e
        eq, wte
    
    let unify eq =
        let rec unify' eq =
            match eq with
            | [] -> ()
            | (t, t')::eq when t = t' -> unify' eq
            | ((WType.Term(Var(_, a)) as va), (WType.Term(Var(_, b)) as vb))::eq ->
                match a.Value, b.Value with
                | WType.Term Unknown, WType.Term Unknown ->
                    // なにもわからないので後回し
                    unify' eq
                    unify' [(va, vb)]
                | (t, WType.Term(Unknown)) -> unify' ((t, vb)::eq)
                | (WType.Term(Unknown), t) -> unify' ((va, t)::eq)
                | (t1, t2) -> unify' ((t1, t2)::eq)
            | ((t, WType.Term(Var(_, a))) | (WType.Term(Var(_, a)), t))::eq ->
                match a.Value with
                | WType.Term Unknown ->
                    a.Value <- t
                    unify' eq
                | t' -> unify' ((t, t')::eq)
            | (WType.Fun(t11, t12), WType.Fun(t21, t22))::eq -> unify' ((t11, t21)::(t12, t22)::eq)
            | (WType.List t1, WType.List t2)::eq -> unify' ((t1, t2)::eq)
            | (t, t')::_ -> failwith $"invalid eq: {t} = {t'}"
        unify' (eq |> Set.toList)

    let rec fixTT = function
        | WTypeTerm.Unknown -> unknown
        | WTypeTerm.Int -> Some(TypeTerm.Int |> Type.Term)
        | WTypeTerm.Bool -> Some(TypeTerm.Bool |> Type.Term)
        | WTypeTerm.Var(_, a) -> fixT a.Value
    and fixT wt =
        match wt with
        | WType.Term wtt -> fixTT wtt
        | WType.Fun(wt1, wt2) -> Option.map2 (fun t1 t2 -> Type.Fun(t1, t2)) (fixT wt1) (fixT wt2)
        | WType.List t -> Option.map (Type.List) (fixT t)
    let fixV = function
        | TypedVar(x, wt) -> Option.map (fun t -> TypedVar(x, t)) (fixT wt)
    let fixET = function
        | TypedExpTerm(et, wt) -> Option.map (fun t -> TypedExpTerm(et, t)) (fixT wt)
    let rec fixE wte =
        match wte with
        | ExpS.Term wtet -> Option.map (ExpS.Term) (fixET wtet)
        | ExpS.BinOp(wte1, op, wte2) -> Option.map2 (fun te1 te2 -> BinOp(te1, op, te2)) (fixE wte1) (fixE wte2)
        | ExpS.If(wte1, wte2, wte3) -> Option.map3 (fun te1 te2 te3 -> If(te1, te2, te3)) (fixE wte1) (fixE wte2) (fixE wte3)
        | ExpS.Let(wtv, wte1, wte2) -> Option.map3 (fun tv te1 te2 -> Let(tv, te1, te2)) (fixV wtv) (fixE wte1) (fixE wte2)
        | ExpS.Fun(wtv, wte) -> Option.map2 (fun tv te -> Fun(tv, te)) (fixV wtv) (fixE wte)
        | ExpS.App(wte1, wte2) -> Option.map2 (fun te1 te2 -> App(te1, te2)) (fixE wte1) (fixE wte2)
        | ExpS.LetRec(wtv1, wtv2, wte1, wte2) ->
            Option.map2 (fun (tv1, tv2) (te1, te2) -> LetRec(tv1, tv2, te1, te2))
                (Option.map2 (fun a b -> a,b) (fixV wtv1) (fixV wtv2))
                (Option.map2 (fun a b -> a,b) (fixE wte1) (fixE wte2))
        | ExpS.Cons(wte1, wte2) -> Option.map2 (fun te1 te2 -> Cons(te1, te2)) (fixE wte1) (fixE wte2)
        | ExpS.Match(wte1, wte2, wtv1, wtv2, wte3) ->
            Option.map3 (fun te1 te2 (tv1, tv2, te3) -> Match(te1, te2, tv1, tv2, te3))
                (fixE wte1)
                (fixE wte2)
                (Option.map3 (fun a b c -> a,b,c) (fixV wtv1) (fixV wtv2) (fixE wte3))

    let eq, wte = extract env exp
    eprintfn $"before: {wte}"
    unify eq
    eprintfn $"after: {wte}"
    fixE wte

let rec derive judge =
    let rec deriveT env te =
        let conclude t name derivs = t, Derivation(Type(env, untyped te, t), name, derivs)
        let incomplete t = t, Incomplete(Type(env, untyped te, t))

        match env, te with
        | _, ExpS.Term(TypedExpTerm(ExpTerm.Int _, (TypeS.Term TypeTerm.Int as t))) ->
            Some(conclude t "T-Int" [])
        | _, ExpS.Term(TypedExpTerm(ExpTerm.Bool _, (TypeS.Term TypeTerm.Bool as t))) ->
            Some(conclude t "T-Bool" [])
        | env, ExpS.If(te1, te2, te3) ->
            option {
                let! t1, d1 = deriveT env te1
                let! t2, d2 = deriveT env te2
                let! t3, d3 = deriveT env te3
                match t1, t2, t3 with
                | TypeS.Term TypeTerm.Bool, t, t' when t = t' -> return conclude t "T-If" [d1; d2; d3]
                | _, _, _ -> return incomplete t2
            }
        | env, ExpS.BinOp(te1, op, te2) ->
            option {
                let! t1, d1 = deriveT env te1
                let! t2, d2 = deriveT env te2
                let ds = [d1; d2]
                let name, t =
                    match op with
                    | Plus  -> "T-Plus" , Type.Term TypeTerm.Int
                    | Minus -> "T-Minus", Type.Term TypeTerm.Int
                    | Times -> "T-Times", Type.Term TypeTerm.Int
                    | Lt    -> "T-Lt"   , Type.Term TypeTerm.Bool
                match t1, t2 with
                | Type.Term TypeTerm.Int, Type.Term TypeTerm.Int -> return conclude t name ds
                | _, _ -> return incomplete t
            }
        | env, ExpS.Term(TypedExpTerm(ExpTerm.Var x, t)) ->
            let rec find = function
                | Bind(_, x', t') when x = x' -> Some t'
                | Bind(env, _, _) -> find env
                | Empty -> None
            option {
                let! t' = find env
                if t = t' then
                    return conclude t "T-Var" []
                else
                    return incomplete t
            }
        | env, ExpS.Let(TypedVar(x, t1), te1, te2) ->
            option {
                let! t1', d1 = deriveT env te1
                if t1 <> t1' then return! None
                else
                    let! t2, d2 = deriveT (Bind(env, x, t1)) te2
                    return conclude t2 "T-Let" [d1; d2]
            }
        | env, ExpS.Fun(TypedVar(x, t1), te) ->
            option {
                let! t2, d = deriveT (Bind(env, x, t1)) te
                return conclude (TypeS.Fun(t1, t2)) "T-Fun" [d]
            }
        | env, ExpS.App(te1, te2) ->
            option {
                let! t12, d1 = deriveT env te1
                let! t1, d2 = deriveT env te2
                match t12 with
                | TypeS.Fun(t1', t2) when t1 = t1' -> return conclude t2 "T-App" [d1; d2]
                | _ -> return! None
            }
        | env, ExpS.LetRec(TypedVar(x, TypeS.Fun(t1, t2)), TypedVar(y, t1'), te1, te2) when t1 = t1' ->
            option {
                let! t2', d1 = deriveT (Bind(Bind(env, x, TypeS.Fun(t1, t2)), y, t1)) te1
                let! t, d2 = deriveT (Bind(env, x, TypeS.Fun(t1, t2))) te2
                if t2 = t2' then
                    return conclude t "T-LetRec" [d1;d2]
                else
                    return incomplete t
            }
        | _, ExpS.Term(TypedExpTerm(ExpTerm.Nil, TypeS.List t)) ->
            Some(conclude (List t) "T-Nil" [])
        | env, ExpS.Cons(te1, te2) ->
            option {
                let! t, d1 = deriveT env te1
                let! tl, d2 = deriveT env te2
                match tl with
                | List t' when t = t' -> return conclude (List t) "T-Cons" [d1;d2]
                | _ -> return incomplete (List t)
            }
        | env, ExpS.Match(te1, te2, TypedVar(x, t1), TypedVar(y, List t1'), te3) when t1 = t1' -> 
            option {
                let! t1', d1 = deriveT env te1
                let! t, d2 = deriveT env te2
                let! t', d3 = deriveT (Bind(Bind(env, x, t1), y, List t1)) te3
                if t1' = List t1 && t = t' then
                    return conclude t "T-Match" [d1; d2; d3]
                else
                    return incomplete t
            }
        | _, _ -> None

    match judge with
    | Type(env, e, t) ->
        let partial = Map.ofList [((env, e), t)]
        let unknown = TypeS.Term TypeTerm.Int
        option {
            let! te = infer partial (Some unknown) env e
            eprintfn $"{te}"
            let! t', d = deriveT env te
            if t = t' then
                return d
        } |> Option.defaultValue (Incomplete judge)

"|- let max = fun x -> fun y -> if x < y then y else x in max 3 5 : int"
|> parse Parser.judge
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> eprintfn $"{t}"; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"