#r "nuget: ScanRat"
open System
open ScanRat.ScanRat

type Nat = 
    | Z
    | S of Nat
    with
        override this.ToString() =
            match this with
            | Z -> "Z"
            | S(n) -> $"S({n.ToString()})"
        static member ( + ) (lhs: Nat, rhs: Nat) =
            match (lhs, rhs) with
            | (Z, n) -> n
            | (S(n1), n2) -> n1 + S(n2)
        static member ( * ) (lhs: Nat, rhs: Nat) =
            match (lhs, rhs) with
            | (Z, _) -> Z
            | (S(Z), n) -> n
            | (S(n1), n2) -> n1 * n2 + n2
module Nat =
    let rec trySubtract lhs rhs =
        match (lhs, rhs) with
        | (n, Z) -> Some n
        | (Z, S(_)) -> None
        | (S(n1), S(n2)) -> trySubtract n1 n2

type Expr =
    | Term of Nat
    | Add of Expr * Expr
    | Mul of Expr * Expr
    with
        override this.ToString() =
            let rec print = function
                | Term(n) -> n.ToString()
                | Add(e1, e2) -> $"({printAdd e1} + {printAdd e2})"
                | Mul(e1, e2) -> $"({printMul e1} * {printMul e2})"
            and printAdd = function
                | Add(e1, e2) -> $"{printAdd e1} + {printAdd e2}"
                | t -> print t
            and printMul = function
                | Mul(e1, e2) -> $"{printMul e1} * {printMul e2}"
                | t -> print t

            print this

type Judge =
    (* n1 plus n2 is n *)
    | Plus of Nat * Nat * Nat
    (* n1 times n2 is n*)
    | Times of Nat * Nat * Nat
    (* e1 ---> e2*)
    | Reduce of Expr * Expr
    (* e1 -*-> e2 *)
    | MReduce of Expr * Expr
    (* e1 -d-> e2 *)
    | DReduce of Expr * Expr
module Judge =
    let rec print = function
        | Plus(lhs, rhs, res) -> $"{lhs} plus {rhs} is {res}"
        | Times(lhs, rhs, res) -> $"{lhs} times {rhs} is {res}"
        | Reduce(e1, e2) -> $"{e1} ---> {e2}"
        | MReduce(e1, e2) -> $"{e1} -*-> {e2}"
        | DReduce(e1, e2) -> $"{e1} -d-> {e2}"
 
type Rule =
    (* n1 plus n2 is n3 => n1 + n2 ---> n3 *)
    | RPlus of Derivation
    (* n1 times n2 is n3 => n1 * n2 ---> n3 *)
    | RTimes of Derivation
    (* e1 ---> e1' => e1 + e2 ---> e1' + e2 *)
    | RPlusL of Derivation
    (* e2 ---> e2' => e1 + e2 ---> e1 + e2' *)
    | RPlusR of Derivation
    (* e1 ---> e1' => e1 * e2 ---> e1' * e2 *)
    | RTimesL of Derivation
    (* e2 ---> e2' => e1 * e2 ---> e1 * e2' *)
    | RTimesR of Derivation
    (* n1 plus n2 is n3 => n1 + n2 -d-> n3 *)
    | DRPlus of Derivation
    (* n1 times n2 is n3 => n1 * n2 -d-> n3 *)
    | DRTimes of Derivation
    (* e1 -d-> e1' => e1 + e2 -d-> e1' + e2 *)
    | DRPlusL of Derivation
    (* e2 -d-> e2' => n1 + e2 -d-> n1 + e2' *)
    | DRPlusR of Derivation
    (* e1 -d-> e1' => e1 * e2 -d-> e1' * e2 *)
    | DRTimesL of Derivation
    (* e2 -d-> e2' => n1 * e2 -d-> n1 * e2' *)
    | DRTimesR of Derivation
    (* e -*-> e *)
    | MRZero
    (* e -*-> e' /\ e' -*-> e'' => e -*-> e'' *)
    | MRMulti of Derivation * Derivation
    (* e ---> e' => e -*-> e' *)
    | MROne of Derivation
    (* Z plus n is n *)
    | PZero
    (* n1 plus n2 is n => S(n1) plus n2 is S(n) *)
    | PSucc of Derivation
    (* Z times n is Z *)
    | TZero
    (* n1 times n2 is n3 /\ n2 plus n3 is n4 => S(n1) times n2 is n4 *)
    | TSucc of Derivation * Derivation
and Derivation = Judge * Rule

let mapRule = function
    | RPlus plus -> "R-Plus", [plus]
    | RTimes times -> "R-Times", [times]
    | RPlusL d -> "R-PlusL", [d]
    | RPlusR d -> "R-PlusR", [d]
    | RTimesL d -> "R-TimesL", [d]
    | RTimesR d -> "R-TimesR", [d]
    | DRPlus plus -> "DR-Plus", [plus]
    | DRTimes times -> "DR-Times", [times]
    | DRPlusL d -> "DR-PlusL", [d]
    | DRPlusR d -> "DR-PlusR", [d]
    | DRTimesL d -> "DR-TimesL", [d]
    | DRTimesR d -> "DR-TimesR", [d]
    | MRZero -> "MR-Zero", []
    | MRMulti(d1, d2) -> "MR-Multi", [d1; d2] 
    | MROne d -> "MR-One", [d]
    | PZero -> "P-Zero", []
    | PSucc plus -> "P-Succ", [plus]
    | TZero -> "T-Zero", []
    | TSucc(times, plus) -> "T-Succ", [times; plus]

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
    | Term(n) -> n
    | Add(l, r) -> (eval l) + (eval r)
    | Mul(l, r) -> (eval l) * (eval r)

let mapPair f (a, b) = (f a, f b)

let rec normalizeParens expr =
    let rec collectAdd = function
        | Add(e1, e2) -> (collectAdd e1) @ (collectAdd e2)
        | e -> [e]
    let rec collectMul = function
        | Mul(e1, e2) -> (collectMul e1) @ (collectMul e2)
        | e -> [e]
    match expr with
    | (Term(_) as t) -> t
    | (Add _ as a) -> collectAdd a |> List.reduce (fun e1 e2 -> Add(e1, e2))
    | (Mul _ as m) -> collectMul m |> List.reduce (fun e1 e2 -> Mul(e1, e2))

let rec derive judge =
    let conclude (by: Rule) = Some (judge, by)
    match judge with
    | Plus(Z, n1, n2) when n1 = n2 -> 
        conclude PZero
    | Plus(S(n1), n2, S(n)) ->
        Plus(n1, n2, n)
        |> derive
        |> Option.bind (PSucc >> conclude)
    | Times(Z, _, Z) -> conclude TZero
    | Times(S(n1), n2, n4) ->
        match (Nat.trySubtract n4 n2) with
        | None -> None
        | Some n3 ->
            let times = derive <| Times(n1, n2, n3)
            let plus = derive <| Plus(n2, n3, n4)
            Option.map2 (fun t p -> (TSucc(t, p) |> conclude)) times plus
            |> Option.flatten
    | Reduce(Add(Term(n1), Term(n2)), Term(n3)) -> Plus(n1, n2, n3) |> derive |> Option.bind(RPlus >> conclude)
    | Reduce(Mul(Term(n1), Term(n2)), Term(n3)) -> Times(n1, n2, n3) |> derive |> Option.bind(RTimes >> conclude)
    | Reduce(Add(e1, e2), Add(e1', e2')) ->
        match (e1=e1', e2=e2') with
        | (false, true) -> Some(Reduce(e1, e1'), RPlusL)
        | (true, false) -> Some(Reduce(e2, e2'), RPlusR)
        | _ -> None
        |> Option.bind (
            fun (j, r) -> j |> derive |> Option.bind(r >> conclude)
        )
    | Reduce(Mul(e1, e2), Mul(e1', e2')) ->
        match (e1=e1', e2=e2') with
        | (false, true) -> Some(Reduce(e1, e1'), RTimesL)
        | (true, false) -> Some(Reduce(e2, e2'), RTimesR)
        | _ -> None
        |> Option.bind(
            fun (j, r) -> j |> derive |> Option.bind(r >> conclude)
        )
    | DReduce(Add(Term(n1), Term(n2)), Term(n3)) -> Plus(n1, n2, n3) |> derive |> Option.bind(DRPlus >> conclude)
    | DReduce(Mul(Term(n1), Term(n2)), Term(n3)) -> Times(n1, n2, n3) |> derive |> Option.bind(DRTimes >> conclude)
    | DReduce(Add(e1, e2), Add(e1', e2')) when e2=e2' -> DReduce(e1, e1') |> derive |> Option.bind(DRPlusL >> conclude)
    | DReduce(Add(Term(n1), e2), Add(Term(n1'), e2')) when n1 = n1' -> DReduce(e2, e2') |> derive |> Option.bind(DRPlusR >> conclude)
    | DReduce(Mul(e1, e2), Mul(e1', e2')) when e2=e2' -> DReduce(e1, e1') |> derive |> Option.bind(DRTimesL >> conclude)
    | DReduce(Mul(Term(n1), e2), Mul(Term(n1'), e2')) when n1 = n1' -> DReduce(e2, e2') |> derive |> Option.bind(DRTimesR >> conclude)
    
    | MReduce(expr, expr') ->
        let one (e1, e2) =
            let es = (e1 |> normalizeParens, e2 |> normalizeParens)
            Reduce es |> derive |> Option.map(fun d -> (MReduce es, MROne(d)))
        let list = decompose (expr, expr')
        printfn "%A" list
        match list with
        | Some [] -> conclude MRZero
        | Some [j] -> one j
        | Some (h::js) ->
            List.fold (
                fun st' ((_, e'') as j) ->
                    let d' = one j
                    Option.map2 (
                        fun st d -> (MReduce(expr, e''), MRMulti(st, d))
                    ) st' d'
            ) (one h) js
        | None -> None
    | _ ->
        printfn "%A" judge
        None
(* 簡約を分解して一回の簡約で表現できるものにする *)
and decompose (expr, expr') =
    let binDerive f e1 e2 e1' e2' =
        (* e1 -*-> e1' => e1 @ e2 -*-> e1' @ e2 *)
        let l1 = decompose (e1, e1') |> Option.map(List.map(mapPair(fun e -> f(e, e2))))
        (* e2 -*-> e2' => e1' @ e2 -*-> e1' @ e2' *)
        let l2 = decompose (e2, e2') |> Option.map(List.map(mapPair(fun e -> f(e1', e))))
        Option.map2 (@) l1 l2

    let evalDerive f e1 e2 e' =
        let (e1', e2') = (e1, e2) |> mapPair (eval >> Term)
        (* e1 -*-> e1' /\ e2- -*-> e2' => e1 @ e2 -*-> e1' @ e2' *)
        let l1 = binDerive f e1 e2 e1' e2'
        (* e1' +/* e2' -*-> e' by MR-One *)
        let l2 = Some [(f(e1', e2'), e')]
        Option.map2 (@) l1 l2

    match (expr, expr') with
    (* e -*-> e' <=> e evalto e' *)
    | (e, e') when eval e <> eval e' -> None
    (* 等価 *)
    | (e, e') when e=e' -> Some []
    (* 評価 *)
    | (Add(e1, e2), (Term _ as e')) -> evalDerive Add e1 e2 e'
    | (Mul(e1, e2), (Term _ as e')) -> evalDerive Mul e1 e2 e'
    (* 部分評価*)
    | (Add(e1, e2), Add(e1', e2')) -> binDerive Add e1 e2 e1' e2'
    | (Mul(e1, e2), Mul(e1', e2')) -> binDerive Mul e1 e2 e1' e2'
    | (e, e') ->
        printfn $"Cannot decompose MR: {e} -*-> {e'}"
        None
    
module Parser =
    let nat = production "nat"
    nat.rule
        <- ~~"Z" --> fun _ -> Z
        |- ~~"S(" +. nat .+ ~~")" --> S
    let term = production "term"
    let primary = production "primary"
    primary.rule
        <- primary .+ ~~" * " + term --> Mul
        |- term
    let expr = production "expr"
    expr.rule
        <- expr .+ ~~" + " + primary --> Add
        |- primary
    term.rule
        <- nat --> Term
        |- ~~"(" +. expr .+ ~~")"
    let input =
        expr .+ ~~" ---> " + expr --> Reduce
        |- expr .+ ~~" -*-> " + expr --> MReduce
        |- expr .+ ~~" -d-> " + expr --> DReduce 

"S(Z) * S(Z) + S(Z) * S(Z) -*-> S(S(Z))"
|> parse Parser.input
|> function
    | Success s -> s.Value
    | Failure e -> failwith (sprintf "%A" e)
|> fun t -> printfn "%A" t; t
|> derive
|> function
    | Some d -> d
    | None -> failwith "cannot derive"
|> printDerivation Judge.print mapRule
|> printfn "%s"
