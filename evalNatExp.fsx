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
            match this with
            | Term(n) -> n.ToString()
            | Add(lhs, rhs) -> "(" + lhs.ToString() + " + " + rhs.ToString() + ")"
            | Mul(lhs, rhs) -> "(" + lhs.ToString() + " * " + rhs.ToString() + ")"

type Judge =
    (* n1 plus n2 is n *)
    | Plus of Nat * Nat * Nat
    (* n1 times n2 is n*)
    | Times of Nat * Nat * Nat
    (* e evalto n*)
    | Eval of Expr * Nat
module Judge =
    let rec print = function
        | Plus(lhs, rhs, res) -> $"{lhs} plus {rhs} is {res}"
        | Times(lhs, rhs, res) -> $"{lhs} times {rhs} is {res}"
        | Eval(e, n) -> $"{e} evalto {n}"
 
type Rule =
    (* n evalto n *)
    | EConst
    (* e1 evalto n1 /\ e2 evalto n2 /\ n1 plus n2 is n -> e1 + e2 evalto n *)
    | EPlus of Derivation * Derivation * Derivation
    (* e1 evalto n1 /\ e2 evalto n2 /\ n1 times n2 is n -> e1 * e2 evalto n *)
    | ETimes of Derivation * Derivation * Derivation
    (* Z plus n is n *)
    | PZero
    (* n1 plus n2 is n -> S(n1) plus n2 is S(n) *)
    | PSucc of Derivation
    (* Z times n is Z *)
    | TZero
    (* n1 times n2 is n3 /\ n2 plus n3 is n4 -> S(n1) times n2 is n4 *)
    | TSucc of Derivation * Derivation
and Derivation = Judge * Rule

let mapRule = function
    | EConst -> "E-Const", []
    | EPlus(en1, en2, plus) -> "E-Plus", [en1; en2; plus]
    | ETimes(en1, en2, times) -> "E-Times", [en1; en2; times]
    | PZero -> "P-Zero", []
    | PSucc(plus) -> "P-Succ", [plus]
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

let rec derive judge =
    let conclude by = (judge, by)
    match judge with
    | Plus(Z, n1, n2) when n1 = n2 -> conclude PZero
    | Plus(S(n1), n2, S(n)) -> conclude <| PSucc(derive <| Plus(n1, n2, n))
    | Times(Z, _, Z) -> conclude TZero
    | Times(S(n1), n2, n4) ->
        match (Nat.trySubtract n4 n2) with
        | None -> failwith "cannot derive(T-Succ)"
        | Some n3 ->
            conclude <| TSucc(
                derive <| Times(n1, n2, n3),
                derive <| Plus(n2, n3, n4)
            )
    | Eval(Term(n1), n2) when n1 = n2 -> conclude EConst
    | Eval(Add(e1, e2), n) ->
        let n1 = eval e1
        let n2 = eval e2
        conclude <| EPlus(
            derive <| Eval(e1, n1),
            derive <| Eval(e2, n2),
            derive <| Plus(n1, n2, n)
        )
    | Eval(Mul(e1, e2), n) ->
        let n1 = eval e1
        let n2 = eval e2
        conclude <| ETimes(
            derive <| Eval(e1, n1),
            derive <| Eval(e2, n2),
            derive <| Times(n1, n2, n)
        )
    | _ -> failwith "cannot derive"

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
    let eval = expr .+ ~~" evalto " + nat --> Eval

"Z * (S(S(Z)) + S(S(Z))) evalto Z"
|> parse Parser.eval
|> function
    | Success s -> s.Value
    | Failure e -> failwith (sprintf "%A" e)
|> derive
|> printDerivation Judge.print mapRule
|> printfn "%s"
