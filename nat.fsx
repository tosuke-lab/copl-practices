open System

type Nat = 
    | Z
    | S of Nat
    with
        override this.ToString() =
            match this with
            | Z -> "Z"
            | S(n) -> $"S({n.ToString()})"
        static member op_LessThan (lhs: Nat, rhs: Nat) =
            match (lhs, rhs) with
            | (Z, Z) -> false
            | (S(_), Z) -> false
            | (Z, S(_)) -> true
            | (S(n1), S(n2)) -> n1 < n2
        static member (+) (lhs: Nat, rhs: Nat) =
            match (lhs, rhs) with
            | (Z, n) -> n
            | (S(n1), n2) -> n1 + S(n2)
module Nat =
    let rec init = function
        | 0u -> Z
        | n -> S(init (n-1u))
    let rec trySubtract lhs rhs =
        match (lhs, rhs) with
        | (n, Z) -> Some n
        | (Z, S(_)) -> None
        | (S(n1), S(n2)) -> trySubtract n1 n2 

type Judge =
    (* lhs plus rhs is res*)
    | Plus of lhs: Nat * rhs: Nat * res: Nat
    (* lhs times rhs is res *)
    | Times of lhs: Nat * rhs: Nat * res: Nat
module Judge =
    let print = function
        | Plus(lhs, rhs, res) -> $"{lhs} plus {rhs} is {res}"
        | Times(lhs, rhs, res) -> $"{lhs} times {rhs} is {res}"

type Rule =
    (* Z plus n is n*)
    | PZero
    (* n1 plus n2 is n -> S(n1) plus n2 is S(n) *)
    | PSucc of Derivation
    (* Z times n is Z*)
    | TZero
    (* n1 times n2 is n3 /\ n2 plus n3 is n4 -> S(n1) times n2 is n4 *)
    | TSucc of Derivation * Derivation
and Derivation = Judge * Rule

let mapRule = function
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

let rec derive judge =
    let conclude by = (judge,by)
    match judge with
    | Plus(Z, n1, n2) when n1 = n2 -> conclude PZero
    | Plus(S(n1), n2, S(n)) -> conclude <| PSucc(derive <| Plus(n1, n2, n))
    | Times(Z, _, Z) -> conclude TZero
    | Times(S(n1), n2, n4) ->
        match (Nat.trySubtract n4 n2) with
        | None -> failwith "cannot derive(T-Succ)"
        | Some n3 ->
            let times = derive <| Times(n1, n2, n3)
            let plus = derive <| Plus(n2, n3, n4)
            conclude <| TSucc(times, plus)

    | _ -> failwith "cannot derive"

(* S(S(Z)) times S(S(Z)) is S(S(S(S(Z)))) *)
let judge = Times(S(S(Z)), S(S(Z)), S(S(S(S(Z)))))
let tree = judge |> derive

printfn "%s" (printDerivation Judge.print mapRule tree)