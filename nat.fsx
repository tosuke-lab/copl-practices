open System

type Nat = 
    | Z
    | S of Nat

let rec minus lhs rhs =
    match (lhs, rhs) with
    | (n, Z) -> Some n
    | (Z, S(_)) -> None
    | (S(n1), S(n2)) -> minus n1 n2

type Judge =
    (* lhs plus rhs is res*)
    | Plus of lhs: Nat * rhs: Nat * res: Nat
    (* lhs times rhs is res *)
    | Times of lhs: Nat * rhs: Nat * res: Nat

type Rule =
    (* Z plus n is n*)
    | PZero
    (* n1 plus n2 is n -> S(n1) plus n2 is S(n) *)
    | PSucc of Derivation
    (* Z times n is Z*)
    | TZero
    (* n1 times n2 is n3 /\ n2 plus n3 is n4 -> S(n1) times n2 is n4 *)
    | TSucc of Derivation * Derivation

and Derivation =
    | Derivation of judge: Judge * by: Rule

let rec printNat = function
    | Z -> "Z"
    | S(n) -> $"S({printNat n})"

let printJudge = function
    | Plus(lhs, rhs, res) -> $"{printNat lhs} plus {printNat rhs} is {printNat res}"
    | Times(lhs, rhs, res) -> $"{printNat lhs} times {printNat rhs} is {printNat res}"

let rec printDerivation level (Derivation(judge, by)) =
    let indent = String.replicate level "  "
    indent + $"{printJudge judge} by {printRule level by}"
and printRule level rule =
    let print name = function
    | [] -> $"{name} {{}};"
    | l ->
        let children = l |> List.fold (fun pre driv -> pre + (printDerivation (level+1) driv) + "\n") ""
        $"{name} {{\n" + children + String.replicate level "  " + "};"
    match rule with
    | PZero -> print "P-Zero" []
    | PSucc(plus) -> print "P-Succ" [plus]
    | TZero -> print "T-Zero" []
    | TSucc(times, plus) -> print "T-Succ" [times; plus]

let rec derive judge =
    let conclude by = Derivation(judge,by)
    match judge with
    | Plus(Z, n1, n2) when n1 = n2 -> conclude PZero
    | Plus(S(n1), n2, S(n)) -> conclude <| PSucc(derive <| Plus(n1, n2, n))
    | Times(Z, _, Z) -> conclude TZero
    | Times(S(n1), n2, n4) ->
        match (minus n4 n2) with
        | None -> failwith "cannot derive(T-Succ)"
        | Some n3 ->
            let times = derive <| Times(n1, n2, n3)
            let plus = derive <| Plus(n2, n3, n4)
            conclude <| TSucc(times, plus)

    | _ -> failwith "cannot derive"

(* S(S(Z)) times S(S(Z)) is S(S(S(S(Z)))) *)
let judge = Times(S(S(Z)), S(S(Z)), S(S(S(S(Z)))))
let tree = judge |> derive

printfn "%s" (printDerivation 0 tree)