open System

type Nat = 
    | Z
    | S of Nat
    with
        override this.ToString() =
            match this with
            | Z -> "Z"
            | S(n) -> $"S({n.ToString()})"

type Judge = Nat * Nat
module Judge =
    let print (lhs,rhs) = $"{lhs} is less than {rhs}"

type Rule =
    (* n is less than S(n) *)
    | LSucc
    (* n1 is less than n2 -> n1 is less than S(n2) *)
    | LSuccR of Derivation
and Derivation = Judge * Rule

let mapRule = function
    | LSucc -> "L-Succ", []
    | LSuccR(cond) -> "L-SuccR", [cond]

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
  let conclude by = (judge, by)
  match judge with
  | (n1, S(n2)) when n1 = n2 -> conclude LSucc
  | (n1, S(n2)) -> conclude <| LSuccR(derive <| (n1, n2))
  | (_, Z) -> failwith "greater eq"

(* S(S(Z)) is less than S(S(S(S(S(Z))))) *)
let judge = (S(S(Z)), S(S(S(S(S(Z))))))

judge
|> derive
|> printDerivation Judge.print mapRule
|> printfn "%s"
