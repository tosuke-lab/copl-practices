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
  (* Z is less than S(n) *)
  | LZero
  (* n1 is less than n2 -> S(n1) is less than S(n2) *)
  | LSuccSucc of Derivation
and Derivation = Judge * Rule

let mapRule = function
  | LZero -> "L-Zero", []
  | LSuccSucc(cond) -> "L-SuccSucc", [cond]

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
  | (Z, S(_)) -> conclude LZero
  | (_, Z) -> failwith "greater eq"
  | (S(n1), S(n2)) -> conclude <| LSuccSucc(derive <| (n1, n2))

(* S(S(Z)) is less than S(S(S(S(S(Z))))) *)
let judge = (S(S(Z)), S(S(S(S(S(Z))))))

judge
|> derive
|> printDerivation Judge.print mapRule
|> printfn "%s"
