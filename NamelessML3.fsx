#r "nuget: ScanRat"
open System
open ScanRat.ScanRat

type Var = string

type Expr =
    | Int of int
    | Bool of bool
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
    with
        override this.ToString() =
            let rec print = function
                | Int i -> string i
                | Bool true -> "true"
                | Bool false -> "false"
                | Var x -> x
                | (Plus _) as e -> "(" + printPlus e + ")"
                | (Minus _) as e -> "(" + printMinus e + ")"
                | (Times _) as e -> "(" + printTimes e + ")"
                | Lt(e1, e2) -> "(" + (print e1) + " < " + (print e2) + ")"
                | If(e, et, ef) -> $"(if {print e} then {print et} else {print ef})"
                | Let(x, e1, e2) -> $"(let {x} = {print e1} in {print e2})"
                | LetRec(x, y, e1, e2) -> $"(let rec {x} = fun {y} -> {print e1} in {print e2})"
                | Func(x, e) -> $"(fun {x} -> {e})"
                | App(e, e') -> $"({e} {e'})"
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

type VarList =
    | VarList of Var list
    with
        override this.ToString() =
            let rec print = function
                | [] -> ""
                | [x] -> x
                | x::t -> $"{print t}, {x}"
            let (VarList l) = this
            print l

type DBValue =
    | Int of int
    | Bool of bool
    (* (V)[fun . -> d] *)
    | Func of DBValueList * DBExpr
    (* (V)[rec . = fun . -> d] *)
    | FuncRec of DBValueList * DBExpr
    with
        override this.ToString() =
            match this with
            | Int i -> string i
            | Bool true -> "true"
            | Bool false -> "false"
            | Func(vl, d) -> $"({vl})[fun . -> {d}]"
            | FuncRec(vl, d) -> $"({vl})[rec . = fun . -> {d}]"
and DBValueList =
    DBValueList of DBValue list
    with
        override this.ToString() =
            let rec print = function
                | [] -> ""
                | [w] -> w.ToString()
                | w::l -> $"{print l}, {w}"
            let (DBValueList v) = this
            print v
and DBExpr = 
    | Int of int
    | Bool of bool
    | Var of int
    | Plus of DBExpr * DBExpr
    | Minus of DBExpr * DBExpr
    | Times of DBExpr * DBExpr
    | Lt of DBExpr * DBExpr
    | If of DBExpr * DBExpr * DBExpr
    (* let . = d1 in d2 *)
    | Let of DBExpr * DBExpr
    (* let rec . = fun . -> d1 in d2 *)
    | LetRec of DBExpr * DBExpr
    (* fun . -> d *)
    | Func of DBExpr
    | App of DBExpr * DBExpr
    with 
        override this.ToString() =
            let rec print = function
                | DBExpr.Int i -> (Expr.Int i).ToString()
                | DBExpr.Bool b -> (Expr.Bool b).ToString()
                | DBExpr.Var i -> $"#{i}"
                | DBExpr.Plus (d1, d2) -> $"({print d1} + {print d2})"
                | DBExpr.Minus(d1, d2) -> $"({print d1} - {print d2})"
                | DBExpr.Times(d1, d2) -> $"({print d1} * {print d2})"
                | DBExpr.Lt   (d1, d2) -> $"({print d1} < {print d2})"
                | DBExpr.If(d1, d2, d3) -> $"(if {print d1} then {print d2} else {print d3})"
                | DBExpr.Let(d1, d2) -> $"(let . = {print d1} in {print d2})"
                | DBExpr.LetRec(d1, d2) -> $"(let rec . = fun . -> {print d1} in {print d2})"
                | DBExpr.Func d -> $"(fun . -> {print d})"
                | DBExpr.App(d1, d2) -> $"({print d1} {print d2})"
            print this

type Judge =
    (* Transform: X |- e ==> d *)
    | Tr of VarList * Expr * DBExpr
    (* V |- d evalto w *)
    | Eval of DBValueList * DBExpr * DBValue
    | Plus of int * int * int
    | Minus of int * int * int
    | Times of int * int * int
    | Lt of int * int * bool
    with
        override this.ToString() =
            match this with
            | Tr(vl, e, d) ->
                let vl = vl.ToString()
                let space = if vl = "" then "" else " "
                $"{vl}{space}|- {e} ==> {d}"
            | Eval(vl, d, w) ->
                let vl = vl.ToString()
                let space = if vl = "" then "" else " "
                $"{vl}{space}|- {d} evalto {w}"
            | Plus(i1, i2, i3) -> $"{i1} plus {i2} is {i3}"
            | Minus(i1, i2, i3) -> $"{i1} minus {i2} is {i3}"
            | Times(i1, i2, i3) -> $"{i1} times {i2} is {i3}"
            | Lt(i1, i2, b3) -> $"{i1} less than {i2} is {DBValue.Bool b3}"
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
        lower + lower.ToUpper() + "_."
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
        ) / (~~"if" |- ~~"then" |- ~~"else" |- ~~"let" |- ~~"rec" |- ~~"in" |- ~~"fun" |- ~~"evalto")
    
    let expr =
        let expr = production "expr"
        let term = production "term"
        term.rule
            <- ~~"(" +. sp +. expr .+ sp .+ ~~")"
            |- digits --> Expr.Int
            |- bool --> Expr.Bool
            |- ident --> Expr.Var
        let app = production "app"
        app.rule
            <- app .+ ~~" " + term --> Expr.App
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
            |- binop
        expr
    let (dbexpr, dbvalue, dbvaluelist) =
        let dbvar = ~~"#" +. digits --> DBExpr.Var
        let value = production "dbvalue"
        let valueList = production "valueList"
        let expr = production "dbexpr"
        value.rule
            <- digits --> DBValue.Int
            |- bool --> DBValue.Bool
            |- (~~"(" +. sp +. valueList .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ sp .+ ~~"fun" .+ sp1 .+ ~~"." .+ sp .+ ~~"->" .+ sp + expr .+ sp .+ ~~"]")
                --> DBValue.Func
            |- (~~"(" +. sp +. valueList .+ sp .+ ~~")" .+ sp .+ ~~"[" .+ ~~"rec" .+ sp1 .+ ~~"." .+ sp .+ ~~"=" .+ sp .+ ~~"fun" .+ sp1 .+ ~~"." .+ sp .+ ~~"->" .+ sp + expr .+ sp .+ ~~"]")
                --> DBValue.FuncRec
        valueList.rule
            <- valueList .+ sp .+ ~~"," .+ sp + value --> fun (DBValueList V, w) -> DBValueList(w::V)
            |- value --> fun w -> DBValueList [w]
            |- ~~"" --> fun _ -> DBValueList []
        let term = production "term"
        term.rule
            <- ~~"(" +. sp +. expr .+ sp .+ ~~")"
            |- digits --> DBExpr.Int
            |- bool --> DBExpr.Bool
            |- dbvar
        let app = production "app"
        app.rule
            <- app .+ ~~" " + term --> DBExpr.App
            |- term
        let binop = production "binop"
        binop.rule
            <- binop .+ sp .+ ~~"*" .+ sp + app --> DBExpr.Times
            |- binop .+ sp .+ ~~"+" .+ sp + app --> DBExpr.Plus
            |- binop .+ sp .+ ~~"-" .+ sp + app --> DBExpr.Minus
            |- binop .+ sp .+ ~~"<" .+ sp + app --> DBExpr.Lt
            |- app
        expr.rule
            <- (~~"if" +. sp1 +. expr .+ sp1 .+ ~~"then" .+ sp1 + expr .+ sp1 .+ ~~"else" .+ sp1 + expr)
                --> fun ((e, et), ef) -> DBExpr.If(e, et, ef)
            |- (~~"let" +. sp1 +. ~~"rec" +. sp1 +. ~~"." +. sp +. ~~"=" +. sp +. ~~"fun" +. sp1 +. ~~"." +. sp +. ~~"->" +. sp +. expr .+ sp1 .+ ~~"in" .+ sp1 + expr)
                --> DBExpr.LetRec
            |- (~~"let" +. sp1 +. ~~"." +. sp +. ~~"=" +. sp +. expr .+ sp1 .+ ~~"in" .+ sp1 + expr) --> DBExpr.Let
            |- (~~"fun" +. sp1 +. ~~"." +. sp +. ~~"->" +. sp +. expr) --> DBExpr.Func
            |- binop
        expr, value, valueList
    let varList = production "varlist"
    varList.rule
        <- varList .+ sp .+ ~~"," .+ sp + ident --> fun (VarList l, x) -> VarList(x::l)
        |- ident --> fun x -> VarList[x]
        |- ~~"" --> fun _ -> VarList[]
    
    let transform = varList .+ sp .+ ~~"|-" .+ sp + expr .+ sp .+ ~~"==>" .+ sp + dbexpr --> fun ((X, e), d) -> Tr(X, e, d)
    let evalto = dbvaluelist .+ sp .+ ~~"|-" .+ sp + dbexpr .+ sp1 .+ ~~"evalto" .+ sp1 + dbvalue --> fun ((V, d), w) -> Judge.Eval(V, d, w)
    let judge = transform |- evalto

let rec eval (DBValueList vl as dvl) dbexpr =
    let evalIntBinop dvl d1 d2 op =
        match (eval dvl d1, eval dvl d2) with 
        | (DBValue.Int i1, DBValue.Int i2) -> op i1 i2
        | _, _ -> failwith "Invalid type"
    match dbexpr with
    | DBExpr.Int i -> DBValue.Int i
    | DBExpr.Bool b -> DBValue.Bool b
    | DBExpr.Var n -> vl.Item(n - 1)
    | DBExpr.Plus(d1, d2) -> evalIntBinop dvl d1 d2 (+) |> DBValue.Int
    | DBExpr.Minus(d1, d2) -> evalIntBinop dvl d1 d2 (-) |> DBValue.Int
    | DBExpr.Times(d1, d2) -> evalIntBinop dvl d1 d2 ( * ) |> DBValue.Int
    | DBExpr.Lt(d1, d2) -> evalIntBinop dvl d1 d2 (<) |> DBValue.Bool
    | DBExpr.If(d1, d2, d3) ->
        match (eval dvl d1) with
        | DBValue.Bool true -> eval dvl d2
        | DBValue.Bool false -> eval dvl d3
        | _ -> failwith "invalid type"
    | DBExpr.Let(d1, d2) ->
        let w = eval dvl d1
        eval (DBValueList(w::vl)) d2
    | DBExpr.LetRec(d1, d2) ->
        eval (DBValueList((DBValue.FuncRec(dvl, d1))::vl)) d2
    | DBExpr.Func d ->
        DBValue.Func(dvl, d)
    | DBExpr.App(d1, d2) ->
        match (eval dvl d1, eval dvl d2) with
        | DBValue.Func(DBValueList vl2, d), w2 ->
            eval (DBValueList(w2::vl2)) d
        | DBValue.FuncRec(DBValueList vl2, d0) as w1, w2 ->
            eval (DBValueList(w2::w1::vl2)) d0
        | _, _ -> failwith "Invalid type(not func)"

let rec derive judge =
    let conclude name derivs = Derivation(judge, name, derivs)

    let deriveTrBinOp name dvl e1 e2 d1 d2 =
        conclude name [
            derive <| Tr(dvl, e1, d1);
            derive <| Tr(dvl, e2, d2);
        ]
    let deriveEvalBinOp name judge dvl d1 d2 r =
        match (eval dvl d1, eval dvl d2) with
        | (DBValue.Int i1 as w1), (DBValue.Int i2 as w2) ->
            conclude name [
                derive <| Eval(dvl, d1, w1);
                derive <| Eval(dvl, d2, w2);
                derive <| judge(i1, i2, r);
            ]
        | _ -> failwith "invalid type"

    match judge with
    | Tr(_, Expr.Int i, DBExpr.Int i') when i = i' -> conclude "Tr-Int" []
    | Tr(_, Expr.Bool b, DBExpr.Bool b') when b = b' -> conclude "Tr-Bool" []
    | Tr(vl, Expr.If(e1, e2, e3), DBExpr.If(d1, d2, d3)) ->
        conclude "Tr-If" [
            derive <| Tr(vl, e1, d1);
            derive <| Tr(vl, e2, d2);
            derive <| Tr(vl, e3, d3);
        ]
    | Tr(vl, Expr.Plus(e1, e2), DBExpr.Plus(d1, d2)) -> deriveTrBinOp "Tr-Plus" vl e1 e2 d1 d2
    | Tr(vl, Expr.Minus(e1, e2), DBExpr.Minus(d1, d2)) -> deriveTrBinOp "Tr-Minus" vl e1 e2 d1 d2
    | Tr(vl, Expr.Times(e1, e2), DBExpr.Times(d1, d2)) -> deriveTrBinOp "Tr-Times" vl e1 e2 d1 d2
    | Tr(vl, Expr.Lt(e1, e2), DBExpr.Lt(d1, d2)) -> deriveTrBinOp "Tr-Lt" vl e1 e2 d1 d2
    | Tr(VarList(x::X), Expr.Var x', DBExpr.Var 1) when x = x' -> conclude "Tr-Var1" []
    | Tr(VarList(y::X), (Expr.Var x as e), DBExpr.Var n) when x <> y && n > 1 ->
        conclude "Tr-Var2" [
            derive <| Tr(VarList X, e, DBExpr.Var (n - 1))
        ]
    | Tr(VarList X, Expr.Let(x, e1, e2), DBExpr.Let(d1, d2)) ->
        conclude "Tr-Let" [
            derive <| Tr(VarList X, e1, d1);
            derive <| Tr(VarList(x::X), e2, d2);
        ]
    | Tr(VarList X, Expr.Func(x, e), DBExpr.Func d) ->
        conclude "Tr-Fun" [
            derive <| Tr(VarList(x::X), e, d)
        ]
    | Tr(vl, Expr.App(e1, e2), DBExpr.App(d1, d2)) -> deriveTrBinOp "Tr-App" vl e1 e2 d1 d2
    | Tr(VarList X, Expr.LetRec(x, y, e1, e2), DBExpr.LetRec(d1, d2)) ->
        conclude "Tr-LetRec" [
            derive <| Tr(VarList(y::x::X), e1, d1);
            derive <| Tr(VarList(x::X), e2, d2);
        ]
    | Eval(_, DBExpr.Int i, DBValue.Int i') when i = i' -> conclude "E-Int" []
    | Eval(_, DBExpr.Bool b, DBValue.Bool b') when b = b' -> conclude "E-Bool" []
    | Eval(DBValueList vl, DBExpr.Var n, w) when vl.Item(n - 1) = w -> conclude "E-Var" []
    | Eval(dvl, DBExpr.Plus(d1, d2), DBValue.Int i3) ->
        deriveEvalBinOp "E-Plus" Judge.Plus dvl d1 d2 i3
    | Eval(dvl, DBExpr.Minus(d1, d2), DBValue.Int i3) ->
        deriveEvalBinOp "E-Minus" Judge.Minus dvl d1 d2 i3
    | Eval(dvl, DBExpr.Times(d1, d2), DBValue.Int i3) ->
        deriveEvalBinOp "E-Times" Judge.Times dvl d1 d2 i3
    | Eval(dvl, DBExpr.Lt(d1, d2), DBValue.Bool b3) ->
        deriveEvalBinOp "E-Lt" Judge.Lt dvl d1 d2 b3
    | Eval(dvl, DBExpr.If(d1, d2, d3), w) ->
        match (eval dvl d1) with
        | (DBValue.Bool true) ->
            conclude "E-IfT" [
                derive <| Eval(dvl, d1, DBValue.Bool true);
                derive <| Eval(dvl, d2, w)
            ]
        | (DBValue.Bool false) ->
            conclude "E-IfF" [
                derive <| Eval(dvl, d1, DBValue.Bool false);
                derive <| Eval(dvl, d3, w)
            ]
        | _ -> failwith "Invalid type"
    | Eval((DBValueList vl as dvl), DBExpr.Let(d1, d2), w) ->
        let w1 = eval dvl d1
        conclude "E-Let" [
            derive <| Eval(dvl, d1, w1);
            derive <| Eval(DBValueList(w1::vl), d2, w)
        ]
    | Eval((DBValueList vl as dvl), DBExpr.LetRec(d1, d2), w) ->
        conclude "E-LetRec" [
            derive <| Eval(DBValueList(DBValue.FuncRec(dvl, d1)::vl), d2, w)
        ]
    | Eval(dvl, DBExpr.Func d, DBValue.Func(dvl', d')) when dvl = dvl' && d = d' -> conclude "E-Fun" []
    | Eval(dvl, DBExpr.App(d1, d2), w) ->
        match (eval dvl d1, eval dvl d2) with
        | (DBValue.Func(DBValueList vl2, d0) as w1), w2 ->
            conclude "E-App" [
                derive <| Eval(dvl, d1, w1);
                derive <| Eval(dvl, d2, w2);
                derive <| Eval(DBValueList(w2::vl2), d0, w);
            ]
        | (DBValue.FuncRec(DBValueList vl2, d0) as w1), w2 ->
            conclude "E-AppRec" [
                derive <| Eval(dvl, d1, w1);
                derive <| Eval(dvl, d2, w2);
                derive <| Eval(DBValueList(w2::w1::vl2), d0, w);
            ]
        | (_, _) -> failwith "d1 must be function"
    | Plus (i1, i2, i3) when i3 = i1 + i2 -> conclude "B-Plus" []
    | Minus(i1, i2, i3) when i3 = i1 - i2 -> conclude "B-Minus" []
    | Times(i1, i2, i3) when i3 = i1 * i2 -> conclude "B-Times" []
    | Lt(i1, i2, b3)    when b3 = (i1 < i2) -> conclude "B-Lt" []
    | j ->
        failwithf "Invalid input(maybe unimplemented): %A" j

"|- let rec . = fun . -> 
     if #1 < 2 then 1 else #1 * #2 (#1 - 1) in #1 3
   evalto 6"
|> parse Parser.judge
|> function
    | Success s -> s.Value
    | Failure e -> failwithf "%A" e
|> fun t -> printfn "%A" t; t
|> derive
|> printDerivation Judge.print
|> printfn "%s"