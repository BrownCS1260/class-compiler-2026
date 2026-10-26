open S_exp

type prim0 = ReadNum

let prim0_of_string (s : string) : prim0 option =
  match s with "read-num" -> Some ReadNum | _ -> None

type prim1 = Add1 | Sub1 | NumP | ZeroP | Not | Left | Right

let prim1_of_string (s : string) : prim1 option =
  match s with
  | "add1" ->
      Some Add1
  | "sub1" ->
      Some Sub1
  | "zero?" ->
      Some ZeroP
  | "num?" ->
      Some NumP
  | "not" ->
      Some Not
  | "left" ->
      Some Left
  | "right" ->
      Some Right
  | _ ->
      None

type prim2 = Plus | Minus | Eq | Lt

let prim2_of_string = function
  | "+" ->
      Some Plus
  | "-" ->
      Some Minus
  | "=" ->
      Some Eq
  | "<" ->
      Some Lt
  | _ ->
      None

type expr =
  | True
  | False
  | Num of int
  | Var of string
  | Prim0 of prim0
  | Prim1 of prim1 * expr
  | Prim2 of prim2 * expr * expr
  | If of expr * expr * expr
  | Let of string * expr * expr
  | Pair of expr * expr
  | Do of expr list

exception BadSExpression of s_exp

let rec expr_of_s_exp (e : s_exp) : expr =
  match e with
  | Num n ->
      Num n
  | Sym "true" ->
      True
  | Sym "false" ->
      False
  | Sym s ->
      Var s
  | Lst [Sym "if"; e1; e2; e3] ->
      If (expr_of_s_exp e1, expr_of_s_exp e2, expr_of_s_exp e3)
  | Lst [Sym op] when Option.is_some (prim0_of_string op) ->
      Prim0 (Option.get (prim0_of_string op))
  | Lst [Sym op; e1] when Option.is_some (prim1_of_string op) ->
      Prim1 (Option.get (prim1_of_string op), expr_of_s_exp e1)
  | Lst [Sym op; e1; e2] when Option.is_some (prim2_of_string op) ->
      Prim2
        ( Option.get (prim2_of_string op)
        , expr_of_s_exp e1
        , expr_of_s_exp e2 )
  | Lst [Sym "let"; Lst [Lst [Sym s; e]]; body] ->
      Let (s, expr_of_s_exp e, expr_of_s_exp body)
  | Lst [Sym "pair"; e1; e2] ->
      Pair (expr_of_s_exp e1, expr_of_s_exp e2)
  | Lst (Sym "do" :: l) ->
      Do (List.map expr_of_s_exp l)
  | _ ->
      raise (BadSExpression e)

let rec fv (bound : string list) (exp : expr) =
  match exp with
  | Var s when not (List.mem s bound) ->
      [s]
  | Var _ ->
      []
  | Let (v, e, body) ->
      fv bound e @ fv (v :: bound) body
  | If (te, the, ee) ->
      fv bound te @ fv bound the @ fv bound ee
  | Prim0 _ ->
      []
  | Prim1 (_, e) ->
      fv bound e
  | Prim2 (_, e1, e2) ->
      fv bound e1 @ fv bound e2
  | Pair (e1, e2) ->
      fv bound e1 @ fv bound e2
  | Num _ ->
      []
  | True ->
      []
  | False ->
      []
  | Do l ->
      List.fold_left (fun l e -> fv bound e @ l) [] l

let has_free_vars (exp : expr) : bool = fv [] exp <> []
