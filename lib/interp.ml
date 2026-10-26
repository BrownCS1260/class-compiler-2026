open S_exp
open Ast
open Util

exception BadExpression of expr

type value = Number of int | Boolean of bool | Pair of value * value

let rec string_of_value (v : value) : string =
  match v with
  | Number n ->
      string_of_int n
  | Boolean b ->
      if b then "true" else "false"
  | Pair (v1, v2) ->
      Printf.sprintf "(pair %s %s)" (string_of_value v1)
        (string_of_value v2)

let rec interp_exp (defns : defn list) (env : value symtab)
    (exp : expr) : value =
  match exp with
  | Num n ->
      Number n
  | True ->
      Boolean true
  | False ->
      Boolean false
  | Var s when Symtab.mem s env ->
      Symtab.find s env
  | Var _ ->
      raise (BadExpression exp)
  | Prim1 (Not, arg) ->
      if interp_exp defns env arg = Boolean false then Boolean true
      else Boolean false
  | Prim0 Newline ->
      output_string stdout "\n" ;
      Boolean true
  | Prim0 ReadNum ->
      Number (input_line stdin |> int_of_string)
  | Prim1 (Print, arg) ->
      interp_exp defns env arg
      |> string_of_value |> output_string stdout ;
      Boolean true
  | Prim1 (ZeroP, arg) -> (
    match interp_exp defns env arg with
    | Number 0 ->
        Boolean true
    | _ ->
        Boolean false )
  | Prim1 (NumP, arg) -> (
    match interp_exp defns env arg with
    | Number _ ->
        Boolean true
    | _ ->
        Boolean false )
  | Prim1 (Add1, arg) -> (
    match interp_exp defns env arg with
    | Number n ->
        Number (n + 1)
    | _ ->
        raise (BadExpression exp) )
  | Prim1 (Sub1, arg) -> (
    match interp_exp defns env arg with
    | Number n ->
        Number (n - 1)
    | _ ->
        raise (BadExpression exp) )
  | Prim1 (Left, arg) -> (
    match interp_exp defns env arg with
    | Pair (l, _) ->
        l
    | _ ->
        raise (BadExpression exp) )
  | Prim1 (Right, arg) -> (
    match interp_exp defns env arg with
    | Pair (_, r) ->
        r
    | _ ->
        raise (BadExpression exp) )
  | Prim2 (Plus, e1, e2) -> (
    match (interp_exp defns env e1, interp_exp defns env e2) with
    | Number n1, Number n2 ->
        Number (n1 + n2)
    | _ ->
        raise (BadExpression exp) )
  | Prim2 (Minus, e1, e2) -> (
      let v1 = interp_exp defns env e1 in
      let v2 = interp_exp defns env e2 in
      match (v1, v2) with
      | Number n1, Number n2 ->
          Number (n1 - n2)
      | _ ->
          raise (BadExpression exp) )
  | Prim2 (Eq, e1, e2) -> (
    match (interp_exp defns env e1, interp_exp defns env e2) with
    | Number n1, Number n2 ->
        Boolean (n1 = n2)
    | _ ->
        raise (BadExpression exp) )
  | Prim2 (Lt, e1, e2) -> (
    match (interp_exp defns env e1, interp_exp defns env e2) with
    | Number n1, Number n2 ->
        Boolean (n1 < n2)
    | _ ->
        raise (BadExpression exp) )
  | If (test_exp, then_exp, else_exp) ->
      if interp_exp defns env test_exp = Boolean false then
        interp_exp defns env else_exp
      else interp_exp defns env then_exp
  | Let (var, e, body) ->
      let e_value = interp_exp defns env e in
      interp_exp defns (Symtab.add var e_value env) body
  | Pair (e1, e2) ->
      let v1 = interp_exp defns env e1 in
      let v2 = interp_exp defns env e2 in
      Pair (v1, v2)
  | Do exps ->
      exps |> List.rev_map (interp_exp defns env) |> List.hd
  | Call (f, args) when is_defn defns f ->
      let defn = get_defn defns f in
      if List.length args = List.length defn.args then
        let vals = List.map (interp_exp defns env) args in
        let fenv = List.combine defn.args vals |> Symtab.of_list in
        interp_exp defns fenv defn.body
      else raise (BadExpression exp)
  | Call (_, _) ->
      raise (BadExpression exp)

let interp (program : string) : unit =
  let out = parse program |> expr_of_s_exp in
  if has_free_vars out then raise (BadExpression out) ;
  interp_exp defns Symtab.empty out |> ignore
