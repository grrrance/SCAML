(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Format
open Ast
open Base

let pp_const fmt = function
  | VInt value -> fprintf fmt "%d" value
  | VBool value -> fprintf fmt "%b" value
;;

let pp_binop fmt = function
  | Add -> fprintf fmt "%s" "+"
  | Sub -> fprintf fmt "%s" "-"
  | Mul -> fprintf fmt "%s" "*"
  | Div -> fprintf fmt "%s" "/"
  | Mod -> fprintf fmt "%s" "%"
  | And -> fprintf fmt "%s" "&&"
  | Or -> fprintf fmt "%s" "||"
  | Equal -> fprintf fmt "%s" "="
  | NotEqual -> fprintf fmt "%s" "<>"
  | Less -> fprintf fmt "%s" "<"
  | LessOrEq -> fprintf fmt "%s" "<="
  | More -> fprintf fmt "%s" ">"
  | MoreOrEq -> fprintf fmt "%s" ">="
;;

let rec get_params acc = function
  | Func (arg, body, _) -> get_params (arg :: acc) body
  | _ as expr -> acc, expr
;;

let pp_args fmt =
  pp_print_list
    ~pp_sep:(fun fmt _ -> fprintf fmt " ")
    (fun fmt value -> fprintf fmt "%s" value)
    fmt
;;

let rec pp_expression fmt = function
  | Variable (varname, _) -> fprintf fmt "%s" varname
  | Value (value, _) -> pp_const fmt value
  | BinOp (left, right, binop, _) ->
    fprintf fmt "%a %a %a" pp_expression left pp_binop binop pp_expression right
  | IfThenElse (condition, true_branch, false_branch, _) ->
    fprintf
      fmt
      "(if %a then %a else %a)"
      pp_expression
      condition
      pp_expression
      true_branch
      pp_expression
      false_branch
  | Apply (func, arg, _) -> fprintf fmt "%a %a" pp_expression func pp_expression arg
  | LetIn (func_name, def, body, _) ->
    let func_params, def_body = get_params [] def in
    let func_params = List.rev func_params in
    (match List.length func_params with
     | 0 ->
       fprintf
         fmt
         "let %s =\n %a in\n %a"
         func_name
         pp_expression
         def_body
         pp_expression
         body
     | _ ->
       fprintf
         fmt
         "let %s %a =\n %a in\n %a"
         func_name
         pp_args
         func_params
         pp_expression
         def_body
         pp_expression
         body)
  | RecLetIn (func_name, def, body, _) ->
    let func_params, def_body = get_params [] def in
    let func_params = List.rev func_params in
    (match List.length func_params with
     | 0 ->
       fprintf
         fmt
         "let rec %s =\n %a in\n %a"
         func_name
         pp_expression
         def_body
         pp_expression
         body
     | _ ->
       fprintf
         fmt
         "let rec %s %a =\n %a in\n %a"
         func_name
         pp_args
         func_params
         pp_expression
         def_body
         pp_expression
         body)
  | Func (_, _, _) as func_expr ->
    let func_params, def_body = get_params [] func_expr in
    let func_params = List.rev func_params in
    fprintf fmt "(fun %a -> %a)" pp_args func_params pp_expression def_body
;;

let pp_statement fmt = function
  | Define (def_name, def_expr, _) ->
    let func_params, def_body = get_params [] def_expr in
    let func_params = List.rev func_params in
    (match List.length func_params with
     | 0 -> fprintf fmt "let %s =\n %a" def_name pp_expression def_body
     | _ ->
       fprintf fmt "let %s %a =\n %a" def_name pp_args func_params pp_expression def_body)
  | RecDefine (def_name, def_expr, _) ->
    let func_params, def_body = get_params [] def_expr in
    let func_params = List.rev func_params in
    (match List.length func_params with
     | 0 -> fprintf fmt "let rec %s =\n %a" def_name pp_expression def_body
     | _ ->
       fprintf
         fmt
         "let rec %s %a =\n %a"
         def_name
         pp_args
         func_params
         pp_expression
         def_body)
;;

let pp_statements_list fmt =
  pp_print_list
    ~pp_sep:(fun fmt _ -> fprintf fmt "\n")
    (fun fmt value -> pp_statement fmt value)
    fmt
;;
