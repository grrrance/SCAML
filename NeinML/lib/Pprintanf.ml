(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Format
open Base

let rec pp_expression fmt = function
  | Lambda_lifting.Variable (varname, _) -> fprintf fmt "%s" varname
  | Lambda_lifting.Value (value, _) -> Pprintast.pp_const fmt value
  | Lambda_lifting.BinOp (left, right, binop, _) ->
    fprintf fmt "%a %a %a" pp_expression left Pprintast.pp_binop binop pp_expression right
  | Lambda_lifting.IfThenElse (condition, true_branch, false_branch, _) ->
    fprintf
      fmt
      "if %a then %a else %a"
      pp_expression
      condition
      pp_expression
      true_branch
      pp_expression
      false_branch
  | Lambda_lifting.Apply (func, arg, args, _) ->
    let pp_args fmt =
      pp_print_list
        ~pp_sep:(fun fmt _ -> fprintf fmt " ")
        (fun fmt value -> pp_expression fmt value)
        fmt
    in
    (match func with
     | Variable _ -> fprintf fmt "%a %a" pp_expression func pp_args (arg :: args)
     | _ -> fprintf fmt "(%a) %a" pp_expression func pp_args (arg :: args))
;;

let pp_var_decl_ll fmt = function
  | let_name, let_def, _ -> fprintf fmt "let %s =\n %a in" let_name pp_expression let_def
;;

let pp_letins_ll fmt =
  pp_print_list
    ~pp_sep:(fun fmt _ -> fprintf fmt "\n")
    (fun fmt value -> pp_var_decl_ll fmt value)
    fmt
;;

let pp_immexpr fmt = function
  | Anf.ImmInt value -> fprintf fmt "%d" value
  | Anf.ImmBool value -> fprintf fmt "%b" value
  | Anf.ImmVar (varname, _) -> fprintf fmt "%s" varname
;;

let rec pp_cexpr fmt = function
  | Anf.CBinOp (left, right, binop, _) ->
    fprintf fmt "%a %a %a" pp_immexpr left Pprintast.pp_binop binop pp_immexpr right
  | Anf.CApply (func, arg, args, _) ->
    let pp_args fmt =
      pp_print_list
        ~pp_sep:(fun fmt _ -> fprintf fmt " ")
        (fun fmt value -> pp_immexpr fmt value)
        fmt
    in
    fprintf fmt "%s %a" func pp_args (arg :: args)
  | Anf.CIfThenElse (condition, (then_lets, then_expr), (else_lets, else_expr), _) ->
    fprintf
      fmt
      "if %a then %a\n %a\n else %a\n %a"
      pp_immexpr
      condition
      pp_letins_anf
      then_lets
      pp_cexpr
      then_expr
      pp_letins_anf
      else_lets
      pp_cexpr
      else_expr
  | Anf.CImm imm -> fprintf fmt "%a" pp_immexpr imm

and pp_var_decl_anf fmt = function
  | let_name, let_def, _ -> fprintf fmt "let %s =\n %a in" let_name pp_cexpr let_def

and pp_letins_anf fmt =
  pp_print_list
    ~pp_sep:(fun fmt _ -> fprintf fmt "\n")
    (fun fmt value -> pp_var_decl_anf fmt value)
    fmt
;;

let pp_statement pp_letins pp_expr fmt = function
  | Lambda_lifting.Define (def_name, def_args, letins, fin_expr, _) ->
    (match List.length def_args with
     | 0 ->
       (match List.length letins with
        | 0 -> fprintf fmt "let %s =\n %a" def_name pp_expr fin_expr
        | _ -> fprintf fmt "let %s =\n %a\n %a" def_name pp_letins letins pp_expr fin_expr)
     | _ ->
       (match List.length letins with
        | 0 ->
          fprintf
            fmt
            "let %s %a =\n %a"
            def_name
            Pprintast.pp_args
            def_args
            pp_expr
            fin_expr
        | _ ->
          fprintf
            fmt
            "let %s %a =\n %a\n %a"
            def_name
            Pprintast.pp_args
            def_args
            pp_letins
            letins
            pp_expr
            fin_expr))
  | Lambda_lifting.RecDefine (def_name, def_args, letins, fin_expr, _) ->
    (match List.length def_args with
     | 0 ->
       (match List.length letins with
        | 0 -> fprintf fmt "let rec %s =\n %a" def_name pp_expr fin_expr
        | _ ->
          fprintf fmt "let rec %s =\n %a\n %a" def_name pp_letins letins pp_expr fin_expr)
     | _ ->
       (match List.length letins with
        | 0 ->
          fprintf
            fmt
            "let rec %s %a =\n %a"
            def_name
            Pprintast.pp_args
            def_args
            pp_expr
            fin_expr
        | _ ->
          fprintf
            fmt
            "let rec %s %a =\n %a\n %a"
            def_name
            Pprintast.pp_args
            def_args
            pp_letins
            letins
            pp_expr
            fin_expr))
;;

let pp_statements_list pp_letins pp_expr fmt =
  pp_print_list
    ~pp_sep:(fun fmt _ -> fprintf fmt "\n")
    (fun fmt value -> (pp_statement pp_letins pp_expr) fmt value)
    fmt
;;

let pp_statements_list_anf = pp_statements_list pp_letins_anf pp_cexpr
let pp_statements_list_ll = pp_statements_list pp_letins_ll pp_expression