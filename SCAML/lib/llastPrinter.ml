(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-3.0 *)

open AstPrinter
open Llast
open Format

let rec pp_llexpr fmt = function
  | LLConst c -> pp_const fmt c
  | LLVar v -> fprintf fmt "%s" v
  | LLBinOp (op, l1, l2) ->
    fprintf fmt "(%a %a %a)" pp_llexpr l1 pp_bin_op op pp_llexpr l2
  | LLIf (l1, l2, l3) ->
    fprintf fmt "(if %a then %a else %a)" pp_llexpr l1 pp_llexpr l2 pp_llexpr l3
  | LLApp (l1, l2) -> fprintf fmt "(%a %a)" pp_llexpr l1 pp_llexpr l2
  | LLLetIn (id, l1, l2) -> fprintf fmt "let %s = %a in %a" id pp_llexpr l1 pp_llexpr l2
  | LLTuple ls -> fprintf fmt "(%a)" (fun fmt -> pp_list fmt pp_llexpr ", ") ls
  | LLGetFromTuple (l1, l2) -> fprintf fmt "%s[%d]" l1 l2
;;

let pp_ids fmt = function
  | [] -> ()
  | [ id ] -> fprintf fmt "%s" id
  | ids ->
    fprintf fmt "%a" (fun fmt -> pp_list fmt (fun fmt id -> fprintf fmt "%s" id) " ") ids
;;

let pp_llbinding fmt = function
  | LLLet (rec_flag, id, ids, l) ->
    fprintf fmt "let %a %s %a  = %a" pp_rec_flag rec_flag id pp_ids ids pp_llexpr l
;;
