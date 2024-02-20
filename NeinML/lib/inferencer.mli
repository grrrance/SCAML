(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(* Original code was taken from
   https://gitlab.com/Kakadu/fp2020course-materials/-/blob/master/code/miniml *)

val w_stms_list
  :  unit Ast.statements_list
  -> (Typing.ty list * Typing.ty Ast.statements_list, Typing.error) Result.t

val parse_and_infer : string -> unit
