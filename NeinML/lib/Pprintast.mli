(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Format
open Ast

val pp_const : formatter -> const -> unit
val pp_binop : formatter -> binop -> unit
val pp_args : formatter -> name list -> unit
val pp_expression : formatter -> 'a expression -> unit
val pp_statement : formatter -> 'a statement -> unit
val pp_statements_list : formatter -> 'a statements_list -> unit
