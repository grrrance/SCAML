(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Format

val pp_expression : formatter -> Lambda_lifting.expression -> unit

val pp_var_decl_ll
  :  formatter
  -> Lambda_lifting.expression Lambda_lifting.var_decl
  -> unit

val pp_immexpr : formatter -> Anf.imm_expr -> unit
val pp_cexpr : formatter -> Anf.cexpr -> unit

val pp_statement
  :  (formatter -> 'a Lambda_lifting.var_decl list -> unit)
  -> (formatter -> 'a -> unit)
  -> formatter
  -> 'a Lambda_lifting.statement
  -> unit

val pp_statements_list
  :  (formatter -> 'a Lambda_lifting.var_decl list -> unit)
  -> (formatter -> 'a -> unit)
  -> formatter
  -> 'a Lambda_lifting.statement list
  -> unit

val pp_statements_list_anf : formatter -> Anf.cexpr Lambda_lifting.statement list -> unit

val pp_statements_list_ll
  :  formatter
  -> Lambda_lifting.expression Lambda_lifting.statement list
  -> unit
