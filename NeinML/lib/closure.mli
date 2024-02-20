(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

val unique_names : 'a Ast.statement list -> 'a Ast.statement list
val closure_converse : Typing.ty Ast.statement list -> Typing.ty Ast.statement list