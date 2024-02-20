(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

val codegen : Anf.cexpr Lambda_lifting.statement list -> Llvm.llvalue list