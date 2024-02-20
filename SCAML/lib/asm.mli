(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-3.0 *)

type asm_val =
  | Imm of string
  | Reg of string
  | Mem of string

val codegen_program :  RestrictedAst.bexpr list -> (string, string) Result.t