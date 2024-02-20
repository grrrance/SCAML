(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(* Original code was taken from
   https://gitlab.com/Kakadu/fp2020course-materials/-/blob/master/code/miniml *)

type binder = int [@@deriving show { with_path = false }]

module VarSet : sig
  include module type of Stdlib.Set.Make (Int)

  val pp : Format.formatter -> t -> unit
end

type binder_set = VarSet.t [@@deriving show { with_path = false }]

type ground =
  | TInt
  | TBool
  | TUnit
[@@deriving show { with_path = false }, equal]

type ty =
  | Prim of ground
  | Ty_var of binder
  | Arrow of ty * ty
[@@deriving show { with_path = false }]

type scheme = S of binder_set * ty [@@deriving show { with_path = false }]

type error =
  [ `Occurs_check
  | `No_variable of string
  | `Unification_failed of ty * ty
  ]

val print_typ : ty -> unit
val v : binder -> ty
val ( @-> ) : ty -> ty -> ty
val int_typ : ty
val bool_typ : ty
val unit_typ : ty
val print_typ_error : error -> unit
val stdlib : (string * scheme) list