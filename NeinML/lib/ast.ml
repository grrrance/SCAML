(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type name = string [@@deriving eq, show { with_path = false }]

type const =
  | VInt of int
  | VBool of bool
[@@deriving show { with_path = false }]

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Equal
  | NotEqual
  | Less
  | LessOrEq
  | More
  | MoreOrEq
[@@deriving show { with_path = false }]

type 'a expression =
  | BinOp of 'a expression * 'a expression * binop * 'a
  | LetIn of name * 'a expression * 'a expression * 'a
  | RecLetIn of name * 'a expression * 'a expression * 'a
  | IfThenElse of 'a expression * 'a expression * 'a expression * 'a
  | Func of name * 'a expression * 'a
  | Apply of 'a expression * 'a expression * 'a
  | Variable of name * 'a
  | Value of const * 'a
[@@deriving show { with_path = false }]

type 'a statement =
  | Define of name * 'a expression * 'a
  | RecDefine of name * 'a expression * 'a
[@@deriving show { with_path = false }]

type 'a statements_list = 'a statement list [@@deriving show { with_path = false }]

let get_meta = function
  | BinOp (_, _, _, meta)
  | LetIn (_, _, _, meta)
  | RecLetIn (_, _, _, meta)
  | IfThenElse (_, _, _, meta)
  | Func (_, _, meta)
  | Apply (_, _, meta)
  | Variable (_, meta)
  | Value (_, meta) -> meta
;;

let get_binop_str = function
  | Add -> "add"
  | Sub -> "sub"
  | Mul -> "mul"
  | Div -> "div"
  | Mod -> "mod"
  | And -> "and"
  | Or -> "or"
  | Equal -> "eq"
  | NotEqual -> "noteq"
  | Less -> "less"
  | LessOrEq -> "lessoreq"
  | More -> "more"
  | MoreOrEq -> "moreoreq"
;;

let cval x meta = Value (x, meta)
let cvar x meta = Variable (x, meta)
let cbinop x y op meta = BinOp (x, y, op, meta)
let capply x y meta = Apply (x, y, meta)
let cfunc x y meta = Func (x, y, meta)
let cdef x y meta = Define (x, y, meta)
let crecdef x y meta = RecDefine (x, y, meta)
let cletin x y z meta = LetIn (x, y, z, meta)
let crecletin x y z meta = RecLetIn (x, y, z, meta)
let cifthenelse x y z meta = IfThenElse (x, y, z, meta)
