(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type error = [ `ParsingError of string ]

val pp_error : Format.formatter -> [< `ParsingError of string ] -> unit

(** Main entry of parser *)
val parse : string -> (unit Ast.statements_list, error) result

type dispatch =
  { func_call : dispatch -> unit Ast.expression Angstrom.t (** Parser for function call *)
  ; parse_lam : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for anonymous functions (fun ... -> ...) *)
  ; parse_if : dispatch -> string -> unit Ast.expression Angstrom.t
  ; arithmetical : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for arithmetic operations *)
  ; parse_priority : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for only arithmetic operations *, /, % *)
  ; logical : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for logic operations without && and || operators *)
  ; parse_and : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for logic operations with && operator *)
  ; logical_sequence : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for logic operations with && and || operators *)
  ; bracket : dispatch -> unit Ast.expression Angstrom.t
      (** Parser for operations in brackets *)
  ; bracket_singles : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for all single program units like func call, lambda functions,
      if/then/else expressions and for operations or singles in brackets. *)
  ; all_singles : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for all single program units like func call, lambda functions,
      if/then/else expressions and for operations or singles in brackets 
      and for arithmetical priority operations (\*, /, %). *)
  ; all_ops : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for all expressions in MiniML except for let and let in expressions. *)
  ; parse_letin : dispatch -> string -> unit Ast.expression Angstrom.t
      (** Parser for let in definitions*)
  ; parse_def : dispatch -> string -> unit Ast.statement Angstrom.t
      (** Parser for let definitions *)
  }

(* A collection of miniparsers *)
val parse_miniml : dispatch
