(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type RESULTSTATE = sig
  type state
  type errorMsg

  type 'a res =
    | ROk of 'a
    | RErr of errorMsg

  include MONAD

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  val ok : 'a -> 'a t
  val error : errorMsg -> 'a t
  val get : state t
  val put : state -> unit t
  val runResState : 'a t -> init:state -> state * 'a res
end

module ResState (S : sig
    type eMsg
    type st
  end) : RESULTSTATE with type state = S.st and type errorMsg = S.eMsg

module IResState : RESULTSTATE with type state = int * int and type errorMsg = string

val fresh_if : (int * int) IResState.t
val decr_offset : (int * int) IResState.t
val get_counters : (int * int) IResState.t
