(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

module type MONAD = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type RESULTSTATE = sig
  type state
  type e_msg

  type 'a res =
    | ROk of 'a
    | RErr of e_msg

  include MONAD

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  val ok : 'a -> 'a t
  val error : e_msg -> 'a t
  val get : state t
  val put : state -> unit t
  val runResState : 'a t -> init:state -> state * 'a res
end

module ResState (S : sig
    type e_msg
    type st
  end) : RESULTSTATE with type state = S.st and type e_msg = S.e_msg = struct
  type e_msg = S.e_msg

  type 'a res =
    | ROk of 'a
    | RErr of e_msg

  type state = S.st
  type 'a t = state -> state * 'a res

  let return v s = s, ROk v
  let ok v s = s, ROk v
  let error e s = s, RErr e

  let ( >>= ) m k s =
    match m s with
    | s', ROk v -> k v s'
    | s', RErr e -> s', RErr e
  ;;

  module Syntax = struct
    let ( let* ) x f = x >>= f
  end

  let get s = s, ROk s
  let put s' _ = s', ROk ()
  let runResState m ~init = m init
end

module IResState = ResState (struct
    type st = int * int
    type e_msg = string
  end)

let fresh_if : (int * int) IResState.t =
  let open IResState in
  get >>= fun (c1, c2) -> put (c1, c2 + 1) >>= fun () -> return (c1, c2)
;;

let decr_offset : (int * int) IResState.t =
  let open IResState in
  get >>= fun (c1, c2) -> put (c1 - 8, c2) >>= fun () -> return (c1 - 8, c2)
;;

let get_counters : (int * int) IResState.t =
  let open IResState in
  get >>= fun (c1, c2) -> return (c1, c2)
;;
