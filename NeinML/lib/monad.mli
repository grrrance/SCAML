(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

module type Monad = sig
  type 'a t

  val return : 'a -> 'a t
  val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
end

module type StateSig = functor
  (S : sig
     type t
   end)
  -> sig
  include Monad

  val get : S.t t
  val put : S.t -> unit t
  val modify : (S.t -> S.t) -> unit t
  val run : S.t -> 'a t -> 'a * S.t
  val eval : S.t -> 'a t -> 'a
end

module State : StateSig

module ListM (M : Monad) : sig
  val fold_left : ('state -> 'b -> 'state M.t) -> 'state -> 'b list -> 'state M.t
  val fold_right : ('b -> 'state -> 'state M.t) -> 'b list -> 'state -> 'state M.t
  val map : ('a -> 'b M.t) -> 'a list -> 'b list M.t
end
