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

module State : StateSig =
functor
  (S : sig
     type t
   end)
  ->
  struct
    type 'a t = S.t -> 'a * S.t

    let return x state = x, state

    let ( >>= ) m f state =
      let x, state = m state in
      f x state
    ;;

    let get state = state, state
    let put state _ = (), state
    let modify f state = (), f state
    let run init m = m init
    let eval init m = m init |> fst
  end

module ListM (M : Monad) : sig
  val fold_left : ('state -> 'b -> 'state M.t) -> 'state -> 'b list -> 'state M.t
  val fold_right : ('b -> 'state -> 'state M.t) -> 'b list -> 'state -> 'state M.t
  val map : ('a -> 'b M.t) -> 'a list -> 'b list M.t
end = struct
  let rec fold_left f state = function
    | [] -> M.return state
    | x :: xs -> M.( >>= ) (f state x) (fun state -> fold_left f state xs)
  ;;

  let rec fold_right f list state =
    match list with
    | [] -> M.return state
    | x :: xs -> M.( >>= ) (fold_right f xs state) (fun state -> f x state)
  ;;

  let rec map f = function
    | [] -> M.return []
    | x :: xs ->
      M.( >>= ) (f x) (fun x -> M.( >>= ) (map f xs) (fun xs -> M.return @@ (x :: xs)))
  ;;
end
