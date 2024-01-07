(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-3.0 *)

(* http://dev.stephendiehl.com/fun/006_hindley_milner.html *)

(* The code is a modified version of the inferencer taken from here
   https://gitlab.com/Kakadu/fp2020course-materials/-/blob/master/code/miniml*)

open Base
open Ast
open Ty
module Format = Stdlib.Format (* silencing a warning *)

module R : sig
  type 'a t

  val return : 'a -> 'a t
  val fail : error -> 'a t

  include Monad.Infix with type 'a t := 'a t

  module Syntax : sig
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  end

  module RMap : sig
    val fold_left
      :  (int, 'a, Base.Int.comparator_witness) Base.Map.t
      -> init:'b t
      -> f:('b -> int * 'a -> 'b t)
      -> 'b t
  end

  (** Creation of a fresh name from internal state *)
  val fresh : int t

  (** Running a transformer: getting the inner result value *)
  val run : 'a t -> ('a, error) Result.t
end = struct
  (* A compositon: State monad after Result monad *)
  type 'a t = int -> int * ('a, error) Result.t

  let ( >>= ) : 'a 'b. 'a t -> ('a -> 'b t) -> 'b t =
    fun m f st ->
    let last, r = m st in
    match r with
    | Result.Error x -> last, Error x
    | Ok a -> f a last
  ;;

  let fail e st = st, Result.fail e
  let return x last = last, Result.return x
  let bind x ~f = x >>= f

  let ( >>| ) : 'a 'b. 'a t -> ('a -> 'b) -> 'b t =
    fun x f st ->
    match x st with
    | st, Ok x -> st, Ok (f x)
    | st, Result.Error e -> st, Result.Error e
  ;;

  module Syntax = struct
    let ( let* ) x f = bind x ~f
  end

  module RMap = struct
    let fold_left map ~init ~f =
      Map.fold map ~init ~f:(fun ~key ~data acc ->
        let open Syntax in
        let* acc = acc in
        f acc (key, data))
    ;;
  end

  let fresh : int t = fun last -> last + 1, Result.Ok last
  let run m = snd (m 0)
end

type fresh = int

module Type = struct
  type t = ty

  let rec occurs_in v = function
    | TVar b -> b = v
    | TArrow (l, r) -> occurs_in v l || occurs_in v r
    | TTuple ts -> List.exists ~f:(occurs_in v) ts
    | TInt | TBool | TUnit -> false
  ;;

  let free_vars =
    let rec helper acc = function
      | TVar b -> VarSet.add b acc
      | TArrow (l, r) -> helper (helper acc l) r
      | TTuple ts -> List.fold_left ~f:helper ~init:acc ts
      | TInt | TBool | TUnit -> acc
    in
    helper VarSet.empty
  ;;
end

module Subst : sig
  type t

  val empty : t
  val singleton : fresh -> ty -> t R.t

  (** Getting value from substitution. May raise [Not_found] *)

  val apply : t -> ty -> ty
  val unify : ty -> ty -> t R.t

  (** Compositon of substitutions *)
  val compose : t -> t -> t R.t

  val compose_all : t list -> t R.t
  val remove : t -> fresh -> t
end = struct
  open R
  open R.Syntax

  type t = (fresh, ty, Int.comparator_witness) Map.t

  let empty = Map.empty (module Int)
  let mapping k v = if Type.occurs_in k v then fail `Occurs_check else return (k, v)

  let singleton k v =
    let* k, v = mapping k v in
    return (Map.singleton (module Int) k v)
  ;;

  let find k xs = Base.Map.find xs k
  let remove xs k = Base.Map.remove xs k

  let apply s =
    let rec helper = function
      | TVar b as ty ->
        (match find b s with
         | None -> ty
         | Some x -> x)
      | TArrow (l, r) -> TArrow (helper l, helper r)
      | TTuple ts -> TTuple (List.map ~f:helper ts)
      | other -> other
    in
    helper
  ;;

  let rec unify l r =
    match l, r with
    | TInt, TInt | TBool, TBool -> return empty
    | TVar a, TVar b when Int.equal a b -> return empty
    | TVar b, t | t, TVar b -> singleton b t
    | TArrow (l1, r1), TArrow (l2, r2) ->
      let* subs1 = unify l1 l2 in
      let* subs2 = unify (apply subs1 r1) (apply subs1 r2) in
      compose subs1 subs2
    | TTuple ts1, TTuple ts2 when List.length ts1 = List.length ts2 ->
      List.fold2_exn ts1 ts2 ~init:(return empty) ~f:(fun acc l r ->
        let* acc = acc in
        let* s = unify l r in
        compose acc s)
    | _ -> fail (`Unification_failed (l, r))

  and extend s (k, v) =
    match find k s with
    | None ->
      let v = apply s v in
      let* s2 = singleton k v in
      RMap.fold_left s ~init:(return s2) ~f:(fun acc (k, v) ->
        let v = apply s2 v in
        let* k, v = mapping k v in
        return (Map.add_exn acc ~key:k ~data:v))
    | Some v2 ->
      let* s2 = unify v v2 in
      compose s s2

  and compose s1 s2 = RMap.fold_left s2 ~init:(return s1) ~f:extend

  let compose_all ss =
    List.fold_left ss ~init:(return empty) ~f:(fun acc ss ->
      let* acc = acc in
      compose acc ss)
  ;;
end

module VarSet = struct
  include VarSet

  let fold_left_m f acc set =
    fold
      (fun x acc ->
        let open R.Syntax in
        let* acc = acc in
        f acc x)
      acc
      set
  ;;
end

module Scheme = struct
  type t = scheme

  let free_vars = function
    | S (bs, t) -> VarSet.diff (Type.free_vars t) bs
  ;;

  let apply sub (S (names, ty)) =
    let s2 = VarSet.fold (fun k s -> Subst.remove s k) names sub in
    S (names, Subst.apply s2 ty)
  ;;
end

module TypeEnv = struct
  type t = (id, scheme, String.comparator_witness) Map.t

  let extend e s = Base.Map.update e (fst s) ~f:(fun _ -> snd s)
  let empty = Map.empty (module String)

  let free_vars : t -> VarSet.t =
    Map.fold ~init:VarSet.empty ~f:(fun ~key:_ ~data:s acc ->
      VarSet.union acc (Scheme.free_vars s))
  ;;

  let apply s env = Map.map env ~f:(Scheme.apply s)
end

open R
open R.Syntax

let unify = Subst.unify
let fresh_var = fresh >>| fun n -> TVar n

let instantiate : scheme -> ty R.t =
  fun (S (bs, t)) ->
  VarSet.fold_left_m
    (fun typ name ->
      let* f1 = fresh_var in
      let* s = Subst.singleton name f1 in
      return (Subst.apply s typ))
    bs
    (return t)
;;

let generalize : TypeEnv.t -> Type.t -> Scheme.t =
  fun env ty ->
  let free = VarSet.diff (Type.free_vars ty) (TypeEnv.free_vars env) in
  S (free, ty)
;;

(* достает из окружения схему функции *)
let lookup_env e xs =
  match Map.find_exn xs e with
  | (exception Stdlib.Not_found) | (exception Not_found_s _) -> fail (`No_variable e)
  | scheme ->
    let* ans = instantiate scheme in
    return (Subst.empty, ans)
;;

let infer_pattern =
  let rec (pattern_helper : TypeEnv.t -> Ast.pattern -> (TypeEnv.t * Subst.t * ty) R.t) =
    fun env -> function
    | PVar x ->
      let* tv = fresh_var in
      let env = TypeEnv.extend env (x, S (VarSet.empty, tv)) in
      return (env, Subst.empty, tv)
    | PConst c ->
      (match c with
       | CInt _ -> return (env, Subst.empty, int_typ)
       | CBool _ -> return (env, Subst.empty, bool_typ)
       | CUnit -> return (env, Subst.empty, unit_typ))
    | PWild ->
      let* fresh = fresh_var in
      return (env, Subst.empty, fresh)
    | PTuple p ->
      let rec helper env s = function
        | [] -> return (env, s, [])
        | h :: tl ->
          let* env, s1, t1 = pattern_helper env h in
          let* s' = Subst.compose_all [ s1; s ] in
          let* env, s2, t2 = helper env s' tl in
          return (env, s2, t1 :: t2)
      in
      let* env, s, t = helper env Subst.empty p in
      let applied = List.map ~f:(Subst.apply s) t in
      return (env, s, TTuple applied)
  in
  pattern_helper
;;

let infer =
  let rec (helper : TypeEnv.t -> Ast.expr -> (Subst.t * ty) R.t) =
    fun env -> function
    | EBinOp (bin_op, l, r) ->
      let* sl, tl = helper env l in
      let* sr, tr = helper env r in
      (match bin_op with
       | Add | Sub | Mul | Div | Mod ->
         let* s1 = unify tl int_typ in
         let* s2 = unify tr int_typ in
         let* sres = Subst.compose_all [ s1; s2; sl; sr ] in
         return (sres, int_typ)
       | Less | Leq | Gre | Geq | Eq | Neq ->
         let* s1 = unify tl tr in
         let* sres = Subst.compose_all [ s1; sl; sr ] in
         return (sres, bool_typ)
       | And | Or ->
         let* s1 = unify tl bool_typ in
         let* s2 = unify tr bool_typ in
         let* sres = Subst.compose_all [ s1; s2; sl; sr ] in
         return (sres, bool_typ))
    | EVar x -> lookup_env x env
    | EFun (p, e1) ->
      let* env, s1, t1 = infer_pattern env p in
      let env2 = TypeEnv.apply s1 env in
      let* s, ty = helper env2 e1 in
      let trez = TArrow (Subst.apply s t1, ty) in
      let* final_subst = Subst.compose_all [ s; s1 ] in
      return (final_subst, trez)
    | EApp (e1, e2) ->
      let* s1, t1 = helper env e1 in
      let* s2, t2 = helper (TypeEnv.apply s1 env) e2 in
      let* tv = fresh_var in
      let* s3 = unify (Subst.apply s2 t1) (TArrow (t2, tv)) in
      let trez = Subst.apply s3 tv in
      let* final_subst = Subst.compose_all [ s3; s2; s1 ] in
      return (final_subst, trez)
    | EConst n ->
      (match n with
       | CInt _ -> return (Subst.empty, int_typ)
       | CBool _ -> return (Subst.empty, bool_typ)
       | CUnit -> return (Subst.empty, unit_typ))
    | EIf (c, th, el) ->
      let* s1, t1 = helper env c in
      let* s2, t2 = helper env th in
      let* s3, t3 = helper env el in
      let* s4 = unify t1 bool_typ in
      let* s5 = unify t2 t3 in
      let* final_subst = Subst.compose_all [ s5; s4; s3; s2; s1 ] in
      R.return (final_subst, Subst.apply s5 t2)
    | ELetIn (false, PVar id, e1, e2) ->
      let* s1, t1 = helper env e1 in
      let env2 = TypeEnv.apply s1 env in
      let t2 = generalize env2 t1 in
      let* s2, t3 = helper (TypeEnv.extend env2 (id, t2)) e2 in
      let* final_subst = Subst.compose s1 s2 in
      return (final_subst, t3)
    | ELetIn (true, PVar id, e1, e2) ->
      let* tv = fresh_var in
      let env = TypeEnv.extend env (id, S (VarSet.empty, tv)) in
      let* s1, t1 = helper env e1 in
      let* s2 = unify (Subst.apply s1 tv) t1 in
      let* s = Subst.compose s2 s1 in
      let env = TypeEnv.apply s env in
      let t2 = generalize env (Subst.apply s tv) in
      let* s2, t2 = helper TypeEnv.(extend (apply s env) (id, t2)) e2 in
      let* final_subst = Subst.compose s s2 in
      return (final_subst, t2)
    | ELetIn (false, pattern, e1, e2) ->
      let* s1, t1 = helper env e1 in
      let* env, s2, t2 = infer_pattern env pattern in
      let* s3 = unify t1 t2 in
      let* s4 = Subst.compose_all [ s3; s2; s1 ] in
      let* s5, t3 = helper env e2 in
      let* final_subst = Subst.compose s4 s5 in
      return (final_subst, t3)
    | ETuple tuple ->
      let rec tuple_helper s = function
        | [] -> return (s, [])
        | h :: tl ->
          let* s1, t1 = helper env h in
          let* s2 = Subst.compose s1 s in
          let* s3, t2 = tuple_helper s2 tl in
          return (s3, t1 :: t2)
      in
      let* s, t = tuple_helper Subst.empty tuple in
      let applied = List.map ~f:(Subst.apply s) t in
      return (s, TTuple applied)
    | _ -> fail `Incorrect_expression
  in
  helper
;;

let infer_prog prog =
  let sc_to_type = function
    | S (_, t) -> t
  in
  let rec helper env prog l =
    match prog with
    | h :: tl ->
      (match h with
       | ELet (false, PVar id, expr) ->
         let* s, t = infer env expr in
         let env = TypeEnv.apply s env in
         let t = generalize env t in
         let env = TypeEnv.extend env (id, t) in
         let l1 = l @ [ id, sc_to_type t ] in
         helper env tl l1
       | ELet (true, PVar id, expr) ->
         let* tv = fresh_var in
         let env = TypeEnv.extend env (id, S (VarSet.empty, tv)) in
         let* s, t = infer env expr in
         let* s2 = unify (Subst.apply s tv) t in
         let* s = Subst.compose s2 s in
         let env = TypeEnv.apply s env in
         let t = generalize env (Subst.apply s tv) in
         let env = TypeEnv.extend env (id, t) in
         let l1 = l @ [ id, sc_to_type t ] in
         helper env tl l1
       | ELet (false, pattern, expr) ->
         let* s, t = infer env expr in
         let* env, s2, t2 = infer_pattern env pattern in
         let* s3 = unify t (Subst.apply s t2) in
         let* s4 = Subst.compose_all [ s3; s2; s ] in
         let env = TypeEnv.apply s4 env in
         let pattern_str = Stdlib.Format.asprintf "%a" AstPrinter.pp_pattern pattern in
         let l1 = l @ [ pattern_str, Subst.apply s4 t2 ] in
         helper env tl l1
       | _ -> fail `Incorrect_expression)
    | [] -> return l
  in
  helper TypeEnv.empty prog []
;;

let w e = Result.map (run (infer TypeEnv.empty e)) ~f:snd
let run_prog_inference prog = run (infer_prog prog)

let print_prog_result prog =
  match run_prog_inference prog with
  | Ok l -> List.iter l ~f:(fun (id, t) -> Stdlib.Format.printf "%s : %a\n" id pp_typ t)
  | Error e -> print_typ_err e
;;

let print_result expression =
  match w expression with
  | Ok typ -> print_typ typ
  | Error e -> print_typ_err e
;;

let%expect_test _ =
  print_result
    (ELetIn
       ( true
       , PVar "fac"
       , EFun
           ( PVar "n"
           , EIf
               ( EBinOp (Leq, EVar "n", EConst (CInt 1))
               , EConst (CInt 1)
               , EBinOp
                   ( Mul
                   , EBinOp (Sub, EVar "n", EConst (CInt 1))
                   , EApp (EVar "fac", EBinOp (Sub, EVar "n", EConst (CInt 1))) ) ) )
       , EApp (EVar "fac", EConst (CInt 5)) ));
  [%expect {| int |}]
;;

let%expect_test _ =
  print_result (EFun (PVar "x", EFun (PVar "y", EFun (PVar "z", EConst (CInt 5)))));
  [%expect {| 'a -> 'b -> 'c -> int |}]
;;

let%expect_test _ =
  print_result
    (ELetIn
       ( false
       , PTuple [ PVar "x"; PVar "y" ]
       , ETuple [ EConst (CInt 5); EConst (CInt 5) ]
       , EVar "x" ));
  [%expect {| 'a |}]
;;

let%expect_test _ =
  print_result
    (ELetIn
       ( false
       , PVar "snd"
       , EFun (PTuple [ PVar "x"; PVar "y" ], EVar "y")
       , EApp (EVar "snd", ETuple [ EConst (CInt 1); EConst (CInt 2) ]) ));
  [%expect {| int |}]
;;

let%expect_test "let rec series n = if n = 1 then 1 else n + series (n - 1)" =
  print_prog_result
    [ ELet
        ( true
        , PVar "series"
        , EFun
            ( PVar "n"
            , EIf
                ( EBinOp (Eq, EVar "n", EConst (CInt 1))
                , EConst (CInt 1)
                , EBinOp
                    ( Add
                    , EVar "n"
                    , EApp (EVar "series", EBinOp (Sub, EVar "n", EConst (CInt 1))) ) ) )
        )
    ];
  [%expect {| series : int -> int |}]
;;

let%expect_test "let bind x f = f x" =
  print_prog_result
    [ ELet
        (false, PVar "bind", EFun (PVar "x", EFun (PVar "f", EApp (EVar "f", EVar "x"))))
    ];
  [%expect {| bind : 'a -> ('a -> 'c) -> 'c |}]
;;

let%expect_test "let x = 10" =
  print_prog_result [ ELet (false, PVar "x", EConst (CInt 10)) ];
  [%expect {| x : int |}]
;;

let%expect_test "let rec factorial n =\n\
                \  if n <= 1\n\
                \  then 1\n\
                \  else factorial (n - 1) * n"
  =
  print_prog_result
    [ ELet
        ( true
        , PVar "factorial"
        , EFun
            ( PVar "n"
            , EIf
                ( EBinOp (Leq, EVar "n", EConst (CInt 1))
                , EConst (CInt 1)
                , EBinOp
                    ( Mul
                    , EApp (EVar "factorial", EBinOp (Sub, EVar "n", EConst (CInt 1)))
                    , EVar "n" ) ) ) )
    ];
  [%expect {| factorial : int -> int |}]
;;

let%expect_test "let mult x = fun y -> x * y" =
  print_prog_result
    [ ELet
        ( false
        , PVar "mult"
        , EFun (PVar "x", EFun (PVar "y", EBinOp (Mul, EVar "x", EVar "y"))) )
    ];
  [%expect {| mult : int -> int -> int |}]
;;

let%expect_test "let a = 10 \n let incr x = x + 1 \n let incremented_a = a + 1 " =
  print_prog_result
    [ ELet (false, PVar "a", EConst (CInt 10))
    ; ELet (false, PVar "incr", EFun (PVar "x", EBinOp (Add, EVar "x", EConst (CInt 1))))
    ; ELet (false, PVar "incremented_a", EBinOp (Add, EVar "a", EConst (CInt 1)))
    ];
  [%expect {|
    a : int
    incr : int -> int
    incremented_a : int |}]
;;

let%expect_test "let a = 10\n\
                 let b = 11\n\
                 let c = a + b\n\
                 let c1 a b = if (a = b) then true else false \n\
                 let c2 a b = if (a > b) then true else false \n\
                 let compare l r c = c l r\n\
                 let k = compare a b c1 \n\
                 let k1 = compare a b c2"
  =
  print_prog_result
    [ ELet (false, PVar "a", EConst (CInt 10))
    ; ELet (false, PVar "b", EConst (CInt 11))
    ; ELet (false, PVar "c", EBinOp (Add, EVar "a", EVar "b"))
    ; ELet
        ( false
        , PVar "c1"
        , EFun
            ( PVar "a"
            , EFun
                ( PVar "b"
                , EIf
                    ( EBinOp (Eq, EVar "a", EVar "b")
                    , EConst (CBool true)
                    , EConst (CBool false) ) ) ) )
    ; ELet
        ( false
        , PVar "c2"
        , EFun
            ( PVar "a"
            , EFun
                ( PVar "b"
                , EIf
                    ( EBinOp (Gre, EVar "a", EVar "b")
                    , EConst (CBool true)
                    , EConst (CBool false) ) ) ) )
    ; ELet
        ( false
        , PVar "compare"
        , EFun
            ( PVar "l"
            , EFun (PVar "r", EFun (PVar "c", EApp (EApp (EVar "c", EVar "l"), EVar "r")))
            ) )
    ; ELet
        ( false
        , PVar "k"
        , EApp (EApp (EApp (EVar "compare", EVar "a"), EVar "b"), EVar "c1") )
    ; ELet
        ( false
        , PVar "k1"
        , EApp (EApp (EApp (EVar "compare", EVar "a"), EVar "b"), EVar "c2") )
    ];
  [%expect
    {|
    a : int
    b : int
    c : int
    c1 : 'b -> 'b -> bool
    c2 : 'd -> 'd -> bool
    compare : 'e -> 'f -> ('e -> 'f -> 'i) -> 'i
    k : bool
    k1 : bool |}]
;;

let%expect_test "let f x = x + true" =
  print_prog_result
    [ ELet (false, PVar "f", EFun (PVar "x", EBinOp (Add, EVar "x", EConst (CBool true))))
    ];
  [%expect {| unification failed on bool and int |}]
;;

let%expect_test "let a = 10 \n let incr x = x + 1 \n let incremented_a = k + 1 " =
  print_prog_result
    [ ELet (false, PVar "a", EConst (CInt 10))
    ; ELet (false, PVar "incr", EFun (PVar "x", EBinOp (Add, EVar "x", EConst (CInt 1))))
    ; ELet (false, PVar "incremented_a", EBinOp (Add, EVar "k", EConst (CInt 1)))
    ];
  [%expect {| Undefined variable 'k' |}]
;;

let%expect_test "let x,y = 5, 5" =
  print_prog_result
    [ ELet
        (false, PTuple [ PVar "x"; PVar "y" ], ETuple [ EConst (CInt 5); EConst (CInt 5) ])
    ];
  [%expect {| (x, y) : (int * int) |}]
;;

let%expect_test "let snd (x,y) = y" =
  print_prog_result
    [ ELet (false, PVar "snd", EFun (PTuple [ PVar "x"; PVar "y" ], EVar "y")) ];
  [%expect {| snd : ('a * 'b) -> 'b |}]
;;
