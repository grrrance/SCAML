(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

(* Original code was taken from
   https://gitlab.com/Kakadu/fp2020course-materials/-/blob/master/code/miniml *)

open Base
open Typing
module Format = Stdlib.Format (* silencing a warning *)

type error =
  [ `Occurs_check
  | `No_variable of string
  | `Unification_failed of ty * ty
  ]

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
      :  (int, 'a, Int.comparator_witness) Map.t
      -> init:'b t
      -> f:(int -> 'a -> 'b -> 'b t)
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
        f key data acc)
    ;;
  end

  let fresh : int t = fun last -> last + 1, Result.Ok last
  let run m = snd (m 0)
end

type fresh = int

module Type = struct
  type t = ty

  let rec occurs_in v = function
    | Ty_var b -> b = v
    | Arrow (l, r) -> occurs_in v l || occurs_in v r
    | Prim _ -> false
  ;;

  let free_vars =
    let rec helper acc = function
      | Ty_var b -> VarSet.add b acc
      | Arrow (l, r) -> helper (helper acc l) r
      | Prim _ -> acc
    in
    helper VarSet.empty
  ;;
end

module Subst : sig
  type t

  val empty : t
  val singleton : fresh -> ty -> t R.t
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
    let* key, value = mapping k v in
    return (Map.update empty key ~f:(fun _ -> value))
  ;;

  let remove xs k = Map.remove xs k

  let apply s =
    let rec helper = function
      | Ty_var b as full_expr ->
        (match Map.find_exn s b with
         | exception Not_found_s _ -> full_expr
         | x -> x)
      | Arrow (l, r) -> Arrow (helper l, helper r)
      | other -> other
    in
    helper
  ;;

  let rec unify l r =
    match l, r with
    | Prim pl, Prim pr ->
      if equal_ground pl pr then return empty else fail (`Unification_failed (l, r))
    | Ty_var a, Ty_var b when Int.equal a b -> return empty
    | Ty_var b, t | t, Ty_var b -> singleton b t
    | Arrow (l1, r1), Arrow (l2, r2) ->
      let* subs1 = unify l1 l2 in
      let* subs2 = unify (apply subs1 r1) (apply subs1 r2) in
      compose subs1 subs2
    | _ -> fail (`Unification_failed (l, r))

  and extend k v s =
    match Map.find s k with
    | None ->
      let v = apply s v in
      let* s2 = singleton k v in
      RMap.fold_left s ~init:(return s2) ~f:(fun k v acc ->
        let v = apply s2 v in
        let* k, v = mapping k v in
        return (Map.update acc k ~f:(fun _ -> v)))
    | Some v2 ->
      let* s2 = unify v v2 in
      compose s s2

  and compose s1 s2 = RMap.fold_left s2 ~init:(return s1) ~f:extend

  let compose_all ss =
    List.fold_left ss ~init:(return empty) ~f:(fun acc subst ->
      let* acc = acc in
      compose acc subst)
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
  type t = (Ast.name, scheme, String.comparator_witness) Map.t

  let extend e h = Base.Map.update e (fst h) ~f:(fun _ -> snd h)
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
let fresh_var = fresh >>| fun n -> Ty_var n

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

let lookup_env e xs =
  match Map.find_exn xs e with
  | (exception Stdlib.Not_found) | (exception Not_found_s _) -> fail (`No_variable e)
  | scheme ->
    let* ans = instantiate scheme in
    return (Subst.empty, ans)
;;

let infer_value = function
  | Ast.VBool _ -> bool_typ
  | Ast.VInt _ -> int_typ
;;

let infer_binop op =
  let open Ast in
  match op with
  | Add | Sub | Mul | Div | Mod -> return (int_typ @-> int_typ @-> int_typ)
  | And | Or -> return (bool_typ @-> bool_typ @-> bool_typ)
  | Equal | NotEqual ->
    let* tvar = fresh_var in
    return (tvar @-> tvar @-> bool_typ)
  | Less | LessOrEq | More | MoreOrEq -> return (int_typ @-> int_typ @-> bool_typ)
;;

let infer_stmt =
  let rec (helper
            : TypeEnv.t -> unit Ast.expression -> (Subst.t * ty * ty Ast.expression) R.t)
    =
   fun env -> function
    | Ast.Value (value, ()) ->
      let typ = infer_value value in
      return (Subst.empty, typ, Ast.Value (value, typ))
    | Ast.Variable (x, ()) ->
      let* subst, typ = lookup_env x env in
      return (subst, typ, Ast.Variable (x, typ))
    | Ast.BinOp (left, right, op, ()) ->
      let* typ_op = infer_binop op in
      let* subst_left, typ_left, typed_left = helper env left in
      let* subst_right, typ_right, typed_right = helper env right in
      let* typ = fresh_var in
      let* subst = unify (typ_left @-> typ_right @-> typ) typ_op in
      let* final_subst = Subst.compose_all [ subst; subst_left; subst_right ] in
      let typ = Subst.apply final_subst typ in
      let typed_ast = Ast.BinOp (typed_left, typed_right, op, typ) in
      return (final_subst, typ, typed_ast)
    | Ast.Apply (left, right, ()) ->
      let* s1, t1, typed_left = helper env left in
      let* s2, t2, typed_right = helper (TypeEnv.apply s1 env) right in
      let* tv = fresh_var in
      let* s3 = unify (Subst.apply s2 t1) (Arrow (t2, tv)) in
      let trez = Subst.apply s3 tv in
      let* final_subst = Subst.compose_all [ s3; s2; s1 ] in
      let new_ast = Ast.Apply (typed_left, typed_right, trez) in
      return (final_subst, trez, new_ast)
    | Ast.IfThenElse (condition, true_expr, else_expr, ()) ->
      let* subst_cond, typ_cond, typed_condition = helper env condition in
      let* subst_true_expr, typ_true_expr, typed_true_expr = helper env true_expr in
      let* subst_false_expr, typ_false_expr, typed_else_expr = helper env else_expr in
      let* s1 = unify typ_cond bool_typ in
      let* s2 = unify typ_true_expr typ_false_expr in
      let* final_subst =
        Subst.compose_all [ subst_cond; subst_true_expr; subst_false_expr; s1; s2 ]
      in
      let typ = Subst.apply final_subst typ_true_expr in
      let new_ast =
        Ast.IfThenElse (typed_condition, typed_true_expr, typed_else_expr, typ)
      in
      return (final_subst, typ, new_ast)
    | Ast.LetIn (name, inner_def, outer_expr, ()) ->
      let* subst_inner_def, typ_inner_def, typed_inner_def = helper env inner_def in
      let env1 = TypeEnv.apply subst_inner_def env in
      let t1 = generalize env1 typ_inner_def in
      let* s1, t2, typed_outer_expr =
        helper (TypeEnv.extend env1 (name, t1)) outer_expr
      in
      let* final_subst = Subst.compose subst_inner_def s1 in
      let typ = Subst.apply final_subst t2 in
      let new_ast = Ast.LetIn (name, typed_inner_def, typed_outer_expr, typ) in
      return (final_subst, typ, new_ast)
    | Ast.RecLetIn (name, inner_def, outer_expr, ()) ->
      let* tv = fresh_var in
      let env = TypeEnv.extend env (name, S (VarSet.empty, tv)) in
      let* subst_inner, typ_inner, typed_inner = helper env inner_def in
      let* s1 = unify (Subst.apply subst_inner tv) typ_inner in
      let* s2 = Subst.compose subst_inner s1 in
      let env = TypeEnv.apply s2 env in
      let t2 = generalize env (Subst.apply s2 tv) in
      let* s3, t3, typed_outer =
        helper TypeEnv.(extend (apply s2 env) (name, t2)) outer_expr
      in
      let* final_subst = Subst.compose s2 s3 in
      let typ = Subst.apply final_subst t3 in
      let new_ast = Ast.RecLetIn (name, typed_inner, typed_outer, typ) in
      return (final_subst, typ, new_ast)
    | Ast.Func (param_name, def, ()) ->
      let* tv = fresh_var in
      let env = TypeEnv.extend env (param_name, S (VarSet.empty, tv)) in
      let* s1, t1, typed_def = helper env def in
      let trez = Arrow (Subst.apply s1 tv, t1) in
      let new_ast = Ast.Func (param_name, typed_def, trez) in
      return (s1, trez, new_ast)
  and statement_helper
    : TypeEnv.t -> unit Ast.statement -> (Subst.t * ty * ty Ast.statement) R.t
    =
   fun env -> function
    | Ast.Define (name, function_body, ()) ->
      let* subst, typ, typed_body = helper env function_body in
      return (subst, typ, Ast.Define (name, typed_body, typ))
    | Ast.RecDefine (name, function_body, ()) ->
      let* tv = fresh_var in
      let env = TypeEnv.extend env (name, S (VarSet.empty, tv)) in
      let* s1, t, typed_body = helper env function_body in
      let* s2 = unify (Subst.apply s1 tv) (Subst.apply s1 t) in
      let* final_subst = Subst.compose s1 s2 in
      let typ = Subst.apply final_subst tv in
      let new_ast = Ast.RecDefine (name, typed_body, typ) in
      return (final_subst, typ, new_ast)
  in
  statement_helper
;;

let update_types subst stmt =
  let rec expr_helper = function
    | Ast.BinOp (op1, op2, op, t) ->
      Ast.BinOp (expr_helper op1, expr_helper op2, op, Subst.apply subst t)
    | Ast.LetIn (name, decl, expr, t) ->
      Ast.LetIn (name, expr_helper decl, expr_helper expr, Subst.apply subst t)
    | Ast.RecLetIn (name, decl, expr, t) ->
      Ast.RecLetIn (name, expr_helper decl, expr_helper expr, Subst.apply subst t)
    | Ast.IfThenElse (cond, thn, els, t) ->
      Ast.IfThenElse
        (expr_helper cond, expr_helper thn, expr_helper els, Subst.apply subst t)
    | Ast.Func (name, body, t) -> Ast.Func (name, expr_helper body, Subst.apply subst t)
    | Ast.Apply (f, arg, t) ->
      Ast.Apply (expr_helper f, expr_helper arg, Subst.apply subst t)
    | Ast.Variable (name, t) -> Ast.Variable (name, Subst.apply subst t)
    | Ast.Value (value, t) -> Ast.Value (value, Subst.apply subst t)
  in
  match stmt with
  | Ast.Define (name, expr, t) -> Ast.Define (name, expr_helper expr, Subst.apply subst t)
  | Ast.RecDefine (name, expr, t) ->
    Ast.RecDefine (name, expr_helper expr, Subst.apply subst t)
;;

let infer_statements (stms : unit Ast.statements_list)
  : (ty list * ty Ast.statements_list) t
  =
  let infer_list_elem env_stmt_ast_pair = function
    | (Ast.Define (name, _, ()) | Ast.RecDefine (name, _, ())) as new_stmt ->
      let* env, stms_types, ast_list = env_stmt_ast_pair in
      let* subst, ty, typed_stmt = infer_stmt env new_stmt in
      let typed_stmt = update_types subst typed_stmt in
      let scheme = generalize env ty in
      let env = TypeEnv.extend env (name, scheme) in
      return (env, ty :: stms_types, typed_stmt :: ast_list)
  in
  let env = List.fold stdlib ~init:TypeEnv.empty ~f:TypeEnv.extend in
  let* _, second, third =
    List.fold ~init:(return (env, [], [])) ~f:infer_list_elem stms
  in
  return (List.rev second, List.rev third)
;;

let w_stms_list e = run (infer_statements e)

let run_stms_list stms_list =
  match w_stms_list stms_list with
  | Result.Error err -> print_typ_error err
  | Ok subst -> List.iter (fst subst) ~f:print_typ
;;

let parse_and_infer text =
  match Parser.parse text with
  | Result.Ok ast -> run_stms_list ast
  | Result.Error (`ParsingError er) ->
    Format.fprintf Format.std_formatter "Parsing error - %S" er
;;
