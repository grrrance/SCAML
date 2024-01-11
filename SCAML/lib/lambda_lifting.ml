(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-3.0 *)

open Ast
open Llast
open Counter
open Base
open IState
open IState.Syntax

let rec get_args acc = function
  | EFun (p, e) -> get_args (p :: acc) e
  | e -> List.rev acc, e
;;

 let rec pat_helper set = function
    | PTuple xs -> List.fold xs ~init:set ~f:pat_helper
    | PVar x -> Set.add set x
    | _ -> set
let rec get_global_scope prog global =
  match prog with
  | [] -> global
  | ELet (_, pat, _) :: tl -> (Set.union global (pat_helper (Set.empty (module String)) pat)) |> get_global_scope tl
;;

let rec gen_fresh_id global =
  let* fresh_id = fresh_name_int in
  let new_id = "id_" ^ Int.to_string fresh_id in
  let is_in = Set.mem global new_id in
  if is_in then gen_fresh_id global else return new_id
;;

let pattern_m_helper inner pat_l global =
  let rec tuple_helper inner pat_l new_id =
    List.fold_left
      ~f:(fun acc x ->
        let* acc, count = acc in
        match x with
        | PVar id -> return (LLLetIn (id, LLGetFromTuple (new_id, count), acc), count + 1)
        | PTuple xs ->
          let* new_id' = gen_fresh_id global in
          let* acc, _ = tuple_helper inner xs new_id' in
          return (LLLetIn (new_id', LLGetFromTuple (new_id, count), acc), count + 1)
        | _ -> return (acc, count + 1))
      ~init:(return (inner, 0))
      pat_l
        in
        List.fold_right
          ~f:(fun x acc ->
            let* acc, args = acc in
            match x with
            | PTuple xs ->(
              let* new_id = gen_fresh_id global in
              let* acc, _ = tuple_helper acc xs new_id in
              return (acc, new_id :: args)
            )
            | PVar id -> return (acc, id :: args)
            | PConst _ -> return (acc, args)
            | PWild -> return (acc,  args))
          ~init:(return (inner, []))
          pat_l

;;
(*Same, but for top level pattern matchings*)
let pattern_m_let_helper pat global =
  let rec tuple_helper pat_l new_id =
    List.fold_left
      ~f:(fun acc x ->
        let* acc, count = acc in
        match x with
        | PVar id -> return ((LLLet (false, id, [], LLGetFromTuple (new_id, count)) :: acc), count + 1)
        | PTuple xs ->
          let* new_id' = gen_fresh_id global in
          let* acc, _ = tuple_helper xs new_id' in
          return ((LLLet (false, new_id', [], LLGetFromTuple (new_id, count)) :: acc), count + 1)
        | _ -> return (acc, count + 1))
      ~init:(return ([], 0))
      pat_l
        in
      match pat with
      | PTuple xs ->(
        let* new_id = gen_fresh_id global in
        let* decl_l, _ = tuple_helper xs new_id in
        return (decl_l, PVar new_id)
      )
      | PVar id -> return ([], PVar id)
      | PConst c -> return ([], PConst c)
      | PWild -> return ([], PWild)
;;

let prog_lift prog =
  let rec lift_expr env ll_list global = function
    | EConst c ->
      (match c with
       | CInt i -> return (LLConst (CInt i), ll_list)
       | CBool b -> return (LLConst (CBool b), ll_list)
       | CUnit -> return (LLConst CUnit, ll_list))
    | EVar x ->
      (match Map.find env x with
       | Some id -> return (LLVar id, ll_list)
       | None -> return (LLVar x, ll_list))
    | EBinOp (op, e1, e2) ->
      let* l1, ll_list = lift_expr env ll_list global e1 in
      let* l2, ll_list = lift_expr env ll_list global e2 in
      return (LLBinOp (op, l1, l2), ll_list)
    | EIf (e1, e2, e3) ->
      let* l1, ll_list = lift_expr env ll_list global e1 in
      let* l2, ll_list = lift_expr env ll_list global e2 in
      let* l3, ll_list = lift_expr env ll_list global e3 in
      return (LLIf (l1, l2, l3), ll_list)
    | EApp (e1, e2) ->
      let* l1, ll_list = lift_expr env ll_list global e1 in
      let* l2, ll_list = lift_expr env ll_list global e2 in
      return (LLApp (l1, l2), ll_list)
    | ELetIn (is_rec, PVar id, (EFun (_, _) as e1), e2) ->
      let args, exp = get_args [] e1 in
      let* new_id = gen_fresh_id global in
      let new_env = Map.set env ~key:id ~data:new_id in
      let* l1, ll_list =
        if is_rec
        then lift_expr new_env ll_list global exp
        else lift_expr env ll_list global exp
      in
      let* l1', args = pattern_m_helper l1 args global in
      let ll_list = LLLet (is_rec, new_id, args, l1') :: ll_list in
      let* l2, ll_list = lift_expr new_env ll_list global e2 in
      return (l2, ll_list)
    | ELetIn (_, pat, e1, e2) ->
      let* l1, ll_list = lift_expr env ll_list global e1 in
      let* l2, ll_list = lift_expr env ll_list global e2 in
      let* l2', args = pattern_m_helper l2 [pat] global in
      (match args with
      | [id] -> return (LLLetIn (id, l1, l2'), ll_list)
      | _ -> return (l2, ll_list))
    | EFun (_, _) as e ->
      let args, exp = get_args [] e in
      let* new_id = gen_fresh_id global in
      let* l1, ll_list = lift_expr (Map.empty (module String)) ll_list global exp in
      let* l1', args = pattern_m_helper l1 args global in
      let ll_list = LLLet (false, new_id, args, l1') :: ll_list in
      return (LLVar new_id, ll_list)
    | ETuple xs ->
      let* tuples, ll_list =
        List.fold_left
          ~f:(fun acc x ->
            let* acc, ll_list = acc in
            let* l, ll_list = lift_expr env ll_list global x in
            return @@ (l :: acc, ll_list))
          ~init:(return ([], ll_list))
          xs
      in
      return (LLTuple (List.rev tuples), ll_list)
  in
  let decl_ll global = function
    | ELet (is_rec, PVar id , e) ->
      let p, expr = get_args [] e in
      let* l1, ll_list = lift_expr (Map.empty (module String)) [] global expr in
      let* l1, p = pattern_m_helper l1 p global in
      let ll_list = LLLet (is_rec, id, p, l1) :: ll_list in
      return ll_list
    | ELet (_, (PTuple _ as pat), e) ->
      let* l1, ll_list = lift_expr (Map.empty (module String)) [] global e in
      let* decl_l, pat = pattern_m_let_helper pat global in
      let decl_l =
        (match pat with
        | PVar id -> decl_l @ [LLLet (false, id, [], l1) ]
        | _ -> decl_l)
      in
      return (decl_l @ ll_list)
    | ELet (_, _, _) -> return []

  in
  let prog_ll prog =
    let global = get_global_scope prog (Set.empty (module String)) in
    let* ll_list =
      List.fold_left
        ~f:(fun acc x ->
          let* ll_list = decl_ll global x in
          let* acc = acc in
          return (acc @ List.rev ll_list))
        ~init:(return [])
        prog
    in
    return ll_list
  in
  prog_ll prog
;;

let run_ll prog = snd @@ IState.runState ~init:0 (prog_lift prog)
