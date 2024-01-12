(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-3.0 *)

open Ast
open Base

let rec pat_helper set = function
  | PTuple xs -> List.fold xs ~init:set ~f:pat_helper
  | PVar x -> Set.add set x
  | _ -> set
;;

let free_vars expr =
  let rec efun_helper set = function
    | EFun (pat, e) ->
      efun_helper (Set.union set (pat_helper (Set.empty (module String)) pat)) e
    | _ -> set
  in
  let rec helper = function
    | EConst _ -> Set.empty (module String)
    | EVar x -> Set.singleton (module String) x
    | EBinOp (_, e1, e2) -> Set.union (helper e1) (helper e2)
    | EIf (e1, e2, e3) -> Set.union (Set.union (helper e1) (helper e2)) (helper e3)
    | EApp (e1, e2) -> Set.union (helper e1) (helper e2)
    | EFun (x, e) ->
      let pat_set = pat_helper (Set.empty (module String)) x in
      Set.diff (helper e) pat_set
    | ELetIn (b, x, e1, e2) ->
      let free1 = helper e1 in
      let p_set = pat_helper (Set.empty (module String)) x in
      let free1' = if b then Set.diff free1 p_set else free1 in
      let e1_pat = efun_helper (Set.empty (module String)) e1 in
      let free2 = Set.diff (helper e2) e1_pat in
      let free2' = Set.diff free2 p_set in
      Set.union free1' free2'
    | ETuple xs ->
      List.fold
        xs
        ~init:(Set.empty (module String))
        ~f:(fun acc x -> Set.union acc (helper x))
  in
  helper expr
;;

let closure_conversion global_env decl =
  let rec expr_closure local_env global_env = function
    | EConst x -> constr_econst x
    | EVar x as orig ->
      (match Map.find local_env x with
       | Some free ->
         let ids = List.map (Set.to_list free) ~f:(fun x -> constr_evar x) in
         constr_eapp orig ids
       | None -> orig)
    | EBinOp (op, e1, e2) ->
      let e1' = expr_closure local_env global_env e1 in
      let e2' = expr_closure local_env global_env e2 in
      constr_ebinop op e1' e2'
    | EIf (e1, e2, e3) ->
      let e1' = expr_closure local_env global_env e1 in
      let e2' = expr_closure local_env global_env e2 in
      let e3' = expr_closure local_env global_env e3 in
      constr_eif e1' e2' e3'
    | EApp (e1, e2) ->
      let e1' = expr_closure local_env global_env e1 in
      let e2' = expr_closure local_env global_env e2 in
      constr_eapp e1' [ e2' ]
    | EFun (x, _) as orig ->
      let s = free_vars orig in
      let s' = Set.diff s global_env in
      let e' = efun_helper local_env global_env orig in
      (match x with
       | PVar _ | PWild | PTuple _ ->
         let fun_fold =
           constr_efun (List.map (Set.to_list s') ~f:(fun x -> constr_pvar x)) e'
         in
         constr_eapp fun_fold (List.map (Set.to_list s') ~f:(fun x -> constr_evar x))
       | _ -> e')
    | ELetIn (b, PVar x, (EFun (_, _) as e1), e2) ->
      let free = free_vars e1 in
      let free' = Set.diff free global_env in
      let free' = if b then Set.remove free' x else free' in
      let e1' = efun_helper local_env global_env e1 in
      let e1_closure =
        constr_efun (List.map (Set.to_list free') ~f:(fun x -> constr_pvar x)) e1'
      in
      let local_env' = Map.set local_env ~key:x ~data:free' in
      let e2' = expr_closure local_env' (Set.add global_env x) e2 in
      constr_eletin b (constr_pvar x) e1_closure e2'
    | ELetIn (b, x, e1, e2) ->
      let e1' = expr_closure local_env global_env e1 in
      let e2' = expr_closure local_env global_env e2 in
      constr_eletin b x e1' e2'
    | ETuple xs ->
      let xs' = List.map xs ~f:(expr_closure local_env global_env) in
      constr_etuple xs'
  and efun_helper local_env global_env = function
    | EFun ((PVar _ as orig), e) ->
      let e' = efun_helper local_env global_env e in
      constr_efun [ orig ] e'
    | EFun (p, e) ->
      let e' = efun_helper local_env global_env e in
      constr_efun [ p ] e'
    | expr -> expr_closure local_env global_env expr
  in
  let decl_closure global_env = function
    | ELet (is_rec, p, e) ->
      let pat_set = pat_helper (Set.empty (module String)) p in
      (*If a pattern other than PVar occurs here, it cannot be recursive. This is checked at the stage of parsing and type checking *)
      let global_env' = if is_rec then Set.union global_env pat_set else global_env in
      let e' = efun_helper (Map.empty (module String)) global_env' e in
      constr_elet is_rec p e'
  in
  decl_closure global_env decl
;;

let prog_conversion program =
  let closured prog =
    List.fold
      ~init:([], Set.empty (module String))
      ~f:(fun (acc, global) ->
        function
        | ELet (_, p, _) as orig ->
          let pat_set = pat_helper (Set.empty (module String)) p in
          let e' = closure_conversion global orig in
          let global' = Set.union global pat_set in
          e' :: acc, global')
      prog
  in
  List.rev (fst @@ closured program)
;;

let print_expr_result decl =
  let buf = closure_conversion (Set.empty (module String)) decl in
  Stdlib.Format.printf "%s" (Ast.show_binding buf)
;;

let%expect_test _ =
  print_expr_result
    (ELet
       ( false
       , PVar "fac"
       , EFun
           ( PVar "n"
           , ELetIn
               ( true
               , PVar "fack"
               , EFun
                   ( PVar "n"
                   , EFun
                       ( PVar "k"
                       , EIf
                           ( EBinOp (Leq, EVar "n", EConst (CInt 1))
                           , EApp (EVar "k", EConst (CInt 1))
                           , EApp
                               ( EApp
                                   (EVar "fack", EBinOp (Sub, EVar "n", EConst (CInt 1)))
                               , EFun
                                   ( PVar "m"
                                   , EApp (EVar "k", EBinOp (Mul, EVar "m", EVar "n")) )
                               ) ) ) )
               , EApp (EApp (EVar "fack", EVar "n"), EFun (PVar "x", EVar "x")) ) ) ));
  [%expect
    {|
      (ELet (false, (PVar "fac"),
         (EFun ((PVar "n"),
            (ELetIn (true, (PVar "fack"),
               (EFun ((PVar "n"),
                  (EFun ((PVar "k"),
                     (EIf ((EBinOp (Leq, (EVar "n"), (EConst (CInt 1)))),
                        (EApp ((EVar "k"), (EConst (CInt 1)))),
                        (EApp (
                           (EApp ((EVar "fack"),
                              (EBinOp (Sub, (EVar "n"), (EConst (CInt 1)))))),
                           (EApp (
                              (EApp (
                                 (EFun ((PVar "k"),
                                    (EFun ((PVar "n"),
                                       (EFun ((PVar "m"),
                                          (EApp ((EVar "k"),
                                             (EBinOp (Mul, (EVar "m"), (EVar "n")))
                                             ))
                                          ))
                                       ))
                                    )),
                                 (EVar "k"))),
                              (EVar "n")))
                           ))
                        ))
                     ))
                  )),
               (EApp ((EApp ((EVar "fack"), (EVar "n"))),
                  (EFun ((PVar "x"), (EVar "x")))))
               ))
            ))
         ))
         |}]
;;
