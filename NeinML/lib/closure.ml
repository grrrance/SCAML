(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Ast
open Typing

let empty = Base.Set.empty (module Base.String)
let singleton = Base.Set.singleton (module Base.String)
let of_list = Base.Set.of_list (module Base.String)
let empty_map = Base.Map.empty (module Base.String)

type name_set = (string, Base.String.comparator_witness) Base.Set.t
type typ_map = (string, ty, Base.String.comparator_witness) Base.Map.t

type free_vars_map_type =
  (string, typ_map * ty, Base.String.comparator_witness) Base.Map.t

module IntState = struct
  include Monad.State (struct
    type t = int * name_set
  end)

  let ( let* ) = ( >>= )

  let incrementCounter =
    let* counter, scope = get in
    let* () = put (counter + 1, scope) in
    return counter
  ;;

  let fresh name =
    let* num = incrementCounter in
    return @@ String.concat "" [ "__neinml_uni"; string_of_int num; name ]
  ;;

  let get_scope =
    let* _, scope = get in
    return scope
  ;;

  let put_scope scope =
    let* counter, _ = get in
    put (counter, scope)
  ;;
end

module ListM = Monad.ListM (IntState)

let unique_names stmts =
  let open IntState in
  let process_name mapping name =
    let* scope = get_scope in
    if Base.Set.mem scope name
    then
      let* new_name = fresh name in
      let mapping = Base.Map.set mapping ~key:name ~data:new_name in
      return (mapping, new_name)
    else
      let* () = Base.Set.add scope name |> put_scope in
      return (mapping, name)
  in
  let rec expr_helper mapping = function
    | BinOp (op_left, op_right, op, meta) ->
      let* op_left = expr_helper mapping op_left in
      let* op_right = expr_helper mapping op_right in
      return @@ BinOp (op_left, op_right, op, meta)
    | IfThenElse (cond, thn, els, meta) ->
      let* cond = expr_helper mapping cond in
      let* thn = expr_helper mapping thn in
      let* els = expr_helper mapping els in
      return @@ IfThenElse (cond, thn, els, meta)
    | Apply (f, x, meta) ->
      let* f = expr_helper mapping f in
      let* x = expr_helper mapping x in
      return @@ Apply (f, x, meta)
    | Value _ as v -> return v
    | Variable (name, meta) ->
      let new_name = Base.Map.find mapping name |> Base.Option.value ~default:name in
      return @@ Variable (new_name, meta)
    | Func (name, body, meta) ->
      let* mapping, new_name = process_name mapping name in
      let* body = expr_helper mapping body in
      return @@ Func (new_name, body, meta)
    | LetIn (name, def, body, meta) ->
      let* new_mapping, new_name = process_name mapping name in
      let* new_def = expr_helper mapping def in
      let* new_body = expr_helper new_mapping body in
      return @@ LetIn (new_name, new_def, new_body, meta)
    | RecLetIn (name, def, body, meta) ->
      let* mapping, new_name = process_name mapping name in
      let* new_def = expr_helper mapping def in
      let* new_body = expr_helper mapping body in
      return @@ RecLetIn (new_name, new_def, new_body, meta)
  in
  let stmt_helper mapping = function
    | Define (name, body, meta) ->
      let* new_body = expr_helper mapping body in
      let* mapping, new_name = process_name mapping name in
      return (Define (new_name, new_body, meta), mapping)
    | RecDefine (name, body, meta) ->
      let* mapping, new_name = process_name mapping name in
      let* new_body = expr_helper mapping body in
      return (RecDefine (new_name, new_body, meta), mapping)
  in
  let rename_stmt (mapping, stmts) stmt =
    let* stmt, mapping = stmt_helper mapping stmt in
    return (mapping, stmt :: stmts)
  in
  ListM.fold_left rename_stmt (empty_map, []) stmts
  |> IntState.eval (0, empty)
  |> snd
  |> List.rev
;;

let get_arg_typ = function
  | Arrow (arg_typ, _) -> arg_typ
  | other -> other
;;

let get_args_body (func : ty Ast.expression) =
  let rec func_helper acc = function
    | Func (arg, inner_func, typ) ->
      func_helper ((arg, get_arg_typ typ) :: acc) inner_func
    | _ as func_body -> acc, func_body
  in
  let args, body = func_helper [] func in
  args, body
;;

let remove_keys map keys =
  let map_keys = Base.Map.keys map in
  Base.List.fold map_keys ~init:map ~f:(fun fold_map key ->
    match Base.Set.mem keys key with
    | true -> Base.Map.remove fold_map key
    | false -> fold_map)
;;

let rec get_unbound_vars (acc : typ_map) = function
  | Variable (name, typ) ->
    Base.Map.update acc name ~f:(function
      | None -> typ
      | Some _ -> typ)
  | Apply (func, arg, _) ->
    let acc_with_func_vars = get_unbound_vars acc func in
    get_unbound_vars acc_with_func_vars arg
  | Func (_, _, _) as func ->
    let args, body = get_args_body func in
    let body_vars = get_unbound_vars acc body in
    let args_set = of_list (Base.List.map args ~f:fst) in
    remove_keys body_vars args_set
  | LetIn (name, definition, body, _) | RecLetIn (name, definition, body, _) ->
    let acc1 = get_unbound_vars acc definition in
    let acc2 = Base.Map.remove acc1 name in
    get_unbound_vars acc2 body
  | Value _ -> acc
  | BinOp (expr1, expr2, _, _) ->
    let acc1 = get_unbound_vars acc expr1 in
    get_unbound_vars acc1 expr2
  | IfThenElse (condition, expr1, expr2, _) ->
    let acc1 = get_unbound_vars acc condition in
    let acc2 = get_unbound_vars acc1 expr1 in
    get_unbound_vars acc2 expr2
;;

let get_define_constructor = function
  | Define (_, _, _) -> cdef
  | RecDefine (_, _, _) -> crecdef
;;

let delete_arrow = function
  | Arrow (_, inner_type) -> inner_type
  | another_case -> another_case
;;

type ancestor_type =
  | Func
  | Apply
  | NotFuncAndApply

let rec closure_conversion
  (free_vars_map : free_vars_map_type)
  (global_scope : name_set)
  (ancestor : ancestor_type)
  (expr : ty expression)
  : ty expression
  =
  match expr with
  | LetIn (name, definition, body, _) | RecLetIn (name, definition, body, _) ->
    (match get_meta definition with
     | Prim _ as let_typ ->
       let new_map = Base.Map.set free_vars_map ~key:name ~data:(empty_map, let_typ) in
       let body_conversion =
         closure_conversion new_map global_scope NotFuncAndApply body
       in
       let body_type = get_meta body_conversion in
       cletin name definition body_conversion body_type
     | let_typ ->
       let args, def_body = get_args_body definition in
       let all_def_vars = get_unbound_vars empty_map def_body in
       let free_vars = remove_keys all_def_vars (of_list (Base.List.map args ~f:fst)) in
       let free_vars = remove_keys free_vars global_scope in
       let free_vars = remove_keys free_vars (singleton name) in
       let new_func_type =
         Base.List.fold
           (Base.List.rev (Base.Map.keys free_vars))
           ~init:let_typ
           ~f:(fun acc arg -> Arrow (Base.Map.find_exn free_vars arg, acc))
       in
       let new_map =
         Base.Map.set free_vars_map ~key:name ~data:(free_vars, new_func_type)
       in
       let def_conversion =
         closure_conversion new_map global_scope NotFuncAndApply def_body
       in
       let def_conversion_with_args =
         Base.List.fold args ~init:def_conversion ~f:(fun acc arg ->
           let arg_name, arg_typ = arg in
           Func (arg_name, acc, Arrow (arg_typ, get_meta acc)))
       in
       let def_conversion_with_free_vars =
         Base.List.fold
           (Base.List.rev (Base.Map.keys free_vars))
           ~init:def_conversion_with_args
           ~f:(fun acc arg ->
             Func (arg, acc, Arrow (Base.Map.find_exn free_vars arg, get_meta acc)))
       in
       let new_map =
         Base.Map.update new_map name ~f:(fun _ ->
           free_vars, get_meta def_conversion_with_free_vars)
       in
       let body_conversion =
         closure_conversion new_map global_scope NotFuncAndApply body
       in
       let body_type = get_meta body_conversion in
       cletin name def_conversion_with_free_vars body_conversion body_type)
  | Variable (name, typ) ->
    (match Base.Map.find free_vars_map name with
     | Some (new_args, new_typ) ->
       let make_application =
         Base.Map.fold
           new_args
           ~init:(Variable (name, new_typ))
           ~f:(fun ~key ~data acc ->
             Apply (acc, Variable (key, data), delete_arrow (get_meta acc)))
       in
       make_application
     | None -> Variable (name, typ))
  | BinOp (expr1, expr2, op, _) as binop ->
    let conversed_left =
      closure_conversion free_vars_map global_scope NotFuncAndApply expr1
    in
    let conversed_right =
      closure_conversion free_vars_map global_scope NotFuncAndApply expr2
    in
    cbinop conversed_left conversed_right op (get_meta binop)
  | Apply (inner_func, last_arg, apply_typ) ->
    let conversed_func = closure_conversion free_vars_map global_scope Apply inner_func in
    let conversed_arg =
      closure_conversion free_vars_map global_scope NotFuncAndApply last_arg
    in
    let new_typ =
      match delete_arrow (get_meta conversed_func) with
      | Ty_var _ -> apply_typ
      | normal_typ -> normal_typ
    in
    capply conversed_func conversed_arg new_typ
  | Value _ as value -> value
  | IfThenElse (cond, expr1, expr2, _) as if_stmt ->
    let conversed_cond =
      closure_conversion free_vars_map global_scope NotFuncAndApply cond
    in
    let conversed_expr1 =
      closure_conversion free_vars_map global_scope NotFuncAndApply expr1
    in
    let conversed_expr2 =
      closure_conversion free_vars_map global_scope NotFuncAndApply expr2
    in
    cifthenelse conversed_cond conversed_expr1 conversed_expr2 (get_meta if_stmt)
  | Func (arg_name, inner_func, func_typ) as new_func ->
    (match ancestor with
     | NotFuncAndApply | Apply ->
       let conversed_func = closure_conversion free_vars_map global_scope Func new_func in
       let lambda_free_vars = get_unbound_vars empty_map conversed_func in
       let func_with_new_args =
         Base.List.fold
           (Base.List.rev (Base.Map.keys lambda_free_vars))
           ~init:conversed_func
           ~f:(fun acc arg ->
             Func (arg, acc, Arrow (Base.Map.find_exn lambda_free_vars arg, get_meta acc)))
       in
       let apply_new_args =
         Base.Map.fold lambda_free_vars ~init:func_with_new_args ~f:(fun ~key ~data acc ->
           Apply (acc, Variable (key, data), delete_arrow (get_meta acc)))
       in
       apply_new_args
     | Func ->
       let conversed_inner_func =
         closure_conversion free_vars_map global_scope Func inner_func
       in
       let arg_typ = get_arg_typ func_typ in
       Func
         (arg_name, conversed_inner_func, Arrow (arg_typ, get_meta conversed_inner_func)))
;;

let rec converse_stms (global_scope : name_set) (acc : ty statements_list) = function
  | stmt :: tail ->
    (match stmt with
     | Define (name, body, _) | RecDefine (name, body, _) ->
       let args, def_body = get_args_body body in
       let new_scope = Base.Set.add global_scope name in
       let conversed_body =
         closure_conversion empty_map new_scope NotFuncAndApply def_body
       in
       let conversed_func =
         Base.List.fold args ~init:conversed_body ~f:(fun acc arg ->
           let arg_name, arg_typ = arg in
           Func (arg_name, acc, Arrow (arg_typ, get_meta acc)))
       in
       let constructor = get_define_constructor stmt in
       let new_stmt = constructor name conversed_func (get_meta conversed_func) in
       converse_stms new_scope (new_stmt :: acc) tail)
  | _ -> List.rev acc
;;

let closure_converse stmts_list = converse_stms empty [] stmts_list
