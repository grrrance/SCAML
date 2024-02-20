(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type imm_expr =
  | ImmVar of Ast.name * Typing.ty
  | ImmInt of int
  | ImmBool of bool
[@@deriving show { with_path = false }]

type cexpr =
  | CBinOp of imm_expr * imm_expr * Ast.binop * Typing.ty
  | CApply of Ast.name * imm_expr * imm_expr list * Typing.ty
  | CIfThenElse of
      imm_expr
      * (cexpr Lambda_lifting.var_decl list * cexpr)
      * (cexpr Lambda_lifting.var_decl list * cexpr)
      * Typing.ty
  | CImm of imm_expr
[@@deriving show { with_path = false }]

module AnfState = struct
  include Monad.State (struct
    type t = int * cexpr Lambda_lifting.var_decl list
  end)

  let ( let* ) = ( >>= )

  let get_counter =
    let* counter, _ = get in
    return counter
  ;;

  let modify_counter f =
    let* counter, lifted = get in
    put (f counter, lifted)
  ;;

  let fresh =
    let* counter = get_counter in
    let* () = modify_counter succ in
    return @@ String.concat "_" [ "__neinml"; "anf"; string_of_int counter ]
  ;;
end

module ListM = Monad.ListM (AnfState)
open AnfState

let rec expr_to_cexpr =
  let open Lambda_lifting in
  let ast_value_to_imm_expr = function
    | Ast.VInt value -> ImmInt value
    | Ast.VBool value -> ImmBool value
  in
  function
  | Variable (name, t) -> return (ImmVar (name, t), [])
  | Value (value, _) -> return (ast_value_to_imm_expr value, [])
  | BinOp (left, right, op, op_typ) ->
    let* new_varname = fresh in
    let new_var = ImmVar (new_varname, op_typ) in
    let* new_left_var, left_var_decls = expr_to_cexpr left in
    let* new_right_var, right_var_decls = expr_to_cexpr right in
    let new_expr = CBinOp (new_left_var, new_right_var, op, op_typ) in
    let new_var_decl = new_varname, new_expr, op_typ in
    return (new_var, (new_var_decl :: left_var_decls) @ right_var_decls)
  | Apply (func, first_arg, arg_list, app_typ) ->
    let* new_varname = fresh in
    let new_var = ImmVar (new_varname, app_typ) in
    let* new_first_arg_var, first_arg_var_decls = expr_to_cexpr first_arg in
    let* new_args = ListM.map expr_to_cexpr arg_list in
    let* new_func_name, func_var_decls =
      match func with
      | Variable (name, _) ->
        return (name, [ "name", CImm (ImmInt 1), Typing.Prim Typing.TBool ])
      | _ ->
        let* new_func_var, func_var_decls = expr_to_cexpr func in
        let* new_varname = fresh in
        let new_var_decl = new_varname, CImm new_func_var, get_meta func in
        return (new_varname, new_var_decl :: func_var_decls)
    in
    let func_var_decls =
      match func_var_decls with
      | [ ("name", CImm (ImmInt 1), Typing.Prim Typing.TBool) ] -> []
      | _ -> func_var_decls
    in
    let new_args_var_decls = Base.List.concat_map ~f:snd new_args in
    let new_args_vars = Base.List.map ~f:fst new_args in
    let new_expr = CApply (new_func_name, new_first_arg_var, new_args_vars, app_typ) in
    let new_var_decl = new_varname, new_expr, app_typ in
    return
      ( new_var
      , (new_var_decl :: func_var_decls) @ first_arg_var_decls @ new_args_var_decls )
  | IfThenElse (cond, true_expr, false_expr, if_typ) ->
    let* new_varname = fresh in
    let new_var = ImmVar (new_varname, if_typ) in
    let* new_cond_var, cond_var_decls = expr_to_cexpr cond in
    let* new_true_var, true_var_decls = expr_to_cexpr true_expr in
    let true_var = CImm new_true_var in
    let* new_false_var, false_var_decls = expr_to_cexpr false_expr in
    let false_var = CImm new_false_var in
    let new_expr =
      CIfThenElse
        ( new_cond_var
        , (List.rev true_var_decls, true_var)
        , (List.rev false_var_decls, false_var)
        , if_typ )
    in
    let new_var_decl = new_varname, new_expr, if_typ in
    return (new_var, new_var_decl :: cond_var_decls)
;;

let make_anf stmts =
  let rec anf_helper acc =
    let open Lambda_lifting in
    function
    | stmt :: stmts ->
      let constructor =
        match stmt with
        | Define _ -> define
        | RecDefine _ -> rec_define
      in
      let stmt_helper = function
        | Define (func_name, func_args, var_decls, body, typ)
        | RecDefine (func_name, func_args, var_decls, body, typ) ->
          let new_var_decls var_decl =
            let varname, decl_expr, decl_typ = var_decl in
            let* new_decl_var, new_decls = expr_to_cexpr decl_expr in
            return (List.rev ((varname, CImm new_decl_var, decl_typ) :: new_decls))
          in
          let* new_body_var, new_body_decls = expr_to_cexpr body in
          let* new_vardecls = ListM.map new_var_decls var_decls in
          let new_vardecls = Base.List.concat new_vardecls in
          let new_body = CImm new_body_var in
          let new_vardecls = new_vardecls @ List.rev new_body_decls in
          return @@ constructor func_name func_args new_vardecls new_body typ
      in
      let new_stmt, _ = stmt_helper stmt |> run (0, []) in
      anf_helper (new_stmt :: acc) stmts
    | [] -> List.rev acc
  in
  anf_helper [] stmts
;;
