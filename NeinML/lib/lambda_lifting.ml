(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type expression =
  | BinOp of expression * expression * Ast.binop * Typing.ty (** x * y *)
  | IfThenElse of expression * expression * expression * Typing.ty
      (** if condition then expr1 else expr2 *)
  | Apply of expression * expression * expression list * Typing.ty
      (** func arg1 arg2 ... *)
  | Variable of Ast.name * Typing.ty (** var *)
  | Value of Ast.const * Typing.ty (** value (const) *)
[@@deriving show { with_path = false }]

type 'expression var_decl = Ast.name * 'expression * Typing.ty
[@@deriving show { with_path = false }]

type 'expression statement =
  | Define of
      Ast.name * Ast.name list * 'expression var_decl list * 'expression * Typing.ty
  | RecDefine of
      Ast.name * Ast.name list * 'expression var_decl list * 'expression * Typing.ty
[@@deriving show { with_path = false }]

type 'expression statement_list = 'expression statement list
[@@deriving show { with_path = false }]

let get_meta = function
  | BinOp (_, _, _, meta)
  | IfThenElse (_, _, _, meta)
  | Apply (_, _, _, meta)
  | Variable (_, meta)
  | Value (_, meta) -> meta
;;

let define name args var_decls ret_v typ = Define (name, args, var_decls, ret_v, typ)

let rec_define name args var_decls ret_v typ =
  RecDefine (name, args, var_decls, ret_v, typ)
;;

module IntState = struct
  include Monad.State (struct
    type t = int * expression statement list
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

  let modify_lifted f =
    let* counter, lifted = get in
    put (counter, f lifted)
  ;;

  let fresh =
    let* counter = get_counter in
    let* () = modify_counter succ in
    return @@ String.concat "_" [ "__neinml"; "ll"; string_of_int counter ]
  ;;

  let add_statement name args var_decls ret_v typ mk =
    let stmt = mk name args var_decls ret_v typ in
    modify_lifted @@ fun stmts -> stmt :: stmts
  ;;
end

module ListM = Monad.ListM (IntState)

let lift_lambda statements =
  let open IntState in
  let rec func_helper acc = function
    | Ast.Func (name, body, _) ->
      let acc, body = func_helper acc body in
      name :: acc, body
    | body -> acc, body
  in
  let rec apply_helper acc = function
    | Ast.Apply (f, x, _) -> apply_helper (x :: acc) f
    | f -> f, acc
  in
  let rec expression_helper var_decls = function
    | Ast.BinOp (op1, op2, op, t) ->
      let* op1, var_decls = expression_helper var_decls op1 in
      let* op2, var_decls = expression_helper var_decls op2 in
      return (BinOp (op1, op2, op, t), var_decls)
    | Ast.LetIn (name, decl, body, _) | Ast.RecLetIn (name, decl, body, _) ->
      let decl_typ = Ast.get_meta decl in
      let args, decl = func_helper [] decl in
      (match decl_typ with
       | Typing.Arrow _ ->
         let* decl, my_var_decls = expression_helper [] decl in
         let* () = add_statement name args my_var_decls decl decl_typ define in
         expression_helper var_decls body
       | _ ->
         let* decl, var_decls = expression_helper var_decls decl in
         let var_decl = name, decl, decl_typ in
         expression_helper (var_decl :: var_decls) body)
    | Ast.IfThenElse (cond, thn, els, t) ->
      let* cond, var_decls = expression_helper var_decls cond in
      let* thn, var_decls = expression_helper var_decls thn in
      let* els, var_decls = expression_helper var_decls els in
      return (IfThenElse (cond, thn, els, t), var_decls)
    | Ast.Func (var, body, t) ->
      let vars, body = func_helper [] body in
      let* body, my_var_decls = expression_helper [] body in
      let* name = fresh in
      let* () = add_statement name (var :: vars) my_var_decls body t define in
      return (Variable (name, t), var_decls)
    | Ast.Apply (f, arg, t) ->
      let f, args = apply_helper [] f in
      let arg, args =
        match args with
        | [] -> arg, []
        | a :: args -> a, args @ [ arg ]
      in
      let* f, var_decls = expression_helper var_decls f in
      let folder arg (args, var_decls) =
        let* arg, var_decls = expression_helper var_decls arg in
        return (arg :: args, var_decls)
      in
      let* arg, arg_var_decls = expression_helper var_decls arg in
      let* args, var_decls = ListM.fold_right folder args ([], []) in
      let var_decls = arg_var_decls @ var_decls in
      return (Apply (f, arg, args, t), var_decls)
    | Ast.Variable (name, t) -> return (Variable (name, t), var_decls)
    | Ast.Value (value, t) -> return (Value (value, t), var_decls)
  in
  let stmt_helper stmt =
    let name, body, t, mk =
      match stmt with
      | Ast.Define (name, body, t) -> name, body, t, define
      | Ast.RecDefine (name, body, t) -> name, body, t, rec_define
    in
    let args, body = func_helper [] body in
    let* body, var_decls = expression_helper [] body in
    add_statement name args (List.rev var_decls) body t mk
  in
  let _, (_, lifted) = ListM.map stmt_helper statements |> run (0, []) in
  List.rev lifted
;;
