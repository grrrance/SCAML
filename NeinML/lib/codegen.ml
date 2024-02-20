(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Llvm

let context = global_context ()
let the_module = create_module context "main"
let builder = builder context
let i64_typ = i64_type context
let ptr_typ = pointer_type context
let empty_map = Base.Map.empty (module Base.String)
let lookup_func_exn name = lookup_function name the_module |> Option.get

let build_alloc_closure func arity =
  let alloc_cls_t = function_type i64_typ [| i64_typ; i64_typ |] in
  let alloc_cls = lookup_func_exn "__neinml_alloc_cls" in
  let func = build_pointercast func i64_typ "pointer_to_i64" builder in
  let arity = const_int i64_typ arity in
  build_call alloc_cls_t alloc_cls [| func; arity |] "allocd_cls" builder
;;

let build_closure_call cls args =
  let argc = List.length args in
  let args_t = array_type i64_typ argc in
  let args_ptr = build_alloca args_t "args" builder in
  let fill i e =
    let addr =
      build_gep
        args_t
        args_ptr
        [| const_int i64_typ 0; const_int i64_typ i |]
        "elem"
        builder
    in
    let (_ : Llvm.llvalue) = build_store e addr builder in
    ()
  in
  List.iteri fill args;
  let apply_t = function_type i64_typ [| i64_typ; i64_typ; ptr_typ |] in
  let apply = lookup_func_exn "__neinml_applyn" in
  let cls =
    if type_of cls = ptr_typ then build_load i64_typ cls "dereference" builder else cls
  in
  build_call apply_t apply [| cls; const_int i64_typ argc; args_ptr |] "applied" builder
;;

let build_apply0 func =
  let apply0_t = function_type i64_typ [| i64_typ |] in
  let apply0 = lookup_func_exn "__neinml_apply0" in
  let func = build_pointercast func i64_typ "pointer_to_i64" builder in
  build_call apply0_t apply0 [| func |] "applied0" builder
;;

let build_application codegen env name args =
  let args = List.map codegen args in
  let cls =
    match Base.Map.find env name with
    | Some f -> f
    | None ->
      let f = lookup_func_exn name in
      (match params f |> Array.length with
       | 0 -> build_apply0 f
       | arity -> build_alloc_closure f arity)
  in
  build_closure_call cls args
;;

let codegen_immexpr env =
  let open Anf in
  function
  | ImmInt value -> const_int i64_typ value
  | ImmBool value -> const_int i64_typ (Bool.to_int value)
  | ImmVar (varname, _) ->
    (match Base.Map.find env varname with
     | Some value -> build_load i64_typ value varname builder
     | None ->
       let func = lookup_func_exn varname in
       (match params func |> Array.length with
        | 0 -> build_apply0 func
        | n -> build_alloc_closure func n))
;;

let rec process_var_decls env = function
  | x :: xs ->
    let _, new_env = codegen_var_decl env x in
    process_var_decls new_env xs
  | _ -> env

and codegen_cexpr env =
  let open Anf in
  let constructor =
    let open Ast in
    function
    | Add -> build_add
    | Sub -> build_sub
    | Mul -> build_mul
    | Div -> build_sdiv
    | Mod -> build_srem
    | And -> build_and
    | Or -> build_or
    | Equal -> build_icmp Icmp.Eq
    | NotEqual -> build_icmp Icmp.Ne
    | Less -> build_icmp Icmp.Slt
    | LessOrEq -> build_icmp Icmp.Sle
    | More -> build_icmp Icmp.Sgt
    | MoreOrEq -> build_icmp Icmp.Sge
  in
  function
  | CBinOp (lhs_imm, rhs_imm, Div, typ) ->
    let new_expr = CApply ("__neinml_divide", lhs_imm, [ rhs_imm ], typ) in
    codegen_cexpr env new_expr
  | CBinOp (lhs_imm, rhs_imm, binop, _) ->
    let lhs = codegen_immexpr env lhs_imm in
    let rhs = codegen_immexpr env rhs_imm in
    let op_constructor = constructor binop in
    let res = op_constructor lhs rhs (Ast.get_binop_str binop ^ "_binop") builder in
    build_zext res i64_typ "_zext" builder
  | CIfThenElse (condition, (then_lets, then_expr), (else_lets, else_expr), _) ->
    let cond = codegen_immexpr env condition in
    (* Convert condition to a bool by comparing equal to 0.0 *)
    let zero = Llvm.const_int i64_typ 0 in
    let cond_val = Llvm.build_icmp Llvm.Icmp.Ne cond zero "ifcond" builder in
    (* Grab the first block so that we might later add the conditional branch
     * to it at the end of the function. *)
    let start_bb = Llvm.insertion_block builder in
    let the_function = Llvm.block_parent start_bb in
    let then_bb = Llvm.append_block context "then" the_function in
    (* Emit 'then' value. *)
    Llvm.position_at_end then_bb builder;
    let new_env = process_var_decls env then_lets in
    let then_val = codegen_cexpr new_env then_expr in
    (* Codegen of 'then' can change the current block, update then_bb for the
     * phi. We create a new name because one is used for the phi node, and the
     * other is used for the conditional branch. *)
    let new_then_bb = Llvm.insertion_block builder in
    (* Emit 'else' value. *)
    let else_bb = Llvm.append_block context "else" the_function in
    Llvm.position_at_end else_bb builder;
    let new_env = process_var_decls env else_lets in
    let else_val = codegen_cexpr new_env else_expr in
    (* Codegen of 'else' can change the current block, update else_bb for the
     * phi. *)
    let new_else_bb = Llvm.insertion_block builder in
    (* Emit merge block. *)
    let merge_bb = Llvm.append_block context "ifcont" the_function in
    Llvm.position_at_end merge_bb builder;
    let incoming = [ then_val, new_then_bb; else_val, new_else_bb ] in
    let phi = Llvm.build_phi incoming "iftmp" builder in
    (* Return to the start block to add the conditional branch. *)
    Llvm.position_at_end start_bb builder;
    let (_ : Llvm.llvalue) = Llvm.build_cond_br cond_val then_bb else_bb builder in
    (* Set a unconditional branch at the end of the 'then' block and the
     * 'else' block to the 'merge' block. *)
    Llvm.position_at_end new_then_bb builder;
    let (_ : Llvm.llvalue) = Llvm.build_br merge_bb builder in
    Llvm.position_at_end new_else_bb builder;
    let (_ : Llvm.llvalue) = Llvm.build_br merge_bb builder in
    (* Finally, set the builder to the end of the merge block. *)
    Llvm.position_at_end merge_bb builder;
    phi
  | CImm imm -> codegen_immexpr env imm
  | CApply (name, arg, args, _) ->
    build_application (codegen_immexpr env) env name (arg :: args)

and codegen_var_decl env (varname, body, _) =
  let codegened_body = codegen_cexpr env body in
  let alloca = build_alloca i64_typ (varname ^ "alloca") builder in
  let (_ : Llvm.llvalue) = build_store codegened_body alloca builder in
  let new_env = Base.Map.set env ~key:varname ~data:alloca in
  alloca, new_env
;;

let create_func_typ args =
  let args_typ = Array.make (List.length args) i64_typ in
  let func_typ = function_type i64_typ args_typ in
  func_typ
;;

let codegen_args env args func_name =
  let f_typ = create_func_typ args in
  assert (lookup_function func_name the_module = None);
  let f = declare_function func_name f_typ the_module in
  let args_arr = Array.of_list args in
  Array.iteri
    (fun i a ->
      let name = Array.get args_arr i in
      set_value_name name a)
    (params f);
  let bb = append_block context "func_entry_block" f in
  position_at_end bb builder;
  let rec process_args i env = function
    | x :: xs ->
      let name = Array.get args_arr i in
      let alloca = build_alloca i64_typ name builder in
      let (_ : Llvm.llvalue) = build_store x alloca builder in
      let new_env = Base.Map.set env ~key:name ~data:alloca in
      process_args (i + 1) new_env xs
    | _ -> env
  in
  let new_env = process_args 0 env (Array.to_list @@ params f) in
  f, new_env
;;

let codegen_define = function
  | Lambda_lifting.Define (func_name, func_args, var_decls, body, _)
  | Lambda_lifting.RecDefine (func_name, func_args, var_decls, body, _) ->
    let env = empty_map in
    let f, new_env = codegen_args env func_args func_name in
    let new_env = process_var_decls new_env var_decls in
    let return_val = codegen_cexpr new_env body in
    let (_ : Llvm.llvalue) = build_ret return_val builder in
    (match Llvm_analysis.verify_function f with
     | true -> ()
     | false ->
       Stdlib.Format.printf "invalid function generated\n%s\n" (Llvm.string_of_llvalue f);
       Llvm_analysis.assert_valid_function f);
    f
;;

let codegen program =
  let program_declarations =
    [ declare_function
        "__neinml_alloc_cls"
        (function_type i64_typ [| i64_typ; i64_typ |])
        the_module
    ; declare_function
        "__neinml_applyn"
        (function_type i64_typ [| i64_typ; i64_typ; ptr_typ |])
        the_module
    ; declare_function "__neinml_apply0" (function_type i64_typ [| i64_typ |]) the_module
    ; declare_function "print_int" (function_type i64_typ [| i64_typ |]) the_module
    ; declare_function "print_bool" (function_type i64_typ [| i64_typ |]) the_module
    ; declare_function
        "__neinml_divide"
        (function_type i64_typ [| i64_typ; i64_typ |])
        the_module
    ]
  in
  let rec helper acc = function
    | x :: xs ->
      let func = codegen_define x in
      helper (func :: acc) xs
    | [] -> acc
  in
  let result = helper program_declarations program in
  List.rev result
;;
