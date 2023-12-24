open RestrictedAst
open Llvm
open Result
open Ast

let context = global_context ()
let the_module = create_module context "SCAML"
let builder = builder context
let int_64 = i64_type context
let void = void_type context
let named_values : (string, int * llvalue) Hashtbl.t = Hashtbl.create 20
let ( let* ) = bind

let codegen_imm = function
  | ImmNum x -> ok (-1, const_int int_64 x)
  | ImmBool b -> ok (-1, const_int int_64 (Base.Bool.to_int b))
  | ImmUnit -> ok (-1, const_pointer_null void)
  | ImmId id ->
    (match Hashtbl.find_opt named_values id with
     | Some (args, v) -> ok (args, build_load int_64 v id builder)
     | None ->
       (match lookup_function id the_module with
        | Some v -> ok @@ (Array.length (params v), v)
        | None -> error "Unknown variable"))
;;

(* fix and add global functions*)

let codegen_binop = function
  | Add -> fun x y -> build_add x y "addtmp" builder
  | Sub -> fun x y -> build_sub x y "subtmp" builder
  | Mul -> fun x y -> build_mul x y "multmp" builder
  | Div -> fun x y -> build_sdiv x y "divtmp" builder
  | Mod -> fun x y -> build_srem x y "modtmp" builder
  | Eq -> fun x y -> build_icmp Icmp.Eq x y "eqtmp" builder
  | Neq -> fun x y -> build_icmp Icmp.Ne x y "neqtmp" builder
  | Less -> fun x y -> build_icmp Icmp.Slt x y "lesstmp" builder
  | Leq -> fun x y -> build_icmp Icmp.Sle x y "leqtmp" builder
  | Gre -> fun x y -> build_icmp Icmp.Sgt x y "gretmp" builder
  | Geq -> fun x y -> build_icmp Icmp.Sge x y "geqtmp" builder
  | And -> fun x y -> build_and x y "andtmp" builder
  | Or -> fun x y -> build_or x y "ortmp" builder
;;

let codegen_cexpr = function
  | CBinOp (op, l, r) ->
    let* l' = codegen_imm l in
    let* r' = codegen_imm r in
    let res = codegen_binop op (snd l') (snd r') in
    ok (-1, build_zext res int_64 "to_int" builder)
  | CImmExpr e -> codegen_imm e
  | CApp (func, argument) ->
    let* calee = codegen_imm func in
    let arg_num, calee = calee in
    let* arg = codegen_imm argument in
    let argument_arg_num, arg = arg in
    (*Если аргумент это функция, то мы должны создать замыкание и для него*)
    let arg =
      if type_of arg = pointer_type context
      then
        build_call
          (function_type int_64 [| int_64; int_64 |])
          (Option.get (lookup_function "addNewPaplyClosure" the_module))
          [| build_pointercast arg int_64 "cast_pointer_to_int" builder
           ; (if argument_arg_num = -1
              then params arg |> Base.Array.length |> const_int int_64
              else const_int int_64 argument_arg_num)
          |]
          "paplyClosure"  
          builder
      else arg
    in
    (*Создаем замыкание для функции и применяем к нему аргумент*)
    let pointer =
      build_call
        (function_type int_64 [| int_64; int_64 |])
        (Option.get (lookup_function "addNewPaplyClosure" the_module))
        [| build_pointercast calee int_64 "cast_pointer_to_int" builder
         ; (if arg_num = -1
            then params calee |> Base.Array.length |> const_int int_64
            else const_int int_64 arg_num)
        |]
        "paplyClosure"
        builder
    in
    ok
      ( (if arg_num = -1 then params calee |> Base.Array.length else arg_num)
      , build_call
          (function_type int_64 [| int_64; int_64 |])
          (Option.get (lookup_function "applyPaply" the_module))
          [| pointer; arg |]
          "paplyApplication"
          builder )
;;

let rec codegen_aexpr = function
  | ACExpr e -> codegen_cexpr e
  | AIf (cond, then_, else_) ->
    let* cond = codegen_aexpr cond in
    let cond = snd cond in
    let zero = const_int int_64 0 in
    let cond_val = build_icmp Icmp.Ne cond zero "ifcondition" builder in
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    let then_bb = append_block context "then_br" the_function in
    position_at_end then_bb builder;
    let* then_val = codegen_aexpr then_ in
    let then_args, then_val = then_val in
    let new_then_bb = insertion_block builder in
    let else_bb = append_block context "else_br" the_function in
    position_at_end else_bb builder;
    let* else_val = codegen_aexpr else_ in
    let else_args, else_val = else_val in
    let new_else_bb = insertion_block builder in
    let merge_bb = append_block context "ifcontext" the_function in
    position_at_end merge_bb builder;
    let incoming = [ then_val, new_then_bb; else_val, new_else_bb ] in
    let phi = build_phi incoming "ifphi" builder in
    position_at_end start_bb builder;
    build_cond_br cond_val then_bb else_bb builder |> ignore;
    position_at_end new_then_bb builder;
    build_br merge_bb builder |> ignore;
    position_at_end new_else_bb builder;
    build_br merge_bb builder |> ignore;
    position_at_end merge_bb builder;
    if then_args = else_args
    then ok (then_args, phi)
    else error "If branches must have the same type"
  | ALetIn (id, cexpr, aexpr) ->
    let* body = codegen_cexpr cexpr in
    let body_args, body = body in
    let alloca = build_alloca int_64 id builder in
    build_store body alloca builder |> ignore;
    Hashtbl.add named_values id (body_args, alloca);
    codegen_aexpr aexpr
;;

let codegen_bexpr = function
  | ALet (_, id, args, body) ->
    Hashtbl.clear named_values;
    let ints = Array.make (List.length args) int_64 in
    let ftype = function_type int_64 ints in
    let* func =
      match lookup_function id the_module with
      | Some _ -> error "Function already exists"
      | None -> ok @@ declare_function id ftype the_module
    in
    let* names =
      let rec check acc = function
        | [] -> ok (List.rev acc)
        | PImmExpr (ImmId id) :: xs -> check (id :: acc) xs
        | PImmWild :: xs -> check ("0_unused_underscore_variable" :: acc) xs
        | _ -> error "Invalid argument"
      in
      check [] args
    in
    Array.iteri
      (fun i a ->
        let name = List.nth names i in
        set_value_name name a)
      (params func);
    let bb = append_block context "entry" func in
    position_at_end bb builder;
    Array.iteri
      (fun i a ->
        let name = List.nth names i in
        let alloca = build_alloca int_64 name builder in
        build_store a alloca builder |> ignore;
        Hashtbl.add named_values name (-1, alloca))
      (params func);
    let* ret_val = codegen_aexpr body in
    (*Если возвращается функция, то для нее создается замыкание и возращается оно*)
    let ret_val =
      if type_of (snd ret_val) = pointer_type context
      then
        build_call
          (function_type int_64 [| int_64; int_64 |])
          (Option.get (lookup_function "addNewPaplyClosure" the_module))
          [| build_pointercast (snd ret_val) int_64 "cast_pointer_to_int" builder
           ; params (snd ret_val) |> Base.Array.length |> const_int int_64
          |]
          "newPaplyClosure"
          builder
      else snd ret_val
    in
    let _ = build_ret ret_val builder in
    ok func
;;

let codegen_program prog = 

  let runtime =
  [  declare_function
        "addNewPaplyClosure"
        (function_type int_64 [| int_64; int_64 |])
        the_module
    ; declare_function "applyPaply" (function_type int_64 [| int_64; int_64 |]) the_module
  ]
  in
  let* result = List.fold_left (fun acc bexpr ->
    let* acc = acc in
    let* res = codegen_bexpr bexpr in
    ok (res :: acc)
  )
  (ok runtime)
  prog
  in
  ok (List.rev result)
