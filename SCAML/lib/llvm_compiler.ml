open RestrictedAst
open Llvm
open Result
open Ast

let context = global_context ()
let the_module = create_module context "SCAML"
let builder = builder context
let int_64 = i64_type context
let void = void_type context
let named_values : (string, llvalue) Hashtbl.t = Hashtbl.create 20
let global_scope : (string, int * llvalue) Base.Map.Poly.t = Base.Map.Poly.empty
let ( let* ) = bind

let codegen_imm = function
  | ImmNum x -> ok (const_int int_64 x)
  | ImmBool b -> ok (const_int int_64 (Base.Bool.to_int b))
  | ImmUnit -> ok (const_pointer_null void)
  | ImmId id ->
    (match Hashtbl.find_opt named_values id with
     | Some v -> ok (build_load int_64 v id builder)
     | None -> error (Printf.sprintf "Unknown identifier %s" id))
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
    ok (codegen_binop op l' r')
  | CImmExpr e -> codegen_imm e
  | CApp (func, arg) -> error "Not implemented"
;;

let rec codegen_aexpr = function
  | ACExpr e -> codegen_cexpr e
  | AIf (cond, then_, else_) ->
    let* cond = codegen_aexpr cond in
    let zero = const_int int_64 0 in
    let cond_val = build_icmp Icmp.Eq cond zero "condition" builder in
    let start_bb = insertion_block builder in
    let the_function = block_parent start_bb in
    let then_bb = append_block context "then" the_function in
    position_at_end then_bb builder;
    let* then_val = codegen_aexpr then_ in
    let new_then_bb = insertion_block builder in
    let else_bb = append_block context "else" the_function in
    position_at_end else_bb builder;
    let* else_val = codegen_aexpr else_ in
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
    ok phi
  | ALetIn (id, cexpr, aexpr) ->
    let* body = codegen_cexpr cexpr in
    let alloca = build_alloca int_64 id builder in
    build_store body alloca builder |> ignore;
    Hashtbl.add named_values id alloca;
    codegen_aexpr aexpr
;;

(* let codegen_bexpr = function
| ALet (is_rec, id, args, body) ->
  Hashtbl.clear named_values;
   *)