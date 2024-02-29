(** Copyright 2023-2024, Grigory Aseev and Matvey Kalashnikov *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

open RestrictedAst
open ResultCounter
open IResState
open IResState.Syntax
open Ast

type asm_val =
  | Imm of string
  | Reg of string
  | Mem of string

let imm i = Imm i
let reg r = Reg r
let mem_str m = Mem (Printf.sprintf "qword [rbp %s]" m)
let mem m = Mem m
let global_env : (string, int) Hashtbl.t = Hashtbl.create 20
let asm_code = Buffer.create 128

let reg_from_arg = function
  | 0 -> ok "rdi"
  | 1 -> ok "rsi"
  | 2 -> ok "rdx"
  | 3 -> ok "rcx"
  | 4 -> ok "r8"
  | 5 -> ok "r9"
  | _ -> error "Too many arguments"
;;

let storage_str = function
  | Mem value | Reg value | Imm value -> value
;;

let buid_store asm_val =
  let* offs, _ = decr_offset in
  let offset = Int.to_string offs in
  match asm_val with
  | Imm value | Reg value ->
    Buffer.add_string asm_code (Printf.sprintf "  mov qword [rbp %s], %s\n" offset value);
    ok (mem_str offset)
  | Mem value -> ok (mem value)
;;

let build_call name args =
  let args = Base.List.map args ~f:storage_str in
  let* _ =
    Base.List.foldi args ~init:(ok ()) ~f:(fun i acc arg ->
      let* _ = acc in
      let* reg = reg_from_arg i in
      Buffer.add_string asm_code (Printf.sprintf "  mov %s, %s\n" reg arg);
      ok ())
  in
  Buffer.add_string asm_code (Printf.sprintf "  call %s\n" name);
  buid_store (reg "rax")
;;

let codegen_imm env = function
  | ImmNum i -> ok (imm (Int.to_string i))
  | ImmBool b -> ok (imm (if b then "1" else "0"))
  | ImmId id ->
    (match Base.Map.Poly.find env id with
     | Some offeset -> ok (mem offeset)
     | None ->
       (match Hashtbl.find_opt global_env id with
        | Some arg_num ->
          Buffer.add_string asm_code (Printf.sprintf "  mov rax, %s\n" id);
          build_call "addNewPAppliClosure" [ reg "rax"; imm (Int.to_string arg_num) ]
        | None -> error "Global function not found"))
  | ImmUnit -> ok (imm "0")
;;

let codegen_binop op left right =
  let left = storage_str left in
  let right = storage_str right in
  (match op with
   | Add ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  add rax, %s\n" left right)
   | Sub ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  sub rax, %s\n" left right)
   | Mul ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  imul rax, %s\n" left right)
   | Div ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  cqo\n  idiv %s\n" left right)
   | Mod ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  cqo\n  idiv %s\n  mov rax, rdx\n" left right)
   | Eq ->
     Buffer.add_string
       asm_code
       (Printf.sprintf
          "  mov rax, %s\n  cmp rax, %s\n  sete al\n  movzx rax, al\n"
          left
          right)
   | Neq ->
     Buffer.add_string
       asm_code
       (Printf.sprintf
          "  mov rax, %s\n  cmp rax, %s\n  setne al\n  movzx rax, al\n"
          left
          right)
   | Less ->
     Buffer.add_string
       asm_code
       (Printf.sprintf
          "  mov rax, %s\n  cmp rax, %s\n  setl al\n  movzx rax, al\n"
          left
          right)
   | Leq ->
     Buffer.add_string
       asm_code
       (Printf.sprintf
          "  mov rax, %s\n  cmp rax, %s\n  setle al\n  movzx rax, al\n"
          left
          right)
   | Gre ->
     Buffer.add_string
       asm_code
       (Printf.sprintf
          "  mov rax, %s\n  cmp rax, %s\n  setg al\n  movzx rax, al\n"
          left
          right)
   | Geq ->
     Buffer.add_string
       asm_code
       (Printf.sprintf
          "  mov rax, %s\n  cmp rax, %s\n  setge al\n  movzx rax, al\n"
          left
          right)
   | And ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  and rax, %s\n" left right)
   | Or ->
     Buffer.add_string
       asm_code
       (Printf.sprintf "  mov rax, %s\n  or rax, %s\n" left right));
  buid_store (reg "rax")
;;

let rec codegen_cexpr env = function
  | CImmExpr imm -> codegen_imm env imm
  | CBinOp (op, left, right) ->
    let* left = codegen_imm env left in
    let* right = codegen_imm env right in
    codegen_binop op left right
  | CApp (func, argument) ->
    let* calee = codegen_imm env func in
    let* arg = codegen_imm env argument in
    build_call "applyPAppli" [ calee; arg ]
  | CIf (cond, then_, else_) ->
    let* cond = codegen_imm env cond in
    let* _, else_id = fresh_if in
    let* _, end_id = fresh_if in
    let else_label = Printf.sprintf "else_%d" else_id in
    let end_label = Printf.sprintf "end_%d" end_id in
    let cond_mem = storage_str cond in
    Buffer.add_string
      asm_code
      (Printf.sprintf "  cmp %s, 0\n  je %s\n" cond_mem else_label);
    let* then_ = codegen_aexpr env then_ in
    let* res = buid_store then_ in
    Buffer.add_string asm_code (Printf.sprintf "  jmp %s\n" end_label);
    Buffer.add_string asm_code (Printf.sprintf "%s:\n" else_label);
    let* else_ = codegen_aexpr env else_ in
    let else_mem =
      match else_ with
      | Mem value ->
        Buffer.add_string asm_code (Printf.sprintf "  mov rax, %s\n" value);
        "rax"
      | Reg value -> value
      | Imm value -> value
    in
    let res_mem = storage_str res in
    Buffer.add_string asm_code (Printf.sprintf "  mov %s, %s\n" res_mem else_mem);
    Buffer.add_string asm_code (Printf.sprintf "%s:\n" end_label);
    ok res

and codegen_aexpr env = function
  | ACExpr cexpr -> codegen_cexpr env cexpr
  | ALetIn (id, cexpr, aexpr) ->
    let* body = codegen_cexpr env cexpr in
    let* mem =
      match body with
      | Mem value -> ok value
      | _ -> error "Operation result should be in memory"
    in
    let new_env = Base.Map.Poly.set env ~key:id ~data:mem in
    codegen_aexpr new_env aexpr
;;

let codegen_bexpr = function
  | ALet (_, id, args, body) ->
    let env = Base.Map.Poly.empty in
    Buffer.add_string asm_code (Printf.sprintf "%s:\n" id);
    Buffer.add_string asm_code "  push rbp\n  mov rbp, rsp\n";
    Buffer.add_string asm_code "  sub rsp, RSP_OFFSET\n";
    let* env =
      Base.List.foldi
        ~f:(fun i env ->
          function
          | PImmExpr (ImmId id) ->
            if i < 6
            then (
              let* offset, _ = decr_offset in
              let* env = env in
              let* reg = reg_from_arg i in
              Buffer.add_string
                asm_code
                (Printf.sprintf "  mov qword [rbp %d], %s\n" offset reg);
              let env =
                Base.Map.Poly.set
                  env
                  ~key:id
                  ~data:(Printf.sprintf "qword [rbp %d]" offset)
              in
              ok env)
            else
              let* env = env in
              ok
                (Base.Map.Poly.set
                   env
                   ~key:id
                   ~data:(Printf.sprintf "qword [rbp + %d]" ((8 * (i - 5)) + 8)))
          | PImmWild -> env
          | _ -> error "Invalid argument")
        ~init:(ok env)
        args
    in
    Hashtbl.add global_env id (List.length args);
    let* body = codegen_aexpr env body in
    let body_mem = storage_str body in
    Buffer.add_string asm_code (Printf.sprintf "  mov rax, %s\n" body_mem);
    let* offset, _ = get_counters in
    let rsp_offset = -1 * offset mod 16 in
    let rsp_offset =
      if rsp_offset <> 0 then (-1 * offset) + 16 - rsp_offset else -1 * offset
    in
    Buffer.add_string asm_code (Printf.sprintf "  add rsp, %d\n" rsp_offset);
    Buffer.add_string asm_code "  mov rsp, rbp\n  pop rbp\n  ret\n";
    let replaced =
      Base.String.substr_replace_first
        (Buffer.contents asm_code)
        ~pattern:"RSP_OFFSET"
        ~with_:(Int.to_string rsp_offset)
    in
    Buffer.reset asm_code;
    ok replaced
;;

let codegen_program prog =
  let header =
    "extern print_bool\n\
     extern print_int\n\
     extern applyPAppli\n\
     extern addNewPAppliClosure\n\
     global main\n"
  in
  Hashtbl.add global_env "print_bool" 1;
  Hashtbl.add global_env "print_int" 1;
  Hashtbl.add global_env "applyPAppli" 2;
  Hashtbl.add global_env "addNewPAppliClosure" 2;
  let* result =
    List.fold_left
      (fun acc expr ->
        let* acc = acc in
        let* res = codegen_bexpr expr in
        ok (acc ^ res))
      (ok "")
      prog
  in
  ok (header ^ result)
;;

let run_asm prog = snd @@ runResState ~init:(0, 0) (codegen_program prog)
