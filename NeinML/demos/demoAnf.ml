(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Neinml_lib

let () =
  let s = Stdio.In_channel.input_all Stdlib.stdin in
  match Neinml_lib.Parser.parse s with
  | Result.Ok ast ->
    (match Neinml_lib.Inferencer.w_stms_list ast with
     | Result.Ok result ->
       let _, typ_ast = result in
       let unique_names_ast = Neinml_lib.Closure.unique_names typ_ast in
       Format.printf
         "%a\n%!"
         Pprintanf.pp_statements_list_anf
         (Neinml_lib.Closure.closure_converse unique_names_ast
         |> Lambda_lifting.lift_lambda
         |> Anf.make_anf)
     | Result.Error _ -> Format.printf "inferencer error")
  | Error _ -> Format.printf "Parsing error"
;;