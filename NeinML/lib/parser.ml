(** Copyright 2023-2024, Mikhail Vyrodov and Vyacheslav Buchin *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open Angstrom
module ListM = Monad.ListM (Angstrom)

let is_space = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

let spaces = skip_many (satisfy is_space)

let accepted_var_symbols = function
  | 'a' .. 'z' -> true
  | 'A' .. 'Z' -> true
  | '_' -> true
  | _ -> false
;;

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let parse_name =
  let symbols_from_second s = accepted_var_symbols s || is_digit s in
  take_while1 accepted_var_symbols
  >>= fun first_symbol ->
  take_while symbols_from_second
  >>= fun other_symbols -> return (first_symbol ^ other_symbols)
;;

let str_integer = take_while1 is_digit

let is_bool =
  parse_name
  >>= function
  | "true" -> return true
  | "false" -> return false
  | _ -> fail "not bool"
;;

let parse_operator = function
  | "+" -> return Ast.Add
  | "-" -> return Ast.Sub
  | "*" -> return Ast.Mul
  | "/" -> return Ast.Div
  | "%" -> return Ast.Mod
  | "&&" -> return Ast.And
  | "||" -> return Ast.Or
  | "=" -> return Ast.Equal
  | "<>" -> return Ast.NotEqual
  | "<" -> return Ast.Less
  | "<=" -> return Ast.LessOrEq
  | ">" -> return Ast.More
  | ">=" -> return Ast.MoreOrEq
  | _ -> fail "unbound operator"
;;

let integer = str_integer >>| int_of_string
let cval x = return @@ Ast.Value (x, ())
let cvar x = return (Ast.Variable (x, ()))
let cbinop x y op = parse_operator op >>= fun op -> return @@ Ast.BinOp (x, y, op, ())
let capply x y = return @@ Ast.Apply (x, y, ())
let cfunc x y = return @@ Ast.Func (x, y, ())
let cdef x y = return (Ast.Define (x, y, ()))
let crecdef x y = return (Ast.RecDefine (x, y, ()))
let cletin x y z = return (Ast.LetIn (x, y, z, ()))
let crecletin x y z = return (Ast.RecLetIn (x, y, z, ()))

let cif condition then_statement else_statement =
  return (Ast.IfThenElse (condition, then_statement, else_statement, ()))
;;

let keywords =
  [ "let"
  ; "in"
  ; "rec"
  ; "match"
  ; "function"
  ; "fun"
  ; "type"
  ; "if"
  ; "then"
  ; "else"
  ; "int"
  ; "bool"
  ]
;;

let varname =
  spaces *> parse_name
  <* spaces
  >>= fun var_name ->
  if List.exists (fun x -> String.equal var_name x) keywords
  then
    fail
      "Parsing error: Your variable name is equal to one of the keywords in MiniML \
       language."
  else return var_name
;;

type dispatch =
  { func_call : dispatch -> unit Ast.expression Angstrom.t
  ; parse_lam : dispatch -> string -> unit Ast.expression Angstrom.t
  ; parse_if : dispatch -> string -> unit Ast.expression Angstrom.t
  ; arithmetical : dispatch -> string -> unit Ast.expression Angstrom.t
  ; parse_priority : dispatch -> string -> unit Ast.expression Angstrom.t
  ; logical : dispatch -> string -> unit Ast.expression Angstrom.t
  ; parse_and : dispatch -> string -> unit Ast.expression Angstrom.t
  ; logical_sequence : dispatch -> string -> unit Ast.expression Angstrom.t
  ; bracket : dispatch -> unit Ast.expression Angstrom.t
  ; bracket_singles : dispatch -> string -> unit Ast.expression Angstrom.t
  ; all_singles : dispatch -> string -> unit Ast.expression Angstrom.t
  ; all_ops : dispatch -> string -> unit Ast.expression Angstrom.t
  ; parse_letin : dispatch -> string -> unit Ast.expression Angstrom.t
  ; parse_def : dispatch -> string -> unit Ast.statement Angstrom.t
  }

type error = [ `ParsingError of string ]

let pp_error ppf = function
  | `ParsingError s -> Format.fprintf ppf "%s" s
;;

let parse_int = spaces *> integer <* spaces >>= fun c -> cval @@ Ast.VInt c
let parse_bool = spaces *> is_bool <* spaces >>= fun c -> cval @@ Ast.VBool c
let parse_const = [ parse_int; parse_bool ]
let parse_part_singles = choice (parse_const @ [ spaces *> varname <* spaces >>= cvar ])
let parse_singles = spaces *> parse_part_singles <* spaces

let input_end_with end_input =
  spaces *> peek_string (String.length end_input)
  >>= fun x ->
  match String.equal x end_input with
  | true -> return "Ok"
  | false -> fail "Parsing error: Wrong expression syntax."
;;

let parse_eof =
  peek_char
  >>= function
  | None -> return "Ok"
  | Some _ -> fail "Parsing error: Wrong expression syntax."
;;

let input_end end_str =
  match end_str with
  | "EOF" -> parse_eof <|> input_end_with "let"
  | _ -> input_end_with end_str
;;

let parse_miniml =
  let all_ops pack inp_end =
    spaces
    *> choice
         [ pack.all_singles pack inp_end
         ; pack.arithmetical pack inp_end
         ; pack.parse_and pack inp_end
         ; pack.logical_sequence pack inp_end
         ; pack.logical pack inp_end
         ]
    <* spaces
  in
  let func_call pack =
    fix (fun _ ->
      spaces *> (varname >>= fun x -> cvar x)
      <|> (char '(' *> pack.parse_if pack ")" <* char ')')
      <|> (char '(' *> pack.parse_lam pack ")" <* char ')')
      <|> (char '(' *> pack.func_call pack <* char ')')
      <|> (char '(' *> pack.parse_letin pack ")" <* char ')')
      >>= fun x_var ->
      many (parse_singles <|> pack.bracket pack) >>= ListM.fold_left capply x_var)
  in
  let parse_lam pack inp_end =
    let parse_bracket_inner_def =
      spaces *> char '(' *> spaces *> (pack.all_ops pack ")" <|> pack.parse_letin pack ")")
      <* spaces
      <* char ')'
      <* spaces
      <* input_end inp_end
    in
    fix (fun _ ->
      spaces *> string "fun" *> many (spaces *> varname <* spaces)
      >>= fun args ->
      string "->"
      *> spaces
      *> (parse_bracket_inner_def
         <|> pack.parse_letin pack inp_end
         <|> pack.all_ops pack inp_end)
      >>= ListM.fold_right cfunc args)
  in
  let parse_var = spaces *> varname <* spaces >>= cvar in
  let parse_part_singles = choice (parse_const @ [ parse_var ]) in
  let parse_singles = spaces *> parse_part_singles <* spaces in
  let parse_if pack inp_end =
    fix (fun _ ->
      let parse_condition end_input =
        choice
          [ parse_var <* input_end end_input
          ; parse_bool <* input_end end_input
          ; pack.func_call pack <* input_end end_input
          ; pack.logical pack end_input
          ; pack.parse_and pack end_input
          ; pack.logical_sequence pack end_input
          ]
      in
      let parse_bracket_condition end_input =
        char '(' *> parse_condition ")"
        <* char ')'
        <* spaces
        <* input_end end_input
        >>= fun x -> return x
      in
      spaces
      *> string "if"
      *> spaces
      *> (parse_bracket_condition "then" <|> parse_condition "then")
      <* string "then"
      >>= fun condition ->
      pack.all_ops pack "else"
      <|> pack.parse_letin pack "else"
      >>= fun true_expr ->
      string "else" *> (pack.all_ops pack inp_end <|> pack.parse_letin pack inp_end)
      >>= fun false_expr -> cif condition true_expr false_expr)
  in
  let bracket_singles pack inp_end =
    choice
      [ parse_singles <* input_end inp_end
      ; pack.parse_lam pack inp_end
      ; pack.func_call pack <* input_end inp_end
      ; pack.parse_if pack inp_end
      ; pack.bracket pack <* input_end inp_end
      ]
  in
  let bracket pack =
    fix (fun _ ->
      spaces
      *> char '('
      *> choice
           [ parse_singles <* input_end ")"
           ; pack.func_call pack <* input_end ")"
           ; pack.parse_if pack ")"
           ; pack.parse_lam pack ")"
           ; pack.parse_priority pack ")"
           ; pack.arithmetical pack ")"
           ; pack.parse_and pack ")"
           ; pack.logical_sequence pack ")"
           ; pack.logical pack ")"
           ; pack.parse_letin pack ")"
           ]
      <* char ')'
      <* spaces)
  in
  let parse_priority pack inp_end =
    fix (fun _ ->
      pack.bracket_singles pack "*"
      <|> pack.bracket_singles pack "/"
      <|> pack.bracket_singles pack "%"
      >>= fun left ->
      choice [ string "*"; string "/"; string "%" ]
      >>= fun operator ->
      pack.bracket_singles pack inp_end
      <|> pack.parse_priority pack inp_end
      >>= fun right -> cbinop left right operator)
  in
  let all_singles pack end_input =
    fix (fun _ ->
      spaces
      *> (pack.bracket_singles pack end_input
         <|> (pack.parse_priority pack end_input <* input_end end_input))
      <* spaces)
  in
  let arithmetical pack end_input =
    fix (fun _ ->
      let parse_simple_op end_input op =
        pack.all_singles pack op
        <* string op
        >>= fun left ->
        pack.all_singles pack end_input
        <* input_end end_input
        >>= fun right -> cbinop left right op
      in
      let parse_simple_ops end_input =
        [ parse_simple_op end_input "+"; parse_simple_op end_input "-" ]
      in
      let parse_complex_op end_input operator =
        pack.all_singles pack operator
        <* string operator
        >>= fun left ->
        let matching = function
          | Ast.Variable _ -> spaces *> pack.arithmetical pack end_input
          | Ast.Value _ -> spaces *> pack.arithmetical pack end_input
          | _ ->
            spaces *> pack.all_singles pack end_input
            <|> spaces *> pack.arithmetical pack end_input
        in
        matching left >>= fun right -> cbinop left right operator
      in
      choice
        (parse_simple_ops end_input
        @ [ parse_complex_op end_input "+"; parse_complex_op end_input "-" ]))
  in
  let logical pack inp_end =
    fix (fun _ ->
      let parse_logical_op end_input operator =
        pack.all_singles pack operator
        <|> pack.arithmetical pack operator
        <* spaces
        <* string operator
        >>= fun left ->
        pack.all_singles pack end_input
        <|> pack.arithmetical pack inp_end
        <|> pack.logical pack inp_end
        <* spaces
        >>= fun right -> cbinop left right operator
      in
      let parse_logical end_input =
        [ parse_logical_op end_input "="
        ; parse_logical_op end_input ">="
        ; parse_logical_op end_input ">"
        ; parse_logical_op end_input "<="
        ; parse_logical_op end_input "<"
        ; parse_logical_op end_input "<>"
        ]
      in
      choice (parse_logical inp_end))
  in
  let parse_and pack inp_end =
    fix (fun _ ->
      let parse_and end_inp operator =
        pack.all_singles pack operator
        <|> pack.logical pack operator
        <* spaces
        <* string operator
        >>= fun left ->
        pack.all_singles pack end_inp
        <|> pack.logical pack end_inp
        <|> pack.parse_and pack inp_end
        <* spaces
        >>= fun right -> cbinop left right operator
      in
      parse_and inp_end "&&")
  in
  let logical_sequence pack inp_end =
    fix (fun _ ->
      let parse_or end_inp operator =
        pack.all_singles pack operator
        <|> pack.logical pack operator
        <|> pack.parse_and pack operator
        <* spaces
        <* string operator
        >>= fun left ->
        pack.all_singles pack end_inp
        <|> spaces *> pack.logical pack end_inp
        <|> pack.parse_and pack inp_end
        <|> pack.logical_sequence pack inp_end
        <* spaces
        >>= fun right -> cbinop left right operator
      in
      parse_or inp_end "||")
  in
  let parse_rec =
    peek_string 3
    >>= function
    | "rec" -> string "rec" *> return true
    | _ -> return false
  in
  let parse_letin pack inp_end =
    fix (fun _ ->
      spaces *> string "let" *> spaces *> parse_rec
      <* spaces
      >>= fun rec_flag ->
      varname
      <* spaces
      >>= fun fun_name ->
      many (spaces *> varname <* spaces)
      >>= fun args ->
      input_end "="
      *> char '='
      *> spaces
      *> (pack.all_ops pack "in" <|> pack.parse_letin pack "in")
      <* spaces
      >>= ListM.fold_right cfunc args
      <* string "in"
      >>= fun parsed_func ->
      pack.all_ops pack inp_end
      <|> pack.parse_letin pack inp_end
      >>= fun z ->
      match rec_flag with
      | true -> crecletin fun_name parsed_func z
      | false -> cletin fun_name parsed_func z)
  in
  let parse_def pack inp_end =
    fix (fun _ ->
      spaces *> string "let" *> spaces *> parse_rec
      <* spaces
      >>= fun rec_flag ->
      varname
      <* spaces
      >>= fun fun_name ->
      many (spaces *> varname <* spaces)
      >>= fun args ->
      char '=' *> spaces *> (pack.all_ops pack inp_end <|> pack.parse_letin pack inp_end)
      <* spaces
      >>= ListM.fold_right cfunc args
      >>= fun parsed_func ->
      match rec_flag with
      | true -> crecdef fun_name parsed_func
      | false -> cdef fun_name parsed_func)
  in
  { func_call
  ; parse_lam
  ; parse_if
  ; arithmetical
  ; parse_priority
  ; logical
  ; parse_and
  ; logical_sequence
  ; bracket
  ; bracket_singles
  ; all_singles
  ; all_ops
  ; parse_def
  ; parse_letin
  }
;;

let parse str =
  match
    Angstrom.parse_string
      (many (parse_miniml.parse_def parse_miniml "EOF"))
      ~consume:Angstrom.Consume.All
      str
  with
  | Result.Ok _ as ok -> ok
  | Result.Error er -> Result.Error (`ParsingError er)
;;
