exception Error of string

let comp text = 
  let lexbuf = Lexing.from_string text in
  try Ds_parser.program Ds_lexer.token lexbuf with
  | Ds_lexer.Error message -> raise (Error message)
  | Ds_parser.Error ->
      let position = Lexing.lexeme_start_p lexbuf in
      let line     = position.pos_lnum in 
      let column   = position.pos_cnum - position.pos_bol in 
      raise (Error
              (Printf.sprintf
                "syntax error at line %d, column %d"
                line column))