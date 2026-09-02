{
  exception Error of string
}

let whitespace = [' ' '\t' '\r']+
let digit = ['0'-'9']
let ident_start = ['a'-'z' 'A'-'Z' '_']
let ident_rest  = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']

rule token = parse
  | whitespace
    { token lexbuf }
  | '\n'
    { Lexing.new_line lexbuf;
      token lexbuf }

  | "return" { Ds_parser.RETURN }
  | "let"    { Ds_parser.LET }
  | "in"     { Ds_parser.IN }
  | "handle" { Ds_parser.HANDLE }
  | "with"   { Ds_parser.WITH }
  | "op"     { Ds_parser.OP }
  | "fun"    { Ds_parser.FUN }

  | "->" { Ds_parser.ARROW }
  | "+" { Ds_parser.PLUS }
  | "=" { Ds_parser.EQUAL }
  | "," { Ds_parser.COMMA }
  | "(" { Ds_parser.LPAREN }
  | ")" { Ds_parser.RPAREN }

  | digit+ as text
    { Ds_parser.INT (int_of_string text) }
  
  | ident_start ident_rest* as name
    { Ds_parser.IDENT name }
  
  | eof 
    { Ds_parser.EOF }
  
  | _ as c 
    { raise 
      (Error
        (Printf.sprintf
          "unexpected character: %C" c)) }