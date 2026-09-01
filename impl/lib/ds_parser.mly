%token RETURN
%token LET 
%token IN 
%token HANDLE
%token WITH
%token OP
%token FUN

%token PLUS
%token EQUAL
%token COMMA
%token ARROW
%token LPAREN
%token RPAREN
%token EOF

%token <string> IDENT
%token <int> INT

%start <Ds.comp> program

%%

program:
  | p = comp; EOF
    { p }

comp:
  | RETURN; v = value
    { Ds.Return v}
  | v = value; w = value
    { Ds.App (v, w) }
  | v = value; PLUS; w = value
    { Ds.Add (v, w) }
  | LET; x = IDENT; EQUAL; p = comp; IN; q = comp
    { Ds.Let (x, p, q) }
  | HANDLE; p = comp; WITH; x = IDENT; COMMA; k = IDENT; ARROW; q = comp
    { Ds.Handle (p, x, k, q) }
  | OP; v = value
    { Ds.Op v }
  | LPAREN; p = comp; RPAREN
    { p }

value:
  | x = IDENT
    { Ds.Var x }
  | n = INT
    { Ds.Int n }
  | FUN; x = IDENT; ARROW; p = comp
    { Ds.Lam (x, p) }
  | LPAREN; v = value; RPAREN
    { v }
