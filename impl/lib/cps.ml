type name = string

(* 
CPS Syntax

Root           R ::= \j. \m. P
Values      V, W ::= x | n | \x. \j. \m. P
Cont. Frame    K ::= \v. \j. \m. P
Cont. Stack    J ::= j | ϵ | K :: J
Handler        H ::= h | \v. \r. \j0. \m0. P
Metacont.      M ::= m | ∙ | <J, H> :: M
Term           P ::= J V M
                   | J (V + W) M
                   | V W J M
                   | M @ V J
*)

type root =
  | Root of name * name * term

and value =
  | Var of name
  | Int of int
  | Lam of name * name * name * term

and frame =
  | Frame of name * name * name * term

and cont = 
  | CVar of name
  | Eps
  | Cons of frame * cont

and handler = 
  | HVar of name
  | Handler of name * name * name * name * term

and metacont =
  | MVar of name
  | Empty
  | MCons of cont * handler * metacont

and term = 
  | Send of cont * value * metacont
  | Add  of cont * value * value * metacont
  | App  of value * value * cont * metacont
  | Op   of metacont * value * cont

