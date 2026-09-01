type name = string

(* 
DS Syntax

Values       V, W ::= x | n | \x. P
Computations P, Q ::= return V
                    | V W
                    | V + W
                    | let x = P in Q
                    | handle P with x, k -> Q
                    | op V

*)


type value =
  | Var of name
  | Int of int
  | Lam of name * comp

and comp =
  | Return of value
  | App of value * value
  | Add of value * value
  | Let of name * comp * comp
  | Handle of comp * name * name * comp
  | Op of value