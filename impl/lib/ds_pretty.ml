let rec pp_value fmt v = 
  match v with
  | Ds.Var x -> Format.fprintf fmt "%s" x
  | Ds.Int n -> Format.fprintf fmt "%d" n
  | Ds.Lam (x, p) -> Format.fprintf fmt "(λ%s. %a)" x pp_comp p

and pp_comp fmt p = 
  match p with
  | Ds.Return v -> Format.fprintf fmt "return %a" pp_value v 
  | Ds.App (v, w) -> Format.fprintf fmt "%a %a" pp_value v pp_value w
  | Ds.Add (v, w) -> Format.fprintf fmt "%a + %a" pp_value v pp_value w
  | Ds.Let (x, p, q) -> 
      Format.fprintf fmt
        "@[<hov>let %s = %a in@ %a@]"
        x pp_let_rhs p pp_comp q
  | Ds.Handle (p, x, k, q) ->
      Format.fprintf fmt
        "@[<v>@[<v 2>handle@,%a@]@,@[<v 2>with %s, %s ->@,%a@]@]"
        pp_comp p x k pp_comp q 
  | Ds.Op v -> Format.fprintf fmt "op %a" pp_value v

and pp_let_rhs fmt = function
  | Ds.Let _ as p ->
      Format.fprintf fmt "(@[%a@])" pp_comp p
  | p ->
      pp_comp fmt p

  
