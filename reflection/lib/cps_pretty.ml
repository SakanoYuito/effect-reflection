let rec pp_root fmt r = 
  match r with
  | Cps.Root (j, m, p) -> 
      Format.fprintf fmt "@[<v 2>λ%s. λ%s.@,%a@]" j m pp_term p 

and pp_value fmt v = 
  match v with
  | Cps.Var x -> Format.fprintf fmt "%s" x
  | Cps.Int n -> Format.fprintf fmt "%d" n
  | Cps.Lam (x, j, m, p) -> 
      Format.fprintf fmt
        "@[<hov 2>(λ%s. λ%s. λ%s.@ %a)@]"
        x j m pp_term p 

and pp_frame fmt k = 
  match k with
  | Cps.Frame (v, j, m, p) ->
      Format.fprintf fmt
        "@[<hov 2>(λ%s. λ%s. λ%s.@ %a)@]"
        v j m pp_term p 


and pp_cont fmt j = 
  match j with
  | Cps.CVar j -> Format.fprintf fmt "%s" j 
  | Cps.Eps    -> Format.fprintf fmt "ε"
  | Cps.Cons (k, js) -> 
      Format.fprintf fmt "@[<hov 2>%a ::@ %a@]" pp_frame k pp_cont js

and pp_cont_argument fmt = function
  | (Cps.CVar _ | Cps.Eps) as j ->
      pp_cont fmt j
  | Cps.Cons _ as j ->
      Format.fprintf fmt "(@[%a@])" pp_cont j

and pp_handler fmt h = 
  match h with
  | Cps.HVar h -> Format.fprintf fmt "%s" h 
  | Cps.Handler (v, r, j0, m0, p) ->
      Format.fprintf fmt
        "@[<hov 2>(λ%s. λ%s. λ%s. λ%s.@ %a)@]"
        v r j0 m0 pp_term p

and pp_metacont fmt m = 
  match m with
  | Cps.MVar m -> Format.fprintf fmt "%s" m
  | Cps.Empty  -> Format.fprintf fmt "()"
  | Cps.MCons (j, h, m) ->
      Format.fprintf fmt "@[<hov 2><%a,@ %a> ::@ %a@]"
        pp_cont j pp_handler h pp_metacont m

and pp_metacont_argument fmt = function
  | (Cps.MVar _ | Cps.Empty) as m ->
      pp_metacont fmt m
  | Cps.MCons _ as m ->
      Format.fprintf fmt "(@[%a@])" pp_metacont m
 
and pp_term fmt p = 
  match p with
  | Cps.Send (j, v, m) -> 
      Format.fprintf fmt "@[<hov 2>%a@ %a@ %a@]"
        pp_cont_argument j pp_value v pp_metacont_argument m
  | Cps.Add (j, v, w, m) ->
      Format.fprintf fmt "@[<hov 2>%a@ (%a + %a)@ %a@]"
        pp_cont_argument j pp_value v pp_value w pp_metacont_argument m
  | Cps.App (v, w, j, m) ->
      Format.fprintf fmt "@[<hov 2>%a@ %a@ %a@ %a@]"
        pp_value v pp_value w pp_cont_argument j pp_metacont_argument m
  | Cps.Op (m, v, j) ->
      Format.fprintf fmt "@[<hov 2>%a @@ %a@ %a@]"
        pp_metacont_argument m pp_value v pp_cont_argument j
