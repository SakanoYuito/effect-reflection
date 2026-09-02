type scope = {
  cont_var : Cps.name;
  meta_var : Cps.name;
}

type error = 
  | Unexpected_cont_var of Cps.name
  | Unexpected_meta_var of Cps.name
  | Free_handler_var of Cps.name

let ( let* ) = Result.bind

let rec value = function
  (* x♮ = x *)
  | Cps.Var x -> Ok (Ds.Var x)

  (* n♮ = n *)
  | Cps.Int n -> Ok (Ds.Int n)

  (* (\x. \j. \m. p)♮ -> \x. p# *)
  | Cps.Lam (x, j, m, p) -> 
      let scope = {
        cont_var = j;
        meta_var = m;
      } in 
      let* body = term scope p in Ok (Ds.Lam (x, body))

and apply_frame k p = 
  match k with
  (* (\v. \j. \m. q)♭[p] 
   = let v = p in q *)
  | Cps.Frame (v, j, m, q) -> 
      let body_scope = {
        cont_var = j;
        meta_var = m;
      } in 
      let* body = term body_scope q in 
      Ok (Ds.Let (v, p, body))

and apply_cont scope j p = 
  match j with
  (* eps♭♭[p] = p *)
  | Cps.Eps -> Ok p
  (* k♭♭[p] = p *)
  | Cps.CVar name when name = scope.cont_var -> Ok p
  | Cps.CVar name -> Error (Unexpected_cont_var name)
  (* (k :: j)♭♭[p] = j♭♭[ k♭[p] ] *)
  | Cps.Cons (k, j) ->
      let* p' = apply_frame k p in 
      apply_cont scope j p'

and apply_metacont scope m p = 
  match m with
  (* ()##[p] = p *)
  | Cps.Empty -> Ok p
  (* m##[p] = p *)
  | Cps.MVar m when m = scope.meta_var -> Ok p
  | Cps.MVar m -> Error (Unexpected_meta_var m)
  (* (<j, h> :: m)##[p]
   = m##[ j♭♭ [handle p with h♪] ] *)
  | Cps.MCons (j, h, m) ->
      let* x, k, q = handler h in 
      let handled = Ds.Handle (p, x, k, q) in
      let* j_applied = apply_cont scope j handled in  (* j♭♭[handle ...] *)
      apply_metacont scope m j_applied                (* m##[ ... ]*)
  
and handler = function
  | Cps.HVar h -> Error (Free_handler_var h)
  (* (\v. \r. \j. \m. p)♪ = v, r -> p# *)
  | Cps.Handler (v, r, j, m, p) ->
      let body_scope = {
        cont_var = j;
        meta_var = m;
      } in 
      let* body = term body_scope p in Ok (v, r, body)
  
and term scope = function
  (* (j v m)# = m##[ j♭♭ [return v♮] ] *)
  | Cps.Send (j, v, m) ->
      let* v' = value v in 
      let base = Ds.Return v' in
      let* with_cont = apply_cont scope j base in
      apply_metacont scope m with_cont
  
  (* (j (v + w) m)# = m##[ j♭♭ [v♮ + w♮] ] *)
  | Cps.Add (j, v, w, m) ->
      let* v' = value v in 
      let* w' = value w in 
      let base = Ds.Add (v', w') in
      let* with_cont = apply_cont scope j base in
      apply_metacont scope m with_cont
  
  (* (v w j m)# = m##[ j♭♭ [v♮ w♮] ] *)
  | Cps.App (v, w, j, m) ->
      let* v' = value v in 
      let* w' = value w in 
      let base = Ds.App (v', w') in
      let* with_cont = apply_cont scope j base in
      apply_metacont scope m with_cont
  
  (* (m @ v j)# = m## [ j♭♭ [op v♮] ] *)
  | Cps.Op (m, v, j) ->
      let* v' = value v in 
      let base = Ds.Op v' in
      let* with_cont = apply_cont scope j base in 
      apply_metacont scope m with_cont

let root = function
  | Cps.Root (j, m, p) ->
      term {cont_var = j; meta_var = m;} p
