let rec value supply ~var ~by = function
  (* x[by/x] = by *)
  | Ds.Var x when x = var -> by
  
  (* x[by/y] = x *)
  | Ds.Var x -> Ds.Var x
  
  (* n[by/x] = n *)
  | Ds.Int n -> Ds.Int n
  
  (* (λx. p)[by/x] = λx. p *)
  | Ds.Lam (x, p) when x = var -> Ds.Lam (x, p)

  (* if x ∈ fv(by), (λx. p)[by/y] = λx'. (p[x'/x])[by/y] *)
  | Ds.Lam (x, p) when (Name_set.mem x (Ds_free_vars.value by)) -> 
      let x' = Fresh.name supply x in 
      let p' = comp supply ~var:x ~by:(Ds.Var x') p in 
      Ds.Lam (x', comp supply ~var ~by p')

  (* if x ∉ fv(by), (λx. p)[by/y] = λx. (p[by/y]) *)
  | Ds.Lam (x, p) -> Ds.Lam (x, comp supply ~var ~by p)

and comp supply ~var ~by = function
  (* (return v)[by/var] = return (v[by/var]) *)
  | Ds.Return v -> Ds.Return (value supply ~var ~by v)

  (* (v w)[by/var] = v[by/var] w[by/var] *)
  | Ds.App (v, w) -> Ds.App 
                       (value supply ~var ~by v,
                        value supply ~var ~by w)

  (* (v + w)[by/var] = v[by/var] + w[by/var] *)
  | Ds.Add (v, w) -> Ds.Add 
                       (value supply ~var ~by v,
                        value supply ~var ~by w)

  (* (op v)[by/var] = op (v[by/var]) *)
  | Ds.Op v -> Ds.Op (value supply ~var ~by v)

  (* (let x = p in q)[by/x] 
    = let x = p[by/x] in q *)
  | Ds.Let (x, p, q) when x = var -> Ds.Let (x, comp supply ~var ~by p, q)

  (* (let x = p in q)[by/y] where x ∈ fv(by) 
    = let x' = p[by/y] in (q[x'/x])[by/y] *)
  | Ds.Let (x, p, q) when (Name_set.mem x (Ds_free_vars.value by)) ->
      let x' = Fresh.name supply x in
      let q' = comp supply ~var:x ~by:(Ds.Var x') q in
      Ds.Let (x',
              comp supply ~var ~by p,
              comp supply ~var ~by q')

  (* (let x = p in q)[by/y] where x ∉ fv(by) 
    = let x = p[by/y] in q[by/y] *)
  | Ds.Let (x, p, q) -> 
      Ds.Let (x,
              comp supply ~var ~by p,
              comp supply ~var ~by q)
  
  (* (handle p with x, k -> q)[by/x] (or ...[by/k])
    = handle p[by/x] with x, k -> p *)
  | Ds.Handle (p, x, k, q) when x = var || k = var ->
      Ds.Handle (comp supply ~var ~by p, x, k, q)

  (* (handle p with x, k -> q)[by/y] where x, k ∉ fv(by)
    = handle p[by/y] with x, k -> p[by/y] *)
  | Ds.Handle (p, x, k, q) 
    when Name_set.disjoint (Name_set.of_list [x; k]) (Ds_free_vars.value by) ->
      Ds.Handle (comp supply ~var ~by p,
                 x, k, 
                 comp supply ~var ~by q)

  (* (handle p with x, k -> q)[by/y] where x, k ∈ fv(by)
    = handle p[by/y] with x', k' -> (p[x'/x, k'/k])[by/y] *)
  | Ds.Handle (p, x, k, q) ->
    let by_fv = Ds_free_vars.value by in 
    let x' = if Name_set.mem x by_fv then Fresh.name supply x else x in 
    let k' = if Name_set.mem k by_fv then Fresh.name supply k else k in
    let q' = q |> comp supply ~var:x ~by:(Ds.Var x') 
               |> comp supply ~var:k ~by:(Ds.Var k') in
    Ds.Handle (comp supply ~var ~by p,
               x', k',
               comp supply ~var ~by q')


  