let rec value supply = function
  | Ds.Var x -> Cps.Var x
  | Ds.Int n -> Cps.Int n
  | Ds.Lam (x, p) ->
      let j = Fresh.name supply "j" in
      let m = Fresh.name supply "m" in
      Cps.Lam (x, j, m, comp supply p (Cps.CVar j) (Cps.MVar m))

and comp supply p j m = match p with
  | Ds.Return v -> Cps.Send (j, value supply v, m)
  | Ds.Add (v, w) -> Cps.Add (j, value supply v, value supply w, m)
  | Ds.App (v, w) -> Cps.App (value supply v, value supply w, j, m)
  | Ds.Op v -> Cps.Op (m, value supply v, j)

  (* let x = P in Q : J : M 
   = P : (Kq :: J) : M 
   where Kq = \v. \j. \m. Q[v/x] : j : m *)
  | Ds.Let (x, p, q) -> 
      let v  = Fresh.name supply "v" in
      let j' = Fresh.name supply "j" in
      let m' = Fresh.name supply "m" in 
      
      let q' = Ds_subst.comp supply ~var:x ~by:(Ds.Var v) q in 
      let kq_body = comp supply q' (Cps.CVar j') (Cps.MVar m') in 
      let kq = Cps.Frame (v, j', m', kq_body) in 
      comp supply p (Cps.Cons (kq, j)) m
  
  (* handle P with x, k -> Q : J : M 
   = P : ε : (<J, H> :: M)
   where H = \v. \r. \j0. \m0. Q[v/x, r/k] : j0 : m0 *)
  | Ds.Handle (p, x, k, q) -> 
      let v  = Fresh.name supply "v" in 
      let r  = Fresh.name supply "r" in 
      let j0 = Fresh.name supply "j" in 
      let m0 = Fresh.name supply "m" in 
      let q' = q |> Ds_subst.comp supply ~var:x ~by:(Ds.Var v)
                 |> Ds_subst.comp supply ~var:k ~by:(Ds.Var r) in
      let h_body = comp supply q' (Cps.CVar j0) (Cps.MVar m0) in
      let h = Cps.Handler (v, r, j0, m0, h_body) in
      comp supply p Cps.Eps (Cps.MCons (j, h, m))

let program supply p = 
  let j = Fresh.name supply "j" in 
  let m = Fresh.name supply "m" in 
  Cps.Root (j, m, comp supply p (Cps.CVar j) (Cps.MVar m))