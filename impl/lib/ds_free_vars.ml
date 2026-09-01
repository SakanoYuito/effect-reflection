let union = Name_set.union

let rec value = function
  | Ds.Var x      -> Name_set.singleton x
  | Ds.Int _      -> Name_set.empty
  | Ds.Lam (x, p) -> Name_set.remove x (comp p)

and comp = function
  | Ds.Return v            -> value v
  | Ds.App (v, w)          -> union (value v) (value w)
  | Ds.Add (v, w)          -> union (value v) (value w)
  | Ds.Let (x, p, q)       -> union (comp p) (comp q 
                                              |> Name_set.remove x)
  | Ds.Handle (p, x, k, q) -> union (comp p) (comp q 
                                              |> Name_set.remove x
                                              |> Name_set.remove k)
  | Ds.Op v                -> value v

let free_in_value x v =
  Name_set.mem x (value v)

let free_in_comp x p =
  Name_set.mem x (comp p)

let not_free_in_value x v =
  not (free_in_value x v)

let not_free_in_comp x p =
  not (free_in_comp x p)