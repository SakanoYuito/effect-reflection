type t = {
  values   : Name_set.t;
  conts    : Name_set.t;
  metas    : Name_set.t;
  handlers : Name_set.t;
}

let empty = {
  values   = Name_set.empty;
  conts    = Name_set.empty;
  metas    = Name_set.empty;
  handlers = Name_set.empty;
}

let union fv1 fv2 = {
  values   = Name_set.union fv1.values   fv2.values;
  conts    = Name_set.union fv1.conts    fv2.conts;
  metas    = Name_set.union fv1.metas    fv2.metas;
  handlers = Name_set.union fv1.handlers fv2.handlers;
}

let union3 fv1 fv2 fv3 = union fv1 (union fv2 fv3)
let union4 fv1 fv2 fv3 fv4 = union fv1 (union fv2 (union fv3 fv4))

let singleton_value x = {
  empty with values = Name_set.singleton x;
}

let singleton_cont j = {
  empty with conts = Name_set.singleton j;
}

let singleton_meta m = {
  empty with metas = Name_set.singleton m;
}

let singleton_handler h = {
  empty with handlers = Name_set.singleton h;
}

let rec value = function
  | Cps.Var x -> singleton_value x
  | Cps.Int _ -> empty
  | Cps.Lam (x, j, m, p) -> 
      let fv = term p in
      {
        fv with
        values = Name_set.remove x fv.values;
        conts  = Name_set.remove j fv.conts;
        metas  = Name_set.remove m fv.metas;
      }

and frame = function
  | Cps.Frame (v, j, m, p) -> 
      let fv = term p in
      {
        fv with
        values = Name_set.remove v fv.values;
        conts  = Name_set.remove j fv.conts;
        metas  = Name_set.remove m fv.metas;
      }

and cont = function
  | Cps.CVar j -> singleton_cont j
  | Cps.Eps -> empty
  | Cps.Cons (k, j) -> union (frame k) (cont j)

and metacont = function
  | Cps.MVar m -> singleton_meta m
  | Cps.Empty -> empty
  | Cps.MCons (j, h, m) -> union3 (cont j) (handler h) (metacont m)

and handler = function
  | Cps.HVar h -> singleton_handler h 
  | Cps.Handler (v, r, j, m, p) ->
      let fv = term p in
      {
        fv with
        values = fv.values |> Name_set.remove v
                           |> Name_set.remove r;
        conts  = Name_set.remove j fv.conts;
        metas  = Name_set.remove m fv.metas;
      }

and term = function
  | Cps.Send (j, v, m) -> 
      union3 (cont j) (value v) (metacont m)
  | Cps.Add (j, v, w, m) -> 
      union4 (cont j) (value v) (value w) (metacont m)
  | Cps.App (v, w, j, m) ->
      union4 (value v) (value w) (cont j) (metacont m)
  | Cps.Op (m, v, j) -> 
      union3 (metacont m) (value v) (cont j)

and root = function
  | Cps.Root (j, m, p) -> 
      let fv = term p in
      {
        fv with
        conts  = Name_set.remove j fv.conts;
        metas  = Name_set.remove m fv.metas;
      }
