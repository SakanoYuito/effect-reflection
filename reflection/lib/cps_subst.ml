type env = {
  values   : (Cps.name * Cps.value)    list;
  conts    : (Cps.name * Cps.cont)     list;
  metas    : (Cps.name * Cps.metacont) list;
  handlers : (Cps.name * Cps.handler)  list;
}

let empty = {
  values   = [];
  conts    = [];
  metas    = [];
  handlers = [];
}

let add_value x v env = {
  env with values = (x, v) :: env.values;
}

let remove_value x env = {
  env with values = List.remove_assoc x env.values;
}

let add_cont j j' env = {
  env with conts = (j, j') :: env.conts;
}

let remove_cont j env = {
  env with
  conts =
    List.remove_assoc j env.conts;
}

let add_meta m m' env = {
  env with metas = (m, m') :: env.metas;
}

let remove_meta m env = {
  env with
  metas =
    List.remove_assoc m env.metas;
}

let add_handler h h' env = {
  env with handlers = (h, h') :: env.handlers;
}

let remove_handler h env = {
  env with
  handlers =
    List.remove_assoc h env.handlers;
}

let range_fv env = 
  let fv_value = List.fold_left 
    (fun acc (_, v) -> Cps_free_vars.union acc (Cps_free_vars.value v)) 
    Cps_free_vars.empty
    env.values in 
  let fv_cont = List.fold_left 
    (fun acc (_, j) -> Cps_free_vars.union acc (Cps_free_vars.cont j)) 
    Cps_free_vars.empty
    env.conts in
  let fv_meta = List.fold_left 
    (fun acc (_, m) -> Cps_free_vars.union acc (Cps_free_vars.metacont m)) 
    Cps_free_vars.empty
    env.metas in
  let fv_handler = List.fold_left 
    (fun acc (_, h) -> Cps_free_vars.union acc (Cps_free_vars.handler h)) 
    Cps_free_vars.empty
    env.handlers in
  Cps_free_vars.union4 fv_value fv_cont fv_meta fv_handler

let rec value supply env = function
  | Cps.Var x -> 
      begin 
        match List.assoc_opt x env.values with
        | Some v -> v
        | None -> Cps.Var x
      end
  | Cps.Int n -> Cps.Int n
  | Cps.Lam (x, j, m, p) -> 
      let env_body = env |> remove_value x |> remove_cont j |> remove_meta m in
      let fvs = range_fv env_body in 
      let x' = if Name_set.mem x fvs.values    then Fresh.name supply x else x in
      let j' = if Name_set.mem j fvs.conts     then Fresh.name supply j else j in
      let m' = if Name_set.mem m fvs.metas     then Fresh.name supply m else m in
      let env_alpha = {
        empty with
        values   = [(x, Cps.Var  x')];
        conts    = [(j, Cps.CVar j')];
        metas    = [(m, Cps.MVar m')];
      } in 
      let p' = term supply env_alpha p in 
      Cps.Lam (x', j', m', term supply env_body p')

and frame supply env = function
  | Cps.Frame (v, j, m, p) -> 
      let env_body = env |> remove_value v |> remove_cont j |> remove_meta m in
      let fvs = range_fv env_body in 
      let v' = if Name_set.mem v fvs.values then Fresh.name supply v else v in
      let j' = if Name_set.mem j fvs.conts  then Fresh.name supply j else j in
      let m' = if Name_set.mem m fvs.metas  then Fresh.name supply m else m in
      let env_alpha = {
        empty with
        values = [(v, Cps.Var  v')];
        conts  = [(j, Cps.CVar j')];
        metas  = [(m, Cps.MVar m')];
      } in 
      let p' = term supply env_alpha p in 
      Cps.Frame (v', j', m', term supply env_body p')

and cont supply env = function
  | Cps.CVar j -> 
      begin 
        match List.assoc_opt j env.conts with
        | Some j -> j
        | None   -> Cps.CVar j
      end
  | Cps.Eps -> Cps.Eps
  | Cps.Cons (k, j) -> Cps.Cons (frame supply env k, cont supply env j)

and metacont supply env = function
  | Cps.MVar m ->
      begin
        match List.assoc_opt m env.metas with
        | Some m -> m
        | None   -> Cps.MVar m
      end
  | Cps.Empty -> Cps.Empty
  | Cps.MCons (j, h, m) -> Cps.MCons (cont supply env j, handler supply env h, metacont supply env m)

and handler supply env = function
  | Cps.HVar h -> 
      begin
        match List.assoc_opt h env.handlers with
        | Some h -> h
        | None   -> Cps.HVar h
      end
  | Cps.Handler (v, r, j, m, p) ->
      let env_body = env |> remove_value v 
                         |> remove_value r
                         |> remove_cont j 
                         |> remove_meta m  in
      let fvs = range_fv env_body in 
      let v' = if Name_set.mem v fvs.values then Fresh.name supply v else v in
      let r' = if Name_set.mem r fvs.values then Fresh.name supply r else r in
      let j' = if Name_set.mem j fvs.conts  then Fresh.name supply j else j in
      let m' = if Name_set.mem m fvs.metas  then Fresh.name supply m else m in
      let env_alpha = {
        empty with
        values = [(v, Cps.Var  v'); 
                  (r, Cps.Var  r')];
        conts  = [(j, Cps.CVar j')];
        metas  = [(m, Cps.MVar m')];
      } in 
      let p' = term supply env_alpha p in 
      Cps.Handler (v', r', j', m', term supply env_body p')
  
and term supply env = function
  | Cps.Send (j, v, m) ->
      Cps.Send (cont     supply env j,
                value    supply env v,
                metacont supply env m)
  | Cps.Add (j, v, w, m) ->
      Cps.Add (cont     supply env j,
               value    supply env v,
               value    supply env w,
               metacont supply env m)
  | Cps.App (v, w, j, m) ->
      Cps.App (value    supply env v,
               value    supply env w,
               cont     supply env j,
               metacont supply env m)
  | Cps.Op (m, v, j) ->
      Cps.Op (metacont supply env m,
              value    supply env v,
              cont     supply env j)

and root supply env = function
  | Cps.Root (j, m, p) ->
      let env_body = env |> remove_cont j |> remove_meta m in
      let fvs = range_fv env_body in 
      let j' = if Name_set.mem j fvs.conts     then Fresh.name supply j else j in
      let m' = if Name_set.mem m fvs.metas     then Fresh.name supply m else m in
      let env_alpha = {
        empty with
        conts    = [(j, Cps.CVar j')];
        metas    = [(m, Cps.MVar m')];
      } in 
      let p' = term supply env_alpha p in 
      Cps.Root (j', m', term supply env_body p')
