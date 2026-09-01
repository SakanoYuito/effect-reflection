type rule = 
  | Beta_value
  | Beta_let
  | Eta_value
  | Eta_let
  | Delta_add
  | Handler_return
  | Beta_op_shallow
  | Assoc

type 'a reduction = {
  rule   : rule;
  reduct : 'a;
}

type value_step = Cps.value reduction
type cont_step = Cps.cont reduction
type step = Cps.term reduction

(* [eta.v]
   \x. \j. \m. V x j m -> V
   if x, j, and m are not free in V *)
let contract_eta_value = function
  | Cps.Lam
      (x, j, m,
       Cps.App
         (v,
          Cps.Var x',
          Cps.CVar j',
          Cps.MVar m'))
    when x = x' && j = j' && m = m' ->
      let fv = Cps_free_vars.value v in
      if Name_set.mem x fv.values
         || Name_set.mem j fv.conts
         || Name_set.mem m fv.metas
      then
        None
      else
        Some { rule = Eta_value; reduct = v }

  | _ ->
      None

let contract_value value =
  List.filter_map
    Fun.id
    [contract_eta_value value]

let rec append_endpoint captured tail =
  match captured with
  | Cps.CVar _ -> None
  | Cps.Eps -> Some tail
  | Cps.Cons (k, j) ->
      Option.map 
        (fun appended -> Cps.Cons (k, appended))
        (append_endpoint j tail)


(* (\v. \j. \m. P) ▷ k2 = \v'. \j'. \m'. P[v'/v, (K2 :: j')/j], m'/m *)
let compose_frames supply (Cps.Frame (v, j, m, p)) k2 =
  let v' = Fresh.name supply "v" in
  let j' = Fresh.name supply "j" in
  let m' = Fresh.name supply "m" in

  let env = Cps_subst.empty 
         |> Cps_subst.add_value v (Cps.Var v')
         |> Cps_subst.add_cont  j (Cps.Cons (k2, Cps.CVar j'))
         |> Cps_subst.add_meta  m (Cps.MVar m') in 
  Cps.Frame (v', j', m', Cps_subst.term supply env p)

(* [assoc] k1 :: k2 :: j -> (k1 ▷ k2) :: j *)
let contract_assoc supply = function
  | Cps.Cons (k1, Cps.Cons (k2, j)) ->
      Some {
        rule = Assoc;
        reduct = Cps.Cons (compose_frames supply k1 k2, j);
      }
  | _ -> None

(* [eta.cont] (\v. \j. \m. j v m) :: J -> J *)
let contract_eta_let = function
  | Cps.Cons (Cps.Frame (v, j, m, Cps.Send (Cps.CVar j', Cps.Var v', Cps.MVar m')), js)
      when v = v' && j = j' && m = m' ->
      Some { rule = Eta_let; reduct = js }
  | _ -> None

let contract_cont supply cont =
  List.filter_map
    Fun.id
    [ contract_eta_let cont;
      contract_assoc supply cont ]

let rewrite_current_cont rewrite = function
  | Cps.Send (j, v, m) -> Option.map (fun j' -> Cps.Send (j', v, m)) (rewrite j)
  | Cps.Add (j, v, w, m) -> Option.map (fun j' -> Cps.Add (j', v, w, m)) (rewrite j)
  | Cps.App (v, w, j, m) -> Option.map (fun j' -> Cps.App (v, w, j', m)) (rewrite j)
  | Cps.Op (m, v, j) -> Option.map (fun j' -> Cps.Op (m, v, j')) (rewrite j)

let contract_current_assoc supply term =
  Option.map
    (fun reduct -> {
        rule = Assoc;
        reduct;
      })
    (rewrite_current_cont
       (fun cont ->
         Option.map
           (fun (step : cont_step) -> step.reduct)
           (contract_assoc supply cont))
       term)

let contract_current_eta_let term =
  Option.map
    (fun reduct -> {
        rule = Eta_let;
        reduct;
      })
    (rewrite_current_cont
       (fun cont ->
         Option.map
           (fun (step : cont_step) -> step.reduct)
           (contract_eta_let cont))
       term)

(* [beta.v]
   (\x. \j. \m. P) x' j' m'
     -> P[x'/x, j'/j, m'/m] *)
let contract_beta_value supply = function
  | Cps.App (Cps.Lam (x, j, m, p), x', j', m') ->
      let env =
        Cps_subst.empty
        |> Cps_subst.add_value x x'
        |> Cps_subst.add_cont j j'
        |> Cps_subst.add_meta m m'
      in
      Some {
        rule = Beta_value;
        reduct = Cps_subst.term supply env p;
      }
  | _ ->
      None

(* [beta.let]
   ((\v. \j. \m. P) :: js) v' m'
     -> P[v'/v, js/j, m'/m] *)
let contract_beta_let supply = function
  | Cps.Send
      (Cps.Cons (Cps.Frame (v, j, m, p), js), v', m') ->
      let env =
        Cps_subst.empty
        |> Cps_subst.add_value v v'
        |> Cps_subst.add_cont j js
        |> Cps_subst.add_meta m m'
      in
      Some {
        rule = Beta_let;
        reduct = Cps_subst.term supply env p;
      }
  | _ ->
      None

(* [delta.add]
   j (n1 + n2) m -> j n m *)
let contract_delta_add = function
  | Cps.Add (j, Cps.Int n1, Cps.Int n2, m) ->
      Some {
        rule = Delta_add;
        reduct = Cps.Send (j, Cps.Int (n1 + n2), m);
      }
  | _ ->
      None

(* [h.return]
   eps v (<j, h> :: m) -> j v m *)
let contract_handler_return = function
  | Cps.Send (Cps.Eps, v, Cps.MCons (j, _h, m)) ->
      Some {
        rule = Handler_return;
        reduct = Cps.Send (j, v, m);
      }
  | _ ->
      None

(* [beta.op.S]
   (<j0, \v. \r. \j0. \m0. P> :: m0) @ v j
     -> P[v/v, r/r, j0/j0, m0/m0]
   where r = \y. \j1. \m1. (j ++ j1) y m1 *)
let contract_beta_op_shallow supply = function
  | Cps.Op
      (Cps.MCons (j0', Cps.Handler (v, r, j0, m0, p), m0'), v', j') ->
      let y = Fresh.name supply "y" in
      let j1 = Fresh.name supply "j" in
      let m1 = Fresh.name supply "m" in
      begin match append_endpoint j' (Cps.CVar j1) with
      | None ->
          None
      | Some j_res ->
          let r_body = Cps.Send (j_res, Cps.Var y, Cps.MVar m1) in
          let r' = Cps.Lam (y, j1, m1, r_body) in
          let env =
            Cps_subst.empty
            |> Cps_subst.add_value v v'
            |> Cps_subst.add_value r r'
            |> Cps_subst.add_cont j0 j0'
            |> Cps_subst.add_meta m0 m0'
          in
          Some {
            rule = Beta_op_shallow;
            reduct = Cps_subst.term supply env p;
          }
      end
  | _ ->
      None

let contract_term supply term =
  List.filter_map
    Fun.id
    [ contract_beta_value supply term;
      contract_beta_let supply term;
      contract_delta_add term;
      contract_handler_return term;
      contract_beta_op_shallow supply term ]

(* Compatibility wrapper for the current deterministic root-step REPL. *)
let contract supply term =
  match contract_term supply term with
  | step :: _ -> Some step
  | [] -> None
