type rule = 
  | Beta_value
  | Beta_let
  | Eta_value
  | Eta_let
  | Delta_add
  | Handler_return
  | Beta_op
  | Assoc

type 'a reduction = {
  rule : rule;
  reduct : 'a;
}

type value_step = Ds.value reduction
type step = Ds.comp reduction

(* [eta.v]
   \x. V x -> V
   if x is not free in V *)
let contract_eta_value = function
  | Ds.Lam (x, Ds.App (v, Ds.Var x'))
    when x = x' && Ds_free_vars.not_free_in_value x v ->
      Some { rule = Eta_value; reduct = v }
  | _ ->
      None

let contract_value value =
  List.filter_map
    Fun.id
    [contract_eta_value value]

(* [beta.v]
   (\x. p) v -> p[v/x] *)
let contract_beta_value supply = function
  | Ds.App (Ds.Lam (x, p), v) -> 
      Some {
        rule   = Beta_value;
        reduct = Ds_subst.comp supply ~var:x ~by:v p;
      }
  | _ ->
      None

(* [beta.let]
   let x = return v in p -> p[v/x] *)
let contract_beta_let supply = function
  | Ds.Let (x, Ds.Return v, p) -> 
      Some {
        rule   = Beta_let;
        reduct = Ds_subst.comp supply ~var:x ~by:v p;
      }
  | _ ->
      None

(* [eta.let]
   let x = p in return x -> p *)
let contract_eta_let = function
  | Ds.Let (x, p, Ds.Return (Ds.Var y)) when x = y -> 
      Some {
        rule   = Eta_let;
        reduct = p;
      }
  | _ ->
      None

(* [delta.add]
   n1 + n2 -> return n *)
let contract_delta_add = function
  | Ds.Add (Ds.Int n1, Ds.Int n2) -> 
      Some {
        rule   = Delta_add;
        reduct = Ds.Return (Ds.Int (n1 + n2));
      }
  | _ ->
      None

(* [h.return]
   handle return v with x, k -> p -> return v *)
let contract_handler_return = function
  | Ds.Handle (Ds.Return v, _x, _k, _p) -> 
      Some {
        rule   = Handler_return;
        reduct = Ds.Return v;
      }
  | _ ->
      None

(* [beta.op.S]
   handle F[op v] with x, k -> q
     -> q[v/x, (\y. F[return y])/k] *)
let contract_beta_op supply = function
  | Ds.Handle (p, x, k, q) -> 
    begin match Ds_context.decompose_operation p with
    | None ->
        None
    | Some (f, v) ->
        let y = Fresh.name supply "y" in
        let res = Ds.Lam (y, Ds_context.plug f (Ds.Return (Ds.Var y))) in

        let x' = Fresh.name supply x in
        let k' = Fresh.name supply k in
        let q' =
          q
          |> Ds_subst.comp supply ~var:x ~by:(Ds.Var x')
          |> Ds_subst.comp supply ~var:k ~by:(Ds.Var k')
        in
        let reduct =
          q'
          |> Ds_subst.comp supply ~var:x' ~by:v
          |> Ds_subst.comp supply ~var:k' ~by:res
        in
        Some { rule = Beta_op; reduct }
    end
  | _ ->
      None

(* [assoc]
   let x = (let y = p in q) in r
     -> let y = p in let x = q in r
   if y is not free in r *)
let contract_assoc = function
  | Ds.Let (x, Ds.Let (y, p, q), r) when Ds_free_vars.not_free_in_comp y r ->
      Some {
        rule = Assoc;
        reduct = Ds.Let (y, p, Ds.Let (x, q, r));
      }
  | _ ->
      None

let contract_comp supply comp =
  List.filter_map
    Fun.id
    [ contract_beta_value supply comp;
      contract_beta_let supply comp;
      contract_eta_let comp;
      contract_delta_add comp;
      contract_handler_return comp;
      contract_beta_op supply comp;
      contract_assoc comp ]

(* Compatibility wrapper for the current deterministic root-step REPL. *)
let contract supply comp =
  match contract_comp supply comp with
  | step :: _ -> Some step
  | [] -> None
