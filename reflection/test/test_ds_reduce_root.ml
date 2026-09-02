open Reflection

let string_of_rule = function
  | Ds_reduce_root.Beta_value -> "beta.v"
  | Ds_reduce_root.Beta_let -> "beta.let"
  | Ds_reduce_root.Eta_value -> "eta.v"
  | Ds_reduce_root.Eta_let -> "eta.let"
  | Ds_reduce_root.Delta_add -> "delta.+"
  | Ds_reduce_root.Handler_return -> "h.return"
  | Ds_reduce_root.Beta_op -> "beta.op.S"
  | Ds_reduce_root.Assoc -> "assoc"

let check_step label expected_rule expected_reduct source =
  match Ds_reduce_root.contract (Fresh.create ()) source with
  | None ->
      failwith (label ^ ": expected a root reduction, but the term is stuck")
  | Some actual ->
      if actual.rule <> expected_rule then
        failwith
          (Printf.sprintf
             "%s: expected rule %s, but got %s"
             label
             (string_of_rule expected_rule)
             (string_of_rule actual.rule));
      if actual.reduct <> expected_reduct then
        failwith
          (Printf.sprintf
             "%s:\nexpected:\n%s\nactual:\n%s"
             label
             (Format.asprintf "%a" Ds_pretty.pp_comp expected_reduct)
             (Format.asprintf "%a" Ds_pretty.pp_comp actual.reduct))

let check_stuck label source =
  match Ds_reduce_root.contract (Fresh.create ()) source with
  | None -> ()
  | Some actual ->
      failwith
        (Printf.sprintf
           "%s: expected no root reduction, but %s applied"
           label
           (string_of_rule actual.rule))

let test_beta_value () =
  check_step
    "beta.v"
    Ds_reduce_root.Beta_value
    (Ds.Add (Ds.Int 1, Ds.Int 2))
    (Ds.App
       (Ds.Lam ("x", Ds.Add (Ds.Var "x", Ds.Int 2)),
        Ds.Int 1))

let test_eta_value () =
  let source =
    Ds.Lam
      ("x",
       Ds.App (Ds.Var "f", Ds.Var "x"))
  in
  match Ds_reduce_root.contract_value source with
  | [{ rule = Ds_reduce_root.Eta_value; reduct = Ds.Var "f" }] -> ()
  | _ -> failwith "eta.v: expected lambda x. f x to reduce to f"

let test_eta_value_side_condition () =
  let source =
    Ds.Lam
      ("x",
       Ds.App (Ds.Var "x", Ds.Var "x"))
  in
  match Ds_reduce_root.contract_value source with
  | [] -> ()
  | _ -> failwith "eta.v ignored the free-variable side condition"

let rules_of_comp source =
  Ds_reduce_root.contract_comp (Fresh.create ()) source
  |> List.map
       (fun (step : Ds_reduce_root.step) -> step.rule)

let test_contract_comp_lists_beta_eta_overlap () =
  let source =
    Ds.Let
      ("x",
       Ds.Return (Ds.Int 1),
       Ds.Return (Ds.Var "x"))
  in
  let expected =
    [Ds_reduce_root.Beta_let; Ds_reduce_root.Eta_let]
  in
  if rules_of_comp source <> expected then
    failwith "contract_comp did not return both beta.let and eta.let"

let test_contract_comp_lists_eta_assoc_overlap () =
  let source =
    Ds.Let
      ("x",
       Ds.Let
         ("y",
          Ds.Return (Ds.Int 1),
          Ds.Return (Ds.Var "y")),
       Ds.Return (Ds.Var "x"))
  in
  let expected =
    [Ds_reduce_root.Eta_let; Ds_reduce_root.Assoc]
  in
  if rules_of_comp source <> expected then
    failwith "contract_comp did not return both eta.let and assoc"

let test_beta_let () =
  check_step
    "beta.let"
    Ds_reduce_root.Beta_let
    (Ds.Add (Ds.Int 1, Ds.Int 2))
    (Ds.Let
       ("x",
        Ds.Return (Ds.Int 1),
        Ds.Add (Ds.Var "x", Ds.Int 2)))

let test_eta_let () =
  let p = Ds.Op (Ds.Int 1) in
  check_step
    "eta.let"
    Ds_reduce_root.Eta_let
    p
    (Ds.Let ("x", p, Ds.Return (Ds.Var "x")))

let test_delta_add () =
  check_step
    "delta.+"
    Ds_reduce_root.Delta_add
    (Ds.Return (Ds.Int 42))
    (Ds.Add (Ds.Int 20, Ds.Int 22))

let test_handler_return () =
  check_step
    "h.return"
    Ds_reduce_root.Handler_return
    (Ds.Return (Ds.Int 1))
    (Ds.Handle
       (Ds.Return (Ds.Int 1),
        "x", "k",
        Ds.App (Ds.Var "k", Ds.Var "x")))

let test_assoc () =
  let source =
    Ds.Let
      ("x",
       Ds.Let
         ("y",
          Ds.Return (Ds.Int 1),
          Ds.Add (Ds.Var "y", Ds.Int 2)),
       Ds.Add (Ds.Var "x", Ds.Int 3))
  in
  let expected =
    Ds.Let
      ("y",
       Ds.Return (Ds.Int 1),
       Ds.Let
         ("x",
          Ds.Add (Ds.Var "y", Ds.Int 2),
          Ds.Add (Ds.Var "x", Ds.Int 3)))
  in
  check_step "assoc" Ds_reduce_root.Assoc expected source

let test_assoc_side_condition () =
  let source =
    Ds.Let
      ("x",
       Ds.Let
         ("y",
          Ds.Return (Ds.Int 1),
          Ds.Return (Ds.Var "y")),
       Ds.Add (Ds.Var "y", Ds.Int 3))
  in
  check_stuck "assoc side condition y not in fv(R)" source

let test_beta_op () =
  let source =
    Ds.Handle
      (Ds.Op (Ds.Int 1),
       "x", "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  let resumption =
    Ds.Lam
      ("y0",
       Ds.Return (Ds.Var "y0"))
  in
  let expected =
    Ds.App (resumption, Ds.Int 1)
  in
  check_step "beta.op.S" Ds_reduce_root.Beta_op expected source

let test_beta_op_nested_context () =
  let handled =
    Ds.Let
      ("v",
       Ds.Let
         ("w",
          Ds.Op (Ds.Int 1),
          Ds.Add (Ds.Var "w", Ds.Int 2)),
       Ds.Add (Ds.Var "v", Ds.Int 3))
  in
  let source =
    Ds.Handle
      (handled,
       "x", "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  let resumption =
    Ds.Lam
      ("y0",
       Ds.Let
         ("v",
          Ds.Let
            ("w",
             Ds.Return (Ds.Var "y0"),
             Ds.Add (Ds.Var "w", Ds.Int 2)),
          Ds.Add (Ds.Var "v", Ds.Int 3)))
  in
  let expected =
    Ds.App (resumption, Ds.Int 1)
  in
  check_step
    "beta.op.S with nested pure context"
    Ds_reduce_root.Beta_op
    expected
    source

let () =
  test_beta_value ();
  test_eta_value ();
  test_eta_value_side_condition ();
  test_contract_comp_lists_beta_eta_overlap ();
  test_contract_comp_lists_eta_assoc_overlap ();
  test_beta_let ();
  test_eta_let ();
  test_delta_add ();
  test_handler_return ();
  test_assoc ();
  test_assoc_side_condition ();
  test_beta_op ();
  test_beta_op_nested_context ()
