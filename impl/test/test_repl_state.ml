open Reflection

let get_ok label = function
  | Ok outcome -> outcome
  | Error _ -> failwith (label ^ ": unexpectedly failed")

let check_error label expected actual =
  match actual with
  | Error error when error = expected -> ()
  | Error _ -> failwith (label ^ ": returned a different error")
  | Ok _ -> failwith (label ^ ": unexpectedly succeeded")

let check_state label expected actual =
  if expected <> actual then
    failwith (label ^ ": returned an unexpected state")

let check_rule label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s: expected rule %s, but got %s"
         label
         (Option.value ~default:"<none>" expected)
         (Option.value ~default:"<none>" actual))

let test_ds_step () =
  let source =
    Repl_state.Ds_state (Ds.Add (Ds.Int 20, Ds.Int 22))
  in
  let actual =
    get_ok
      "DS step"
      (Repl_state.apply (Fresh.create ()) Repl_state.Ds_step source)
  in
  check_state
    "DS step"
    (Repl_state.Ds_state (Ds.Return (Ds.Int 42)))
    actual.state;
  check_rule "DS step" (Some "δ.+") actual.rule_name

let test_to_cps () =
  let source =
    Repl_state.Ds_state (Ds.Return (Ds.Int 1))
  in
  let actual =
    get_ok
      "to CPS"
      (Repl_state.apply (Fresh.create ()) Repl_state.To_cps source)
  in
  let expected =
    Repl_state.Cps_state
      (Cps.Root
         ("j0", "m0",
          Cps.Send (Cps.CVar "j0", Cps.Int 1, Cps.MVar "m0")))
  in
  check_state "to CPS" expected actual.state;
  check_rule "to CPS" None actual.rule_name

let test_cps_step () =
  let source =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Add
            (Cps.CVar "j", Cps.Int 20, Cps.Int 22, Cps.MVar "m")))
  in
  let actual =
    get_ok
      "CPS step"
      (Repl_state.apply (Fresh.create ()) Repl_state.Cps_step source)
  in
  let expected =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Send (Cps.CVar "j", Cps.Int 42, Cps.MVar "m")))
  in
  check_state "CPS step" expected actual.state;
  check_rule "CPS step" (Some "δ.+") actual.rule_name

let test_cps_assoc () =
  let k1 =
    Cps.Frame
      ("x", "j1", "m1",
       Cps.Add
         (Cps.CVar "j1", Cps.Var "x", Cps.Int 2, Cps.MVar "m1"))
  in
  let k2 =
    Cps.Frame
      ("y", "j2", "m2",
       Cps.Add
         (Cps.CVar "j2", Cps.Var "y", Cps.Int 3, Cps.MVar "m2"))
  in
  let source =
    Repl_state.Cps_state
      (Cps.Root
         ("root_j", "root_m",
          Cps.Send
            (Cps.Cons (k1, Cps.Cons (k2, Cps.CVar "root_j")),
             Cps.Int 1,
             Cps.MVar "root_m")))
  in
  let composed =
    Cps.Frame
      ("v0", "j0", "m0",
       Cps.Add
         (Cps.Cons (k2, Cps.CVar "j0"),
          Cps.Var "v0",
          Cps.Int 2,
          Cps.MVar "m0"))
  in
  let expected =
    Repl_state.Cps_state
      (Cps.Root
         ("root_j", "root_m",
          Cps.Send
            (Cps.Cons (composed, Cps.CVar "root_j"),
             Cps.Int 1,
             Cps.MVar "root_m")))
  in
  let actual =
    get_ok
      "CPS assoc"
      (Repl_state.apply (Fresh.create ()) Repl_state.Cps_assoc source)
  in
  check_state "CPS assoc" expected actual.state;
  check_rule "CPS assoc" (Some "assoc") actual.rule_name

let test_cps_eta () =
  let identity =
    Cps.Frame
      ("x", "j1", "m1",
       Cps.Send (Cps.CVar "j1", Cps.Var "x", Cps.MVar "m1"))
  in
  let source =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Op
            (Cps.MVar "m",
             Cps.Int 1,
             Cps.Cons (identity, Cps.CVar "j"))))
  in
  let expected =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Op (Cps.MVar "m", Cps.Int 1, Cps.CVar "j")))
  in
  let actual =
    get_ok
      "CPS eta.let"
      (Repl_state.apply (Fresh.create ()) Repl_state.Cps_eta source)
  in
  check_state "CPS eta.let" expected actual.state;
  check_rule "CPS eta.let" (Some "η.let") actual.rule_name

let test_eta_let_translation_path () =
  let supply = Fresh.create () in
  let source =
    Repl_state.Ds_state
      (Ds.Let
         ("x",
          Ds.Op (Ds.Int 1),
          Ds.Return (Ds.Var "x")))
  in
  let cps =
    get_ok
      "eta.let path: CPS translation"
      (Repl_state.apply supply Repl_state.To_cps source)
  in
  let reduced =
    get_ok
      "eta.let path: CPS eta.let"
      (Repl_state.apply supply Repl_state.Cps_eta cps.state)
  in
  let ds =
    get_ok
      "eta.let path: DS translation"
      (Repl_state.apply supply Repl_state.To_ds reduced.state)
  in
  check_state
    "eta.let translation path"
    (Repl_state.Ds_state (Ds.Op (Ds.Int 1)))
    ds.state

let test_to_ds () =
  let source =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m")))
  in
  let actual =
    get_ok
      "to DS"
      (Repl_state.apply (Fresh.create ()) Repl_state.To_ds source)
  in
  check_state
    "to DS"
    (Repl_state.Ds_state (Ds.Return (Ds.Int 1)))
    actual.state;
  check_rule "to DS" None actual.rule_name

let test_full_path () =
  let supply = Fresh.create () in
  let initial =
    Repl_state.Ds_state (Ds.Add (Ds.Int 1, Ds.Int 2))
  in
  let cps =
    get_ok "full path: CPS translation"
      (Repl_state.apply supply Repl_state.To_cps initial)
  in
  let reduced =
    get_ok "full path: CPS step"
      (Repl_state.apply supply Repl_state.Cps_step cps.state)
  in
  let ds =
    get_ok "full path: DS translation"
      (Repl_state.apply supply Repl_state.To_ds reduced.state)
  in
  check_state
    "full path"
    (Repl_state.Ds_state (Ds.Return (Ds.Int 3)))
    ds.state

let test_stuck_states () =
  check_error
    "DS has no root redex"
    Repl_state.No_ds_redex
    (Repl_state.apply
       (Fresh.create ())
       Repl_state.Ds_step
       (Repl_state.Ds_state (Ds.Return (Ds.Int 1))));
  check_error
    "CPS has no root redex"
    Repl_state.No_cps_redex
    (Repl_state.apply
       (Fresh.create ())
       Repl_state.Cps_step
       (Repl_state.Cps_state
          (Cps.Root
             ("j", "m",
              Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m")))))

let test_wrong_language () =
  let ds = Repl_state.Ds_state (Ds.Return (Ds.Int 1)) in
  let cps =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m")))
  in
  List.iter
    (fun action ->
      check_error
        "expected DS state"
        Repl_state.Expected_ds
        (Repl_state.apply (Fresh.create ()) action cps))
    [Repl_state.Ds_step; Repl_state.To_cps];
  List.iter
    (fun action ->
      check_error
        "expected CPS state"
        Repl_state.Expected_cps
        (Repl_state.apply (Fresh.create ()) action ds))
    [ Repl_state.Cps_step;
      Repl_state.Cps_assoc;
      Repl_state.Cps_eta;
      Repl_state.To_ds ]

let test_ds_translation_error () =
  let source =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Send (Cps.CVar "other_j", Cps.Int 1, Cps.MVar "m")))
  in
  check_error
    "DS translation error"
    (Repl_state.Ds_translation_error
       (Ds_translate.Unexpected_cont_var "other_j"))
    (Repl_state.apply (Fresh.create ()) Repl_state.To_ds source)

let test_prompt () =
  let ds = Repl_state.Ds_state (Ds.Return (Ds.Int 1)) in
  let cps =
    Repl_state.Cps_state
      (Cps.Root
         ("j", "m",
          Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m")))
  in
  if Repl_state.prompt ds <> "ds> " then
    failwith "DS prompt is incorrect";
  if Repl_state.prompt cps <> "cps> " then
    failwith "CPS prompt is incorrect"

let () =
  test_ds_step ();
  test_to_cps ();
  test_cps_step ();
  test_cps_assoc ();
  test_cps_eta ();
  test_eta_let_translation_path ();
  test_to_ds ();
  test_full_path ();
  test_stuck_states ();
  test_wrong_language ();
  test_ds_translation_error ();
  test_prompt ()
