open Reflection

let check_value label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected: %s\nactual:   %s"
         label
         (Format.asprintf "%a" Ds_pretty.pp_value expected)
         (Format.asprintf "%a" Ds_pretty.pp_value actual))

let check_comp label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected:\n%s\nactual:\n%s"
         label
         (Format.asprintf "%a" Ds_pretty.pp_comp expected)
         (Format.asprintf "%a" Ds_pretty.pp_comp actual))

let subst_value ~var ~by value =
  Ds_subst.value (Fresh.create ()) ~var ~by value

let subst_comp ~var ~by comp =
  Ds_subst.comp (Fresh.create ()) ~var ~by comp

let test_variable_hit () =
  check_value
    "x[1/x]"
    (Ds.Int 1)
    (subst_value ~var:"x" ~by:(Ds.Int 1) (Ds.Var "x"))

let test_variable_miss () =
  check_value
    "y[1/x]"
    (Ds.Var "y")
    (subst_value ~var:"x" ~by:(Ds.Int 1) (Ds.Var "y"))

let test_lambda_shadowing () =
  let term =
    Ds.Lam ("x", Ds.Return (Ds.Var "x"))
  in
  check_value
    "lambda shadowing"
    term
    (subst_value ~var:"x" ~by:(Ds.Int 1) term)

let test_lambda_capture_avoidance () =
  let term =
    Ds.Lam ("x", Ds.Return (Ds.Var "y"))
  in
  let expected =
    Ds.Lam ("x0", Ds.Return (Ds.Var "x"))
  in
  check_value
    "lambda capture avoidance"
    expected
    (subst_value ~var:"y" ~by:(Ds.Var "x") term)

let test_addition_preserves_constructor () =
  let term =
    Ds.Add (Ds.Var "x", Ds.Int 2)
  in
  let expected =
    Ds.Add (Ds.Int 1, Ds.Int 2)
  in
  check_comp
    "addition substitution"
    expected
    (subst_comp ~var:"x" ~by:(Ds.Int 1) term)

let test_let_shadowing () =
  let term =
    Ds.Let
      ("x",
       Ds.Return (Ds.Var "x"),
       Ds.Return (Ds.Var "x"))
  in
  let expected =
    Ds.Let
      ("x",
       Ds.Return (Ds.Int 1),
       Ds.Return (Ds.Var "x"))
  in
  check_comp
    "let binder scopes only the body"
    expected
    (subst_comp ~var:"x" ~by:(Ds.Int 1) term)

let test_let_capture_avoidance () =
  let term =
    Ds.Let
      ("x",
       Ds.Return (Ds.Var "y"),
       Ds.Add (Ds.Var "y", Ds.Var "x"))
  in
  let expected =
    Ds.Let
      ("x0",
       Ds.Return (Ds.Var "x"),
       Ds.Add (Ds.Var "x", Ds.Var "x0"))
  in
  check_comp
    "let capture avoidance"
    expected
    (subst_comp ~var:"y" ~by:(Ds.Var "x") term)

let test_handler_shadowing () =
  let term =
    Ds.Handle
      (Ds.Op (Ds.Var "x"),
       "x",
       "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  let expected =
    Ds.Handle
      (Ds.Op (Ds.Int 1),
       "x",
       "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  check_comp
    "handler binders scope only the clause body"
    expected
    (subst_comp ~var:"x" ~by:(Ds.Int 1) term)

let test_handler_capture_avoidance () =
  let term =
    Ds.Handle
      (Ds.Return (Ds.Var "y"),
       "x",
       "k",
       Ds.Add (Ds.Var "y", Ds.Var "x"))
  in
  let expected =
    Ds.Handle
      (Ds.Return (Ds.Var "x"),
       "x0",
       "k",
       Ds.Add (Ds.Var "x", Ds.Var "x0"))
  in
  check_comp
    "handler capture avoidance"
    expected
    (subst_comp ~var:"y" ~by:(Ds.Var "x") term)

let () =
  test_variable_hit ();
  test_variable_miss ();
  test_lambda_shadowing ();
  test_lambda_capture_avoidance ();
  test_addition_preserves_constructor ();
  test_let_shadowing ();
  test_let_capture_avoidance ();
  test_handler_shadowing ();
  test_handler_capture_avoidance ()
