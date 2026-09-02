open Reflection

let check_equal pp label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected:\n%s\nactual:\n%s"
         label
         (Format.asprintf "%a" pp expected)
         (Format.asprintf "%a" pp actual))

let check_value = check_equal Cps_pretty.pp_value
let check_term = check_equal Cps_pretty.pp_term
let check_root = check_equal Cps_pretty.pp_root

let translate_comp source =
  Cps_translate.comp
    (Fresh.create ())
    source
    (Cps.CVar "j")
    (Cps.MVar "m")

let test_lambda () =
  let source =
    Ds.Lam ("x", Ds.Return (Ds.Var "x"))
  in
  let expected =
    Cps.Lam
      ("x", "j0", "m0",
       Cps.Send
         (Cps.CVar "j0",
          Cps.Var "x",
          Cps.MVar "m0"))
  in
  let actual =
    Cps_translate.value (Fresh.create ()) source
  in
  check_value "lambda" expected actual

let test_return () =
  let expected =
    Cps.Send
      (Cps.CVar "j",
       Cps.Int 1,
       Cps.MVar "m")
  in
  check_term
    "return"
    expected
    (translate_comp (Ds.Return (Ds.Int 1)))

let test_add () =
  let expected =
    Cps.Add
      (Cps.CVar "j",
       Cps.Var "x",
       Cps.Int 2,
       Cps.MVar "m")
  in
  check_term
    "addition"
    expected
    (translate_comp (Ds.Add (Ds.Var "x", Ds.Int 2)))

let test_application () =
  let expected =
    Cps.App
      (Cps.Var "f",
       Cps.Int 1,
       Cps.CVar "j",
       Cps.MVar "m")
  in
  check_term
    "application"
    expected
    (translate_comp (Ds.App (Ds.Var "f", Ds.Int 1)))

let test_operation () =
  let expected =
    Cps.Op
      (Cps.MVar "m",
       Cps.Int 1,
       Cps.CVar "j")
  in
  check_term
    "operation"
    expected
    (translate_comp (Ds.Op (Ds.Int 1)))

let test_let () =
  let source =
    Ds.Let
      ("x",
       Ds.Return (Ds.Int 1),
       Ds.Add (Ds.Var "x", Ds.Int 2))
  in
  let frame =
    Cps.Frame
      ("v0", "j0", "m0",
       Cps.Add
         (Cps.CVar "j0",
          Cps.Var "v0",
          Cps.Int 2,
          Cps.MVar "m0"))
  in
  let expected =
    Cps.Send
      (Cps.Cons (frame, Cps.CVar "j"),
       Cps.Int 1,
       Cps.MVar "m")
  in
  check_term "let" expected (translate_comp source)

let test_handle () =
  let source =
    Ds.Handle
      (Ds.Op (Ds.Int 1),
       "x",
       "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  let handler =
    Cps.Handler
      ("v0", "r0", "j0", "m0",
       Cps.App
         (Cps.Var "r0",
          Cps.Var "v0",
          Cps.CVar "j0",
          Cps.MVar "m0"))
  in
  let expected =
    Cps.Op
      (Cps.MCons
         (Cps.CVar "j",
          handler,
          Cps.MVar "m"),
       Cps.Int 1,
       Cps.Eps)
  in
  check_term "handle" expected (translate_comp source)

let test_program () =
  let source =
    Ds.Return (Ds.Int 1)
  in
  let expected =
    Cps.Root
      ("j0", "m0",
       Cps.Send
         (Cps.CVar "j0",
          Cps.Int 1,
          Cps.MVar "m0"))
  in
  let actual =
    Cps_translate.program (Fresh.create ()) source
  in
  check_root "program" expected actual

let () =
  test_lambda ();
  test_return ();
  test_add ();
  test_application ();
  test_operation ();
  test_let ();
  test_handle ();
  test_program ()
