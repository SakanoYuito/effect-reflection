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
let check_cont = check_equal Cps_pretty.pp_cont
let check_handler = check_equal Cps_pretty.pp_handler
let check_term = check_equal Cps_pretty.pp_term
let check_root = check_equal Cps_pretty.pp_root

let test_four_namespaces () =
  let replacement_handler =
    Cps.HVar "replacement_h"
  in
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "x" (Cps.Int 1)
    |> Cps_subst.add_cont "j" Cps.Eps
    |> Cps_subst.add_meta "m" Cps.Empty
    |> Cps_subst.add_handler "h" replacement_handler
  in
  let term =
    Cps.Send
      (Cps.CVar "j",
       Cps.Var "x",
       Cps.MCons
         (Cps.CVar "tail",
          Cps.HVar "h",
          Cps.MVar "m"))
  in
  let expected =
    Cps.Send
      (Cps.Eps,
       Cps.Int 1,
       Cps.MCons
         (Cps.CVar "tail",
          replacement_handler,
          Cps.Empty))
  in
  let actual =
    Cps_subst.term (Fresh.create ()) env term
  in
  check_term "four substitution namespaces" expected actual

let test_simultaneous_substitution () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "x" (Cps.Var "y")
    |> Cps_subst.add_value "y" (Cps.Int 1)
  in
  let actual =
    Cps_subst.value (Fresh.create ()) env (Cps.Var "x")
  in
  check_value
    "a replacement is not substituted again"
    (Cps.Var "y")
    actual

let test_lambda_shadowing () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "x" (Cps.Int 1)
    |> Cps_subst.add_cont "j" Cps.Eps
    |> Cps_subst.add_meta "m" Cps.Empty
  in
  let source =
    Cps.Lam
      ("x", "j", "m",
       Cps.Send
         (Cps.CVar "j",
          Cps.Var "x",
          Cps.MVar "m"))
  in
  let actual =
    Cps_subst.value (Fresh.create ()) env source
  in
  check_value "lambda shadowing" source actual

let test_lambda_capture_avoidance () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "y" (Cps.Var "x")
    |> Cps_subst.add_cont "tail" (Cps.CVar "j")
    |> Cps_subst.add_meta "outer" (Cps.MVar "m")
  in
  let source =
    Cps.Lam
      ("x", "j", "m",
       Cps.Send
         (Cps.CVar "tail",
          Cps.Var "y",
          Cps.MVar "outer"))
  in
  let expected =
    Cps.Lam
      ("x0", "j0", "m0",
       Cps.Send
         (Cps.CVar "j",
          Cps.Var "x",
          Cps.MVar "m"))
  in
  let actual =
    Cps_subst.value (Fresh.create ()) env source
  in
  check_value "lambda capture avoidance" expected actual

let test_frame_capture_avoidance () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "y" (Cps.Var "v")
  in
  let source =
    Cps.Cons
      (Cps.Frame
         ("v", "j", "m",
          Cps.Send
            (Cps.CVar "j",
             Cps.Var "y",
             Cps.MVar "m")),
       Cps.CVar "tail")
  in
  let expected =
    Cps.Cons
      (Cps.Frame
         ("v0", "j", "m",
          Cps.Send
            (Cps.CVar "j",
             Cps.Var "v",
             Cps.MVar "m")),
       Cps.CVar "tail")
  in
  let actual =
    Cps_subst.cont (Fresh.create ()) env source
  in
  check_cont "frame capture avoidance" expected actual

let test_handler_shadowing () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "v" (Cps.Int 1)
    |> Cps_subst.add_value "r" (Cps.Int 2)
    |> Cps_subst.add_cont "j" Cps.Eps
    |> Cps_subst.add_meta "m" Cps.Empty
  in
  let source =
    Cps.Handler
      ("v", "r", "j", "m",
       Cps.App
         (Cps.Var "r",
          Cps.Var "v",
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  let actual =
    Cps_subst.handler (Fresh.create ()) env source
  in
  check_handler "handler shadowing" source actual

let test_handler_capture_avoidance () =
  let replacement =
    Cps.Lam
      ("z", "jz", "mz",
       Cps.App
         (Cps.Var "v",
          Cps.Var "r",
          Cps.CVar "jz",
          Cps.MVar "mz"))
  in
  let env =
    Cps_subst.empty
    |> Cps_subst.add_value "y" replacement
    |> Cps_subst.add_cont "tail" (Cps.CVar "j")
    |> Cps_subst.add_meta "outer" (Cps.MVar "m")
  in
  let source =
    Cps.Handler
      ("v", "r", "j", "m",
       Cps.App
         (Cps.Var "y",
          Cps.Int 0,
          Cps.CVar "tail",
          Cps.MVar "outer"))
  in
  let expected =
    Cps.Handler
      ("v0", "r0", "j0", "m0",
       Cps.App
         (replacement,
          Cps.Int 0,
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  let actual =
    Cps_subst.handler (Fresh.create ()) env source
  in
  check_handler "handler capture avoidance" expected actual

let test_root_shadowing () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_cont "j" Cps.Eps
    |> Cps_subst.add_meta "m" Cps.Empty
  in
  let source =
    Cps.Root
      ("j", "m",
       Cps.Send
         (Cps.CVar "j",
          Cps.Int 1,
          Cps.MVar "m"))
  in
  let actual =
    Cps_subst.root (Fresh.create ()) env source
  in
  check_root "root shadowing" source actual

let test_root_capture_avoidance () =
  let env =
    Cps_subst.empty
    |> Cps_subst.add_cont "tail" (Cps.CVar "j")
    |> Cps_subst.add_meta "outer" (Cps.MVar "m")
  in
  let source =
    Cps.Root
      ("j", "m",
       Cps.Send
         (Cps.CVar "tail",
          Cps.Int 1,
          Cps.MVar "outer"))
  in
  let expected =
    Cps.Root
      ("j0", "m0",
       Cps.Send
         (Cps.CVar "j",
          Cps.Int 1,
          Cps.MVar "m"))
  in
  let actual =
    Cps_subst.root (Fresh.create ()) env source
  in
  check_root "root capture avoidance" expected actual

let () =
  test_four_namespaces ();
  test_simultaneous_substitution ();
  test_lambda_shadowing ();
  test_lambda_capture_avoidance ();
  test_frame_capture_avoidance ();
  test_handler_shadowing ();
  test_handler_capture_avoidance ();
  test_root_shadowing ();
  test_root_capture_avoidance ()
