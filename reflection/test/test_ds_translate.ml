open Reflection

let check_equal pp label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected:\n%s\nactual:\n%s"
         label
         (Format.asprintf "%a" pp expected)
         (Format.asprintf "%a" pp actual))

let check_value = check_equal Ds_pretty.pp_value
let check_comp = check_equal Ds_pretty.pp_comp

let check_error label expected actual =
  match actual with
  | Error error when error = expected -> ()
  | Error _ -> failwith (label ^ ": returned a different error")
  | Ok _ -> failwith (label ^ ": unexpectedly succeeded")

let get_ok label = function
  | Ok value -> value
  | Error _ -> failwith (label ^ ": unexpectedly failed")

let scope =
  Ds_translate.{ cont_var = "j"; meta_var = "m" }

let test_values () =
  check_value
    "variable"
    (Ds.Var "x")
    (get_ok "variable" (Ds_translate.value (Cps.Var "x")));
  check_value
    "integer"
    (Ds.Int 42)
    (get_ok "integer" (Ds_translate.value (Cps.Int 42)));
  let source =
    Cps.Lam
      ("x", "j1", "m1",
       Cps.Send (Cps.CVar "j1", Cps.Var "x", Cps.MVar "m1"))
  in
  check_value
    "lambda"
    (Ds.Lam ("x", Ds.Return (Ds.Var "x")))
    (get_ok "lambda" (Ds_translate.value source))

let test_basic_terms () =
  let cases =
    [ ("send",
       Ds.Return (Ds.Int 1),
       Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m"));
      ("addition",
       Ds.Add (Ds.Int 1, Ds.Int 2),
       Cps.Add
         (Cps.CVar "j", Cps.Int 1, Cps.Int 2, Cps.MVar "m"));
      ("application",
       Ds.App (Ds.Var "f", Ds.Int 1),
       Cps.App
         (Cps.Var "f", Cps.Int 1, Cps.CVar "j", Cps.MVar "m"));
      ("operation",
       Ds.Op (Ds.Int 1),
       Cps.Op (Cps.MVar "m", Cps.Int 1, Cps.CVar "j")) ]
  in
  List.iter
    (fun (label, expected, source) ->
      check_comp
        label
        expected
        (get_ok label (Ds_translate.term scope source)))
    cases

let test_continuation_boundaries () =
  let plus_two =
    Cps.Frame
      ("x", "j1", "m1",
       Cps.Add
         (Cps.CVar "j1", Cps.Var "x", Cps.Int 2, Cps.MVar "m1"))
  in
  let plus_three =
    Cps.Frame
      ("y", "j2", "m2",
       Cps.Add
         (Cps.CVar "j2", Cps.Var "y", Cps.Int 3, Cps.MVar "m2"))
  in
  let source =
    Cps.Send
      (Cps.Cons (plus_two, Cps.Cons (plus_three, Cps.Eps)),
       Cps.Int 1,
       Cps.Empty)
  in
  let expected =
    Ds.Let
      ("y",
       Ds.Let
         ("x",
          Ds.Return (Ds.Int 1),
          Ds.Add (Ds.Var "x", Ds.Int 2)),
       Ds.Add (Ds.Var "y", Ds.Int 3))
  in
  check_comp
    "continuation boundaries"
    expected
    (get_ok "continuation boundaries" (Ds_translate.term scope source))

let test_metacontinuation () =
  let outside =
    Cps.Frame
      ("z", "j1", "m1",
       Cps.Add
         (Cps.CVar "j1", Cps.Var "z", Cps.Int 4, Cps.MVar "m1"))
  in
  let handler =
    Cps.Handler
      ("x", "k", "j2", "m2",
       Cps.Send (Cps.CVar "j2", Cps.Var "x", Cps.MVar "m2"))
  in
  let source =
    Cps.Send
      (Cps.Eps,
       Cps.Int 1,
       Cps.MCons (Cps.Cons (outside, Cps.Eps), handler, Cps.Empty))
  in
  let expected =
    Ds.Let
      ("z",
       Ds.Handle
         (Ds.Return (Ds.Int 1),
          "x",
          "k",
          Ds.Return (Ds.Var "x")),
       Ds.Add (Ds.Var "z", Ds.Int 4))
  in
  check_comp
    "metacontinuation"
    expected
    (get_ok "metacontinuation" (Ds_translate.term scope source))

let test_root () =
  let source =
    Cps.Root
      ("j0", "m0",
       Cps.Send (Cps.CVar "j0", Cps.Int 1, Cps.MVar "m0"))
  in
  check_comp
    "root"
    (Ds.Return (Ds.Int 1))
    (get_ok "root" (Ds_translate.root source))

let test_translation_image () =
  let source =
    Ds.Handle
      (Ds.Let
         ("x", Ds.Op (Ds.Int 1), Ds.Add (Ds.Var "x", Ds.Int 2)),
       "x",
       "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  let cps = Cps_translate.program (Fresh.create ()) source in
  let expected =
    Ds.Handle
      (Ds.Let
         ("v1", Ds.Op (Ds.Int 1), Ds.Add (Ds.Var "v1", Ds.Int 2)),
       "v0",
       "r0",
       Ds.App (Ds.Var "r0", Ds.Var "v0"))
  in
  check_comp
    "CPS translation image"
    expected
    (get_ok "CPS translation image" (Ds_translate.root cps))

let test_errors () =
  check_error
    "unexpected continuation variable"
    (Ds_translate.Unexpected_cont_var "other_j")
    (Ds_translate.term
       scope
       (Cps.Send (Cps.CVar "other_j", Cps.Int 1, Cps.MVar "m")));
  check_error
    "unexpected metacontinuation variable"
    (Ds_translate.Unexpected_meta_var "other_m")
    (Ds_translate.term
       scope
       (Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "other_m")));
  check_error
    "free handler variable"
    (Ds_translate.Free_handler_var "h")
    (Ds_translate.term
       scope
       (Cps.Send
          (Cps.Eps,
           Cps.Int 1,
           Cps.MCons (Cps.Eps, Cps.HVar "h", Cps.Empty))))

let () =
  test_values ();
  test_basic_terms ();
  test_continuation_boundaries ();
  test_metacontinuation ();
  test_root ();
  test_translation_image ();
  test_errors ()
