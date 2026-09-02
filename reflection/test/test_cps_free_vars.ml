open Reflection

let string_of_name_set names =
  names
  |> Name_set.elements
  |> String.concat ", "
  |> Printf.sprintf "{%s}"

let check_set label expected actual =
  if not (Name_set.equal expected actual) then
    failwith
      (Printf.sprintf
         "%s:\nexpected %s\nactual   %s"
         label
         (string_of_name_set expected)
         (string_of_name_set actual))

let check_fv label
    (expected : Cps_free_vars.t)
    (actual : Cps_free_vars.t) =
  check_set (label ^ " / values") expected.values actual.values;
  check_set (label ^ " / continuations") expected.conts actual.conts;
  check_set (label ^ " / metacontinuations") expected.metas actual.metas;
  check_set (label ^ " / handlers") expected.handlers actual.handlers

let fv ?(values = []) ?(conts = []) ?(metas = []) ?(handlers = []) () =
  {
    Cps_free_vars.values = Name_set.of_list values;
    conts = Name_set.of_list conts;
    metas = Name_set.of_list metas;
    handlers = Name_set.of_list handlers;
  }

let test_term_namespaces () =
  let term =
    Cps.App
      (Cps.Var "f",
       Cps.Var "x",
       Cps.CVar "j",
       Cps.MVar "m")
  in
  check_fv
    "term namespaces"
    (fv ~values:["f"; "x"] ~conts:["j"] ~metas:["m"] ())
    (Cps_free_vars.term term)

let test_lambda_binders () =
  let value =
    Cps.Lam
      ("x", "j", "m",
       Cps.App
         (Cps.Var "x",
          Cps.Var "free",
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  check_fv
    "lambda binders"
    (fv ~values:["free"] ())
    (Cps_free_vars.value value)

let test_frame_and_tail () =
  let frame =
    Cps.Frame
      ("v", "j", "m",
       Cps.App
         (Cps.Var "f",
          Cps.Var "v",
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  let cont =
    Cps.Cons (frame, Cps.CVar "tail")
  in
  check_fv
    "frame binders and continuation tail"
    (fv ~values:["f"] ~conts:["tail"] ())
    (Cps_free_vars.cont cont)

let test_handler_binders () =
  let argument =
    Cps.Lam
      ("x", "j1", "m1",
       Cps.App
         (Cps.Var "v",
          Cps.Var "free",
          Cps.CVar "j1",
          Cps.MVar "m1"))
  in
  let handler =
    Cps.Handler
      ("v", "r", "j", "m",
       Cps.App
         (Cps.Var "r",
          argument,
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  check_fv
    "handler binders"
    (fv ~values:["free"] ())
    (Cps_free_vars.handler handler)

let test_metacontinuation () =
  let metacont =
    Cps.MCons
      (Cps.CVar "stored",
       Cps.HVar "h",
       Cps.MVar "m")
  in
  check_fv
    "metacontinuation components"
    (fv ~conts:["stored"] ~metas:["m"] ~handlers:["h"] ())
    (Cps_free_vars.metacont metacont)

let test_root_binders () =
  let root =
    Cps.Root
      ("j", "m",
       Cps.App
         (Cps.Var "f",
          Cps.Int 1,
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  check_fv
    "root binders"
    (fv ~values:["f"] ())
    (Cps_free_vars.root root)

let test_closed_translation () =
  let source =
    Ds.Handle
      (Ds.Op (Ds.Int 1),
       "x",
       "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  let target =
    Cps_translate.program (Fresh.create ()) source
  in
  check_fv
    "closed translated program"
    (fv ())
    (Cps_free_vars.root target)

let () =
  test_term_namespaces ();
  test_lambda_binders ();
  test_frame_and_tail ();
  test_handler_binders ();
  test_metacontinuation ();
  test_root_binders ();
  test_closed_translation ()
