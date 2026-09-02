open Reflection

let check_equal label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected:\n%s\nactual:\n%s"
         label expected actual)

let print pp value =
  Format.asprintf "%a" pp value

let identity_body value cont meta =
  Cps.Send (Cps.CVar cont, Cps.Var value, Cps.MVar meta)

let identity_frame value cont meta =
  Cps.Frame (value, cont, meta, identity_body value cont meta)

let resuming_handler () =
  Cps.Handler
    ("v", "r", "j0", "m0",
     Cps.App
       (Cps.Var "r",
        Cps.Var "v",
        Cps.CVar "j0",
        Cps.MVar "m0"))

let test_root () =
  let root =
    Cps.Root
      ("j", "m",
       Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m"))
  in
  check_equal
    "root"
    "λj. λm.\n  j 1 m"
    (print Cps_pretty.pp_root root)

let test_values () =
  check_equal
    "value variable"
    "x"
    (print Cps_pretty.pp_value (Cps.Var "x"));
  check_equal
    "value integer"
    "42"
    (print Cps_pretty.pp_value (Cps.Int 42));
  let lambda =
    Cps.Lam
      ("x", "j", "m",
       Cps.Add
         (Cps.CVar "j", Cps.Var "x", Cps.Int 2, Cps.MVar "m"))
  in
  check_equal
    "value lambda"
    "(λx. λj. λm. j (x + 2) m)"
    (print Cps_pretty.pp_value lambda)

let test_frame () =
  let frame = identity_frame "v" "j" "m" in
  check_equal
    "continuation frame"
    "(λv. λj. λm. j v m)"
    (print Cps_pretty.pp_frame frame)

let test_continuations () =
  check_equal
    "continuation variable"
    "j"
    (print Cps_pretty.pp_cont (Cps.CVar "j"));
  check_equal
    "empty continuation"
    "ε"
    (print Cps_pretty.pp_cont Cps.Eps);
  let continuation =
    Cps.Cons
      (identity_frame "x" "j1" "m1",
       Cps.Cons
         (identity_frame "y" "j2" "m2",
          Cps.Eps))
  in
  check_equal
    "continuation stack"
    "(λx. λj1. λm1. j1 x m1) :: (λy. λj2. λm2. j2 y m2) :: ε"
    (print Cps_pretty.pp_cont continuation)

let test_handlers () =
  check_equal
    "handler variable"
    "h"
    (print Cps_pretty.pp_handler (Cps.HVar "h"));
  check_equal
    "handler"
    "(λv. λr. λj0. λm0. r v j0 m0)"
    (print Cps_pretty.pp_handler (resuming_handler ()))

let test_metacontinuations () =
  check_equal
    "metacontinuation variable"
    "m"
    (print Cps_pretty.pp_metacont (Cps.MVar "m"));
  check_equal
    "empty metacontinuation"
    "()"
    (print Cps_pretty.pp_metacont Cps.Empty);
  let metacontinuation =
    Cps.MCons
      (Cps.Eps,
       resuming_handler (),
       Cps.MCons (Cps.CVar "outside", Cps.HVar "h", Cps.Empty))
  in
  check_equal
    "metacontinuation stack"
    "<ε, (λv. λr. λj0. λm0. r v j0 m0)> :: <outside, h> :: ()"
    (print Cps_pretty.pp_metacont metacontinuation)

let test_terms () =
  check_equal
    "send"
    "j 1 m"
    (print
       Cps_pretty.pp_term
       (Cps.Send (Cps.CVar "j", Cps.Int 1, Cps.MVar "m")));
  check_equal
    "addition"
    "j (x + 2) m"
    (print
       Cps_pretty.pp_term
       (Cps.Add
          (Cps.CVar "j", Cps.Var "x", Cps.Int 2, Cps.MVar "m")));
  check_equal
    "application"
    "f 1 j m"
    (print
       Cps_pretty.pp_term
       (Cps.App
          (Cps.Var "f", Cps.Int 1, Cps.CVar "j", Cps.MVar "m")));
  check_equal
    "operation"
    "m @ 1 j"
    (print
       Cps_pretty.pp_term
       (Cps.Op (Cps.MVar "m", Cps.Int 1, Cps.CVar "j")))

let test_nested_operation () =
  let captured =
    Cps.Cons (identity_frame "x" "j1" "m1", Cps.Eps)
  in
  let metacontinuation =
    Cps.MCons (Cps.Eps, resuming_handler (), Cps.Empty)
  in
  let term = Cps.Op (metacontinuation, Cps.Int 1, captured) in
  check_equal
    "operation with captured and stored continuations"
    "(<ε, (λv. λr. λj0. λm0. r v j0 m0)> :: ()) @ 1\n\
     \  ((λx. λj1. λm1. j1 x m1) :: ε)"
    (print Cps_pretty.pp_term term)

let () =
  test_root ();
  test_values ();
  test_frame ();
  test_continuations ();
  test_handlers ();
  test_metacontinuations ();
  test_terms ();
  test_nested_operation ()
