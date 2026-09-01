open Reflection

let check_equal label expected actual = 
  if expected <> actual then
    failwith
      (Printf.sprintf
        "%s:\nexpected:\n%s\nactual:\n%s"
        label expected actual)

let print_comp term = 
  Format.asprintf "%a" Ds_pretty.pp_comp term

let test_return () = 
  (* return 1 *)
  let term = 
    Ds.Return (Ds.Int 1)
  in
  check_equal
    "return"
    "return 1"
    (print_comp term)

let test_add () = 
  (* x + 2 *)
  let term = 
    Ds.Add (Ds.Var "x", Ds.Int 2)
  in
  check_equal
    "add"
    "x + 2"
    (print_comp term)

let test_let () = 
  (* let x = return 1 in x + 2 *)
  let term = 
    Ds.Let 
      ("x",
       Ds.Return (Ds.Int 1),
       Ds.Add (Ds.Var "x", Ds.Int 2))
  in
  check_equal
    "let"
    "let x = return 1 in x + 2"
    (print_comp term)

let test_nested_let_rhs () =
  let term =
    Ds.Let
      ("y",
       Ds.Let
         ("x",
          Ds.Return (Ds.Int 1),
          Ds.Add (Ds.Var "x", Ds.Int 2)),
       Ds.Add (Ds.Var "y", Ds.Int 3))
  in
  check_equal
    "nested let RHS"
    "let y = (let x = return 1 in x + 2) in y + 3"
    (print_comp term)

let () = 
  test_return ();
  test_add ();
  test_let ();
  test_nested_let_rhs ()
