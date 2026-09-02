open Reflection

let check_comp label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected:\n%s\nactual:\n%s"
         label
         (Format.asprintf "%a" Ds_pretty.pp_comp expected)
         (Format.asprintf "%a" Ds_pretty.pp_comp actual))

let check_parse label input expected =
  check_comp label expected (Ds_parse.comp input)

let test_return () =
  check_parse
    "return"
    "return 1"
    (Ds.Return (Ds.Int 1))

let test_variable_r () =
  check_parse
    "r is an identifier, not whitespace"
    "return r"
    (Ds.Return (Ds.Var "r"))

let test_addition () =
  check_parse
    "addition"
    "x + 2"
    (Ds.Add (Ds.Var "x", Ds.Int 2))

let test_application () =
  check_parse
    "application"
    "f x"
    (Ds.App (Ds.Var "f", Ds.Var "x"))

let test_operation () =
  check_parse
    "operation"
    "op x"
    (Ds.Op (Ds.Var "x"))

let test_lambda () =
  check_parse
    "lambda value"
    "return (fun x -> return x)"
    (Ds.Return
       (Ds.Lam
          ("x", Ds.Return (Ds.Var "x"))))

let test_let () =
  check_parse
    "let"
    "let x = return 1 in x + 2"
    (Ds.Let
       ("x",
        Ds.Return (Ds.Int 1),
        Ds.Add (Ds.Var "x", Ds.Int 2)))

let test_parenthesized_computation () =
  check_parse
    "parenthesized computation in a let binding"
    "let y = (let x = return 1 in x + 2) in y + 3"
    (Ds.Let
       ("y",
        Ds.Let
          ("x",
           Ds.Return (Ds.Int 1),
           Ds.Add (Ds.Var "x", Ds.Int 2)),
        Ds.Add (Ds.Var "y", Ds.Int 3)))

let test_handle () =
  check_parse
    "handle"
    "handle op 1 with x, k -> k x"
    (Ds.Handle
       (Ds.Op (Ds.Int 1),
        "x",
        "k",
        Ds.App (Ds.Var "k", Ds.Var "x")))

let test_nested_program () =
  let input =
    String.concat "\n"
      [ "handle";
        "  let v = op 1 in";
        "  v + 2";
        "with x, k ->";
        "  k x" ]
  in
  let expected =
    Ds.Handle
      (Ds.Let
         ("v",
          Ds.Op (Ds.Int 1),
          Ds.Add (Ds.Var "v", Ds.Int 2)),
       "x",
       "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in
  check_parse "multiline nested program" input expected

let test_carriage_return () =
  check_parse
    "carriage return whitespace"
    "return\r\n1"
    (Ds.Return (Ds.Int 1))

let test_invalid_input () =
  match Ds_parse.comp "return @" with
  | _ ->
      failwith "invalid input: expected a parse error"
  | exception Ds_parse.Error _ ->
      ()

let () =
  test_return ();
  test_variable_r ();
  test_addition ();
  test_application ();
  test_operation ();
  test_lambda ();
  test_let ();
  test_parenthesized_computation ();
  test_handle ();
  test_nested_program ();
  test_carriage_return ();
  test_invalid_input ()
