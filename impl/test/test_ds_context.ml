open Reflection

let check_comp label expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf
         "%s:\nexpected:\n%s\nactual:\n%s"
         label
         (Format.asprintf "%a" Ds_pretty.pp_comp expected)
         (Format.asprintf "%a" Ds_pretty.pp_comp actual))

let test_hole () =
  match Ds_context.decompose_operation (Ds.Op (Ds.Int 1)) with
  | Some (Ds_context.Hole, Ds.Int 1) -> ()
  | _ -> failwith "direct operation: expected Hole and value 1"

let test_nested_context_round_trip () =
  let source =
    Ds.Let
      ("v",
       Ds.Let
         ("w",
          Ds.Op (Ds.Int 1),
          Ds.Add (Ds.Var "w", Ds.Int 2)),
       Ds.Add (Ds.Var "v", Ds.Int 3))
  in
  match Ds_context.decompose_operation source with
  | None ->
      failwith "nested context: expected an operation decomposition"
  | Some (context, operation_value) ->
      if operation_value <> Ds.Int 1 then
        failwith "nested context: expected operation value 1";
      check_comp
        "decompose followed by plug"
        source
        (Ds_context.plug context (Ds.Op operation_value))

let test_no_operation () =
  match
    Ds_context.decompose_operation
      (Ds.Add (Ds.Int 1, Ds.Int 2))
  with
  | None -> ()
  | Some _ -> failwith "no operation: expected no decomposition"

let () =
  test_hole ();
  test_nested_context_round_trip ();
  test_no_operation ()
