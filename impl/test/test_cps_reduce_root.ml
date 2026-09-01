open Reflection

let string_of_rule = function
  | Cps_reduce_root.Beta_value -> "beta.v"
  | Cps_reduce_root.Beta_let -> "beta.let"
  | Cps_reduce_root.Eta_value -> "eta.v"
  | Cps_reduce_root.Delta_add -> "delta.+"
  | Cps_reduce_root.Handler_return -> "h.return"
  | Cps_reduce_root.Beta_op_shallow -> "beta.op.S"
  | Cps_reduce_root.Assoc -> "assoc"
  | Cps_reduce_root.Eta_let -> "eta.let"

let check_step label expected_rule expected_reduct source =
  match Cps_reduce_root.contract (Fresh.create ()) source with
  | None ->
      failwith (label ^ ": expected a root reduction, but the term is stuck")

  | Some actual ->
      if actual.rule <> expected_rule then
        failwith
          (Printf.sprintf
             "%s: expected rule %s, but got %s"
             label
             (string_of_rule expected_rule)
             (string_of_rule actual.rule));

      if actual.reduct <> expected_reduct then
        failwith
          (Printf.sprintf
             "%s:\nexpected:\n%s\nactual:\n%s"
             label
             (Format.asprintf "%a" Cps_pretty.pp_term expected_reduct)
             (Format.asprintf "%a" Cps_pretty.pp_term actual.reduct))

let check_stuck label source =
  match Cps_reduce_root.contract (Fresh.create ()) source with
  | None -> ()
  | Some actual ->
      failwith
        (Printf.sprintf
           "%s: expected no root reduction, but %s applied"
           label
           (string_of_rule actual.rule))

let identity_frame v j m =
  Cps.Frame
    (v, j, m,
     Cps.Send
       (Cps.CVar j,
        Cps.Var v,
        Cps.MVar m))

let add_frame v j m n =
  Cps.Frame
    (v, j, m,
     Cps.Add
       (Cps.CVar j,
        Cps.Var v,
        Cps.Int n,
        Cps.MVar m))

let two_frame_continuation () =
  let k1 = add_frame "x" "j1" "m1" 2 in
  let k2 = add_frame "y" "j2" "m2" 3 in
  (k1, k2,
   Cps.Cons (k1, Cps.Cons (k2, Cps.CVar "tail")))

let test_beta_value () =
  let source =
    Cps.App
      (Cps.Lam
         ("x", "j", "m",
          Cps.Add
            (Cps.CVar "j",
             Cps.Var "x",
             Cps.Int 2,
             Cps.MVar "m")),
       Cps.Int 1,
       Cps.Eps,
       Cps.Empty)
  in
  let expected =
    Cps.Add
      (Cps.Eps,
       Cps.Int 1,
       Cps.Int 2,
       Cps.Empty)
  in
  check_step
    "beta.v"
    Cps_reduce_root.Beta_value
    expected
    source

let test_eta_value () =
  let source =
    Cps.Lam
      ("x", "j", "m",
       Cps.App
         (Cps.Var "f",
          Cps.Var "x",
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  match Cps_reduce_root.contract_value source with
  | [{ rule = Cps_reduce_root.Eta_value; reduct = Cps.Var "f" }] -> ()
  | _ -> failwith "eta.v: expected lambda x j m. f x j m to reduce to f"

let test_eta_value_side_conditions () =
  let value_capture =
    Cps.Lam
      ("x", "j", "m",
       Cps.App
         (Cps.Var "x", Cps.Var "x", Cps.CVar "j", Cps.MVar "m"))
  in
  let free_cont_value =
    Cps.Lam
      ("z", "inner_j", "inner_m",
       Cps.Send
         (Cps.CVar "j", Cps.Var "z", Cps.MVar "inner_m"))
  in
  let cont_capture =
    Cps.Lam
      ("x", "j", "m",
       Cps.App
         (free_cont_value,
          Cps.Var "x",
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  let free_meta_value =
    Cps.Lam
      ("z", "inner_j", "inner_m",
       Cps.Send
         (Cps.CVar "inner_j", Cps.Var "z", Cps.MVar "m"))
  in
  let meta_capture =
    Cps.Lam
      ("x", "j", "m",
       Cps.App
         (free_meta_value,
          Cps.Var "x",
          Cps.CVar "j",
          Cps.MVar "m"))
  in
  List.iter
    (fun source ->
      match Cps_reduce_root.contract_value source with
      | [] -> ()
      | _ -> failwith "eta.v ignored a free-variable side condition")
    [value_capture; cont_capture; meta_capture]

let test_contract_cont_lists_overlapping_rules () =
  let identity = identity_frame "x" "j1" "m1" in
  let following = add_frame "y" "j2" "m2" 3 in
  let continuation =
    Cps.Cons
      (identity,
       Cps.Cons (following, Cps.CVar "tail"))
  in
  let rules =
    Cps_reduce_root.contract_cont (Fresh.create ()) continuation
    |> List.map
         (fun (step : Cps_reduce_root.cont_step) -> step.rule)
  in
  if rules <> [Cps_reduce_root.Eta_let; Cps_reduce_root.Assoc] then
    failwith "contract_cont did not return both eta.let and assoc"

let test_beta_let () =
  let frame =
    Cps.Frame
      ("v", "j", "m",
       Cps.Add
         (Cps.CVar "j",
          Cps.Var "v",
          Cps.Int 2,
          Cps.MVar "m"))
  in
  let source =
    Cps.Send
      (Cps.Cons (frame, Cps.CVar "tail"),
       Cps.Int 1,
       Cps.MVar "outer")
  in
  let expected =
    Cps.Add
      (Cps.CVar "tail",
       Cps.Int 1,
       Cps.Int 2,
       Cps.MVar "outer")
  in
  check_step
    "beta.let"
    Cps_reduce_root.Beta_let
    expected
    source

let test_delta_add () =
  let source =
    Cps.Add
      (Cps.CVar "j",
       Cps.Int 20,
       Cps.Int 22,
       Cps.MVar "m")
  in
  let expected =
    Cps.Send
      (Cps.CVar "j",
       Cps.Int 42,
       Cps.MVar "m")
  in
  check_step
    "delta.+"
    Cps_reduce_root.Delta_add
    expected
    source

let test_handler_return () =
  let source =
    Cps.Send
      (Cps.Eps,
       Cps.Int 1,
       Cps.MCons
         (Cps.CVar "exit",
          Cps.HVar "h",
          Cps.MVar "outer"))
  in
  let expected =
    Cps.Send
      (Cps.CVar "exit",
       Cps.Int 1,
       Cps.MVar "outer")
  in
  check_step
    "h.return"
    Cps_reduce_root.Handler_return
    expected
    source

let resuming_handler () =
  Cps.Handler
    ("operation_value", "resume", "handler_j", "handler_m",
     Cps.App
       (Cps.Var "resume",
        Cps.Var "operation_value",
        Cps.CVar "handler_j",
        Cps.MVar "handler_m"))

let test_beta_op_empty_capture () =
  let source =
    Cps.Op
      (Cps.MCons
         (Cps.CVar "exit",
          resuming_handler (),
          Cps.MVar "outer"),
       Cps.Int 1,
       Cps.Eps)
  in
  let resumption =
    Cps.Lam
      ("y0", "j0", "m0",
       Cps.Send
         (Cps.CVar "j0",
          Cps.Var "y0",
          Cps.MVar "m0"))
  in
  let expected =
    Cps.App
      (resumption,
       Cps.Int 1,
       Cps.CVar "exit",
       Cps.MVar "outer")
  in
  check_step
    "beta.op.S with an empty captured continuation"
    Cps_reduce_root.Beta_op_shallow
    expected
    source

let test_beta_op_multiple_frames () =
  let frame1 = identity_frame "a" "ja" "ma" in
  let frame2 = identity_frame "b" "jb" "mb" in
  let captured =
    Cps.Cons
      (frame1,
       Cps.Cons (frame2, Cps.Eps))
  in
  let handler =
    Cps.Handler
      ("operation_value", "resume", "handler_j", "handler_m",
       Cps.Send
         (Cps.CVar "handler_j",
          Cps.Var "resume",
          Cps.MVar "handler_m"))
  in
  let source =
    Cps.Op
      (Cps.MCons
         (Cps.CVar "exit",
          handler,
          Cps.MVar "outer"),
       Cps.Int 1,
       captured)
  in
  let resumed_cont =
    Cps.Cons
      (frame1,
       Cps.Cons
         (frame2,
          Cps.CVar "j0"))
  in
  let resumption =
    Cps.Lam
      ("y0", "j0", "m0",
       Cps.Send
         (resumed_cont,
          Cps.Var "y0",
          Cps.MVar "m0"))
  in
  let expected =
    Cps.Send
      (Cps.CVar "exit",
       resumption,
       Cps.MVar "outer")
  in
  check_step
    "beta.op.S preserves every captured frame"
    Cps_reduce_root.Beta_op_shallow
    expected
    source

let test_beta_op_open_capture_is_stuck () =
  let source =
    Cps.Op
      (Cps.MCons
         (Cps.CVar "exit",
          resuming_handler (),
          Cps.MVar "outer"),
       Cps.Int 1,
       Cps.CVar "captured")
  in
  check_stuck
    "beta.op.S with an open captured continuation"
    source

let test_unhandled_operation_is_stuck () =
  check_stuck
    "unhandled operation"
    (Cps.Op (Cps.Empty, Cps.Int 1, Cps.Eps))

let test_assoc () =
  let _k1, k2, continuation = two_frame_continuation () in
  let source =
    Cps.Send (continuation, Cps.Int 1, Cps.MVar "outer")
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
    Cps.Send
      (Cps.Cons (composed, Cps.CVar "tail"),
       Cps.Int 1,
       Cps.MVar "outer")
  in
  match Cps_reduce_root.contract_current_assoc (Fresh.create ()) source with
  | None -> failwith "assoc: expected a reduction"
  | Some step ->
      if step.rule <> Cps_reduce_root.Assoc then
        failwith "assoc: returned the wrong rule";
      if step.reduct <> expected then
        failwith
          (Printf.sprintf
             "assoc:\nexpected:\n%s\nactual:\n%s"
             (Format.asprintf "%a" Cps_pretty.pp_term expected)
             (Format.asprintf "%a" Cps_pretty.pp_term step.reduct))

let test_assoc_beta_let_diamond () =
  let _k1, k2, continuation = two_frame_continuation () in
  let source =
    Cps.Send (continuation, Cps.Int 1, Cps.MVar "outer")
  in
  let beta_first =
    match Cps_reduce_root.contract (Fresh.create ()) source with
    | Some { rule = Cps_reduce_root.Beta_let; reduct } -> reduct
    | _ -> failwith "assoc/beta.let diamond: beta.let did not apply"
  in
  let assoc_supply = Fresh.create () in
  let after_assoc =
    match Cps_reduce_root.contract_current_assoc assoc_supply source with
    | Some { rule = Cps_reduce_root.Assoc; reduct } -> reduct
    | _ -> failwith "assoc/beta.let diamond: assoc did not apply"
  in
  let assoc_then_beta =
    match Cps_reduce_root.contract assoc_supply after_assoc with
    | Some { rule = Cps_reduce_root.Beta_let; reduct } -> reduct
    | _ -> failwith "assoc/beta.let diamond: beta.let did not follow assoc"
  in
  let expected =
    Cps.Add
      (Cps.Cons (k2, Cps.CVar "tail"),
       Cps.Int 1,
       Cps.Int 2,
       Cps.MVar "outer")
  in
  if beta_first <> expected || assoc_then_beta <> expected then
    failwith "assoc/beta.let diamond does not converge"

let test_assoc_all_current_continuation_positions () =
  let _k1, _k2, continuation = two_frame_continuation () in
  let terms =
    [ Cps.Send (continuation, Cps.Int 1, Cps.MVar "m");
      Cps.Add
        (continuation, Cps.Var "x", Cps.Int 2, Cps.MVar "m");
      Cps.App
        (Cps.Var "f", Cps.Var "x", continuation, Cps.MVar "m");
      Cps.Op (Cps.MVar "m", Cps.Int 1, continuation) ]
  in
  List.iter
    (fun term ->
      match Cps_reduce_root.contract_current_assoc (Fresh.create ()) term with
      | Some { rule = Cps_reduce_root.Assoc; _ } -> ()
      | _ -> failwith "assoc is unavailable at a current-continuation position")
    terms

let test_assoc_requires_two_frames () =
  let source =
    Cps.Send
      (Cps.Cons
         (add_frame "x" "j" "m" 2,
          Cps.CVar "tail"),
       Cps.Int 1,
       Cps.MVar "outer")
  in
  match Cps_reduce_root.contract_current_assoc (Fresh.create ()) source with
  | None -> ()
  | Some _ -> failwith "assoc applied to a continuation with one frame"

let test_eta_let () =
  let identity = identity_frame "x" "j1" "m1" in
  let source =
    Cps.Op
      (Cps.MVar "m",
       Cps.Int 1,
       Cps.Cons (identity, Cps.CVar "j"))
  in
  let expected =
    Cps.Op (Cps.MVar "m", Cps.Int 1, Cps.CVar "j")
  in
  match Cps_reduce_root.contract_current_eta_let source with
  | Some { rule = Cps_reduce_root.Eta_let; reduct }
      when reduct = expected -> ()
  | Some step ->
      failwith
        (Printf.sprintf
           "eta.let:\nexpected:\n%s\nactual:\n%s"
           (Format.asprintf "%a" Cps_pretty.pp_term expected)
           (Format.asprintf "%a" Cps_pretty.pp_term step.reduct))
  | None ->
      failwith "eta.let: expected a reduction"

let test_eta_let_all_current_continuation_positions () =
  let continuation =
    Cps.Cons
      (identity_frame "x" "j1" "m1",
       Cps.CVar "tail")
  in
  let terms =
    [ Cps.Send (continuation, Cps.Int 1, Cps.MVar "m");
      Cps.Add
        (continuation, Cps.Var "x", Cps.Int 2, Cps.MVar "m");
      Cps.App
        (Cps.Var "f", Cps.Var "x", continuation, Cps.MVar "m");
      Cps.Op (Cps.MVar "m", Cps.Int 1, continuation) ]
  in
  List.iter
    (fun term ->
      match Cps_reduce_root.contract_current_eta_let term with
      | Some { rule = Cps_reduce_root.Eta_let; _ } -> ()
      | _ -> failwith "eta.let is unavailable at a continuation position")
    terms

let test_eta_let_rejects_nonidentity_frame () =
  let source =
    Cps.Op
      (Cps.MVar "m",
       Cps.Int 1,
       Cps.Cons
         (add_frame "x" "j" "m1" 2,
          Cps.CVar "tail"))
  in
  match Cps_reduce_root.contract_current_eta_let source with
  | None -> ()
  | Some _ -> failwith "eta.let eliminated a non-identity frame"

let test_eta_let_beta_let_diamond () =
  let source =
    Cps.Send
      (Cps.Cons
         (identity_frame "x" "j1" "m1",
          Cps.CVar "tail"),
       Cps.Int 1,
       Cps.MVar "outer")
  in
  let expected =
    Cps.Send (Cps.CVar "tail", Cps.Int 1, Cps.MVar "outer")
  in
  let by_beta =
    match Cps_reduce_root.contract (Fresh.create ()) source with
    | Some { rule = Cps_reduce_root.Beta_let; reduct } -> reduct
    | _ -> failwith "eta.let/beta.let diamond: beta.let did not apply"
  in
  let by_eta =
    match Cps_reduce_root.contract_current_eta_let source with
    | Some { rule = Cps_reduce_root.Eta_let; reduct } -> reduct
    | _ -> failwith "eta.let/beta.let diamond: eta.let did not apply"
  in
  if by_beta <> expected || by_eta <> expected then
    failwith "eta.let/beta.let diamond does not converge"

let () =
  test_beta_value ();
  test_eta_value ();
  test_eta_value_side_conditions ();
  test_beta_let ();
  test_delta_add ();
  test_handler_return ();
  test_beta_op_empty_capture ();
  test_beta_op_multiple_frames ();
  test_beta_op_open_capture_is_stuck ();
  test_unhandled_operation_is_stuck ();
  test_assoc ();
  test_assoc_beta_let_diamond ();
  test_assoc_all_current_continuation_positions ();
  test_assoc_requires_two_frames ();
  test_eta_let ();
  test_eta_let_all_current_continuation_positions ();
  test_eta_let_rejects_nonidentity_frame ();
  test_eta_let_beta_let_diamond ();
  test_contract_cont_lists_overlapping_rules ()
