open Reflection

let string_of_name_set names =
  names |> Name_set.elements |> String.concat ", " |> Printf.sprintf "{%s}"

let check_set label expected actual =
  if not (Name_set.equal expected actual) then
    failwith
      (Printf.sprintf
        "%s:\nexpected %s\nactual   %s"
        label
        (string_of_name_set expected)
        (string_of_name_set actual))

let test1 () = 
  (* v : λx. return x
     fv(v) = ∅ *)
  let term = 
    Ds.Lam ("x", Ds.Return (Ds.Var "x"))
  in let expected = 
    Name_set.empty
  in let actual = 
    Ds_free_vars.value term
  in check_set "λx. return x" expected actual

let test2 () = 
  (* p : let x = op y in x + z
     fv(p) = {y, z} *)
  let term = 
    Ds.Let ("x", Ds.Op (Ds.Var "y"), Ds.Add (Ds.Var "x", Ds.Var "z"))
  in let expected = 
    Name_set.of_list ["y"; "z"]
  in let actual = 
    Ds_free_vars.comp term
  in check_set "let x = op y in x + z" expected actual

let test3 () =
  (* p : handle op x with x, k -> k x
     fv(p) = {x} *)
  let term = 
    Ds.Handle
      (Ds.Op (Ds.Var "x"),
       "x", "k",
       Ds.App (Ds.Var "k", Ds.Var "x"))
  in let expected = 
    Name_set.singleton "x"
  in let actual = 
    Ds_free_vars.comp term
  in check_set "handle op x with x, k -> k x" expected actual


let () = 
  test1 ();
  test2 ();
  test3 ();

