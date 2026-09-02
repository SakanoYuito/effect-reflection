open Reflection

let ex1 = 
  Ds.Handle
    (Ds.Let
      ("v",
       Ds.Op (Ds.Int 1),
       Ds.Add (Ds.Var "v", Ds.Int 2)),
     "x",
     "k", 
     Ds.Let
       ("y",
        Ds.App (Ds.Var "k", Ds.Var "x"),
        Ds.Add (Ds.Var "y", Ds.Int 3)))

let ex2 = Ds_parse.comp
  "let x = return 1 in x + 2"

let () =
  let s = Format.asprintf "%a" Ds_pretty.pp_comp ex2 in 
  let n = Fresh.create () in 
  let t  = Cps_translate.program n ex2 in 
  let t' = Format.asprintf "%a" Cps_pretty.pp_root t in 
  print_endline s;
  print_endline t'
