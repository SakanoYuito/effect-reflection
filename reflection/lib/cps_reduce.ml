type crumb =
  | Root_body

  | Send_cont
  | Send_value
  | Send_meta

  | Add_cont
  | Add_left
  | Add_right
  | Add_meta

  | App_function
  | App_argument
  | App_cont
  | App_meta

  | Op_meta
  | Op_value
  | Op_cont

  | Lambda_body
  | Frame_body
  | Handler_body

  | Cons_frame
  | Cons_tail

  | Mcons_cont
  | Mcons_handler
  | Mcons_tail

type path = crumb list

type candidate = {
  rule : Cps_reduce_root.rule;
  path : path;
}

(* let rec redexes_cont path cont = 
  let here = Cps_reduce_root.contract_cont  *)