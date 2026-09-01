type pure = 
  | Hole 
  | Let_rhs of Ds.name * pure * Ds.comp


let rec plug context term = 
  match context with
  | Hole -> term
  | Let_rhs (x, context, body) -> Ds.Let (x, plug context term, body)

let rec decompose_operation = function
  | Ds.Op v -> Some (Hole, v)
  | Ds.Let (x, p, q) -> 
      Option.map
        (fun (context, v) -> (Let_rhs (x, context, q), v))
        (decompose_operation p)
  | _ -> None

