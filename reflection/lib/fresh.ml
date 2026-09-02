type t = {
  counters : (string, int) Hashtbl.t
}

let create () = 
  { counters = Hashtbl.create 16 }

let name supply base = 
  let n = 
    Option.value
      (Hashtbl.find_opt supply.counters base)
      ~default:0
  in
  Hashtbl.replace supply.counters base (n + 1);
  base ^ string_of_int n
