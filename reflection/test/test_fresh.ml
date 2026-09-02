open Reflection

let check_equal label expected actual = 
  if expected <> actual then
    failwith
      (Printf.sprintf
        "%s: expected %S, but got %S"
        label expected actual)

let test_counters () =
  let supply = Fresh.create () in 

  check_equal "first x"  "x0" (Fresh.name supply "x");
  check_equal "first y"  "y0" (Fresh.name supply "y");
  check_equal "second x" "x1" (Fresh.name supply "x");
  check_equal "third x"  "x2" (Fresh.name supply "x");
  check_equal "first z"  "z0" (Fresh.name supply "z");
  check_equal "second y" "y1" (Fresh.name supply "y")

let () =
  test_counters ()
  