open Reflection

let print_help () =
  print_endline {|
Commands:
  :dstep       reduce the current DS term at the top level
  :cps         translate DS to CPS
  :cstep       reduce the current CPS term at the top level
  :cassoc      apply CPS assoc to the current continuation
  :ceta        eliminate an identity continuation frame
  :ds          translate CPS to DS
  :show        show the current term
  :new TERM    replace the current state with a DS term
  :help        show this help
  :quit        quit
|}

let string_of_translation_error = function
  | Ds_translate.Unexpected_cont_var j ->
      "unexpected continuation variable: " ^ j
  | Ds_translate.Unexpected_meta_var m ->
      "unexpected metacontinuation variable: " ^ m
  | Ds_translate.Free_handler_var h ->
      "free handler variable: " ^ h

let string_of_error = function
  | Repl_state.Expected_ds ->
      "this command requires a DS term"
  | Repl_state.Expected_cps ->
      "this command requires a CPS term"
  | Repl_state.No_ds_redex ->
      "no top-level DS redex"
  | Repl_state.No_cps_redex ->
      "no top-level CPS redex"
  | Repl_state.Ds_translation_error error ->
      string_of_translation_error error

let strip_prefix prefix text =
  let prefix_length = String.length prefix in
  let text_length = String.length text in
  if text_length >= prefix_length
     && String.sub text 0 prefix_length = prefix
  then
    Some
      (String.sub
         text
         prefix_length
         (text_length - prefix_length))
  else
    None

let run_action supply action state =
  match Repl_state.apply supply action state with
  | Error error ->
      Printf.eprintf "error: %s\n%!" (string_of_error error);
      state

  | Ok outcome ->
      Option.iter
        (fun rule -> Printf.printf "[%s]\n%!" rule)
        outcome.rule_name;

      Repl_state.print_state outcome.state;
      outcome.state

let rec loop supply state =
  print_string (Repl_state.prompt state);
  flush stdout;

  match read_line () with
  | exception End_of_file ->
      print_newline ()

  | line ->
      let line = String.trim line in

      match line with
      | "" ->
          loop supply state

      | ":quit" ->
          ()

      | ":help" ->
          print_help ();
          loop supply state

      | ":show" ->
          Repl_state.print_state state;
          loop supply state

      | ":dstep" ->
          let state' =
            run_action supply Repl_state.Ds_step state
          in
          loop supply state'

      | ":cps" ->
          let state' =
            run_action supply Repl_state.To_cps state
          in
          loop supply state'

      | ":cstep" ->
          let state' =
            run_action supply Repl_state.Cps_step state
          in
          loop supply state'

      | ":cassoc" ->
          let state' =
            run_action supply Repl_state.Cps_assoc state
          in
          loop supply state'

      | ":ceta" ->
          let state' =
            run_action supply Repl_state.Cps_eta state
          in
          loop supply state'

      | ":ds" ->
          let state' =
            run_action supply Repl_state.To_ds state
          in
          loop supply state'

      | _ ->
          begin match strip_prefix ":new " line with
          | Some source ->
              begin
                try
                  let term = Ds_parse.comp source in
                  let state' = Repl_state.Ds_state term in
                  Repl_state.print_state state';
                  loop supply state'
                with
                | Ds_parse.Error message ->
                    Printf.eprintf "parse error: %s\n%!" message;
                    loop supply state
              end

          | None ->
              Printf.eprintf
                "unknown command: %s\n\
                 type :help to see the available commands\n%!"
                line;
              loop supply state
          end
let rec read_initial_state supply =
  print_string "Enter a DS term: ";
  flush stdout;

  match read_line () with
  | exception End_of_file ->
      ()

  | source ->
      begin
        try
          let term = Ds_parse.comp source in
          let state = Repl_state.Ds_state term in
          Repl_state.print_state state;
          loop supply state
        with
        | Ds_parse.Error message ->
            Printf.eprintf "parse error: %s\n%!" message;
            read_initial_state supply
      end

let () =
  let supply = Fresh.create () in
  print_endline "Reflection REPL";
  print_endline "Type :help to see the available commands.";
  read_initial_state supply
