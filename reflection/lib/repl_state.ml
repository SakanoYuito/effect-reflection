type t = 
  | Ds_state of Ds.comp
  | Cps_state of Cps.root

type action = 
  | Ds_step
  | To_cps
  | Cps_step
  | Cps_assoc
  | Cps_eta
  | To_ds

type error = 
  | Expected_ds
  | Expected_cps
  | No_ds_redex
  | No_cps_redex
  | Ds_translation_error of Ds_translate.error

type outcome = {
  state : t;
  rule_name : string option;
}

let ds_rule_name = function
  | Ds_reduce_root.Beta_value -> "β.v"
  | Ds_reduce_root.Beta_let -> "β.let"
  | Ds_reduce_root.Eta_value -> "η.v"
  | Ds_reduce_root.Eta_let -> "η.let"
  | Ds_reduce_root.Delta_add -> "δ.+"
  | Ds_reduce_root.Handler_return -> "h.return"
  | Ds_reduce_root.Beta_op -> "β.op.S"
  | Ds_reduce_root.Assoc -> "assoc"

let cps_rule_name = function
  | Cps_reduce_root.Beta_value -> "β.v"
  | Cps_reduce_root.Beta_let -> "β.let"
  | Cps_reduce_root.Eta_value -> "η.v"
  | Cps_reduce_root.Eta_let -> "η.let"
  | Cps_reduce_root.Delta_add -> "δ.+"
  | Cps_reduce_root.Handler_return -> "h.return"
  | Cps_reduce_root.Beta_op_shallow -> "β.op.S"
  | Cps_reduce_root.Assoc -> "assoc"

let apply supply action state = 
  match action, state with
  | Ds_step, Ds_state p ->
      begin match Ds_reduce_root.contract supply p with
      | Some step ->
          Ok {
            state = Ds_state step.reduct;
            rule_name = Some (ds_rule_name step.rule);
          }
      | None -> Error No_ds_redex
      end
  
  | To_cps, Ds_state p ->
      Ok {
        state = Cps_state (Cps_translate.program supply p);
        rule_name = None;
      }

  | Cps_step, Cps_state (Cps.Root (j, m, p)) ->
    begin match Cps_reduce_root.contract supply p with
    | Some step -> 
        Ok {
          state = Cps_state (Cps.Root (j, m, step.reduct));
          rule_name = Some (cps_rule_name step.rule);
        }
    | None -> Error No_cps_redex
    end

  | Cps_assoc, Cps_state (Cps.Root (j, m, p)) ->
    begin match Cps_reduce_root.contract_current_assoc supply p with
    | Some step ->
        Ok {
          state = Cps_state (Cps.Root (j, m, step.reduct));
          rule_name = Some (cps_rule_name step.rule);
        }
    | None -> Error No_cps_redex
    end

  | Cps_eta, Cps_state (Cps.Root (j, m, p)) ->
    begin match Cps_reduce_root.contract_current_eta_let p with
    | Some step ->
        Ok {
          state = Cps_state (Cps.Root (j, m, step.reduct));
          rule_name = Some (cps_rule_name step.rule);
        }
    | None -> Error No_cps_redex
    end
  
  | To_ds, Cps_state root ->
      begin match Ds_translate.root root with
      | Ok p -> 
          Ok {
            state = Ds_state p;
            rule_name = None;
          }
      | Error error -> Error (Ds_translation_error error)
      end
  
  | (Ds_step | To_cps), Cps_state _ -> Error Expected_ds
  | (Cps_step | Cps_assoc | Cps_eta | To_ds), Ds_state  _ -> Error Expected_cps

let print_state = function
  | Ds_state p ->
      Format.printf "@[<v>DS:@,%a@]@."
        Ds_pretty.pp_comp p

  | Cps_state r ->
      Format.printf "@[<v>CPS:@,%a@]@."
        Cps_pretty.pp_root r
      
let prompt = function
  | Ds_state _ -> "ds> "
  | Cps_state _ -> "cps> "
