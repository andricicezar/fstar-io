module QTypes.HelperTactics

open FStar.Tactics.V1
open QTypes.OpenValComp

(** Tactics to simplify qTypes **)

let simplify_stack_ops () : Tac unit =
   l_to_r [`lem_hd_stack; `lem_tail_stack_inverse]

let simplify_qType_g g (x:term) : Tac term =
  norm_term_env g [
    delta_only [
      `%fs_oval; `%fs_val; `%qUnit; `%qBool; `%qString; `%qResexn;
      `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Plus;
      `%op_Hat_Subtraction_Greater_Bang_At;
      `%get_rel; `%get_Type;
      `%q_io_args; `%q_io_res;
      `%Mkdtuple2?._1;`%Mkdtuple2?._2];
    zeta;
    iota;
    simplify
  ] x

let simplify_qType (x:term) : Tac term = simplify_qType_g (top_env ()) x
