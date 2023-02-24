module Utils

open FStar.List
open FStar.Tactics

open Compiler.Model

let rec lemma_append_enforced_locally_0 pi h lt1 lt2:
  Lemma 
    (requires (
      enforced_locally pi h lt1 /\
      enforced_locally pi (apply_changes h lt1) lt2))
    (ensures (
      enforced_locally pi h (lt1 @ lt2))) 
    (decreases (List.length lt1)) =
    match lt1 with
    | [] -> ()
    | e::[] -> begin
      assert (enforced_locally pi h [e]);
      calc (==) {
        enforced_locally pi (apply_changes h [e]) lt2;
        == {}
        enforced_locally pi h ([e] @ lt2);
      }
    end
    | e::t1 ->
      calc (==) {
        enforced_locally pi (apply_changes h (lt1)) lt2;
        == {}
        enforced_locally pi (apply_changes h (e::t1)) lt2;
        == {}
        enforced_locally pi (List.rev (e::t1) @ h) lt2;
        == { _ by (l_to_r [`List.Tot.Properties.rev_rev'] ) }
        enforced_locally pi ((List.rev (t1) @ [e]) @ h) lt2;
        == { _ by (l_to_r [`List.Tot.Properties.append_assoc]) }
        enforced_locally pi (List.rev (t1) @ ([e] @ h)) lt2;
        == {}
        enforced_locally pi (apply_changes ([e] @ h) t1) lt2;
    };
    assert (enforced_locally pi ([e]@h) t1);
    lemma_append_enforced_locally_0 pi ([e] @ h) t1 lt2;
    calc (==) {
        enforced_locally pi ([e] @ h) (t1 @ lt2);
        == {}
        enforced_locally pi (apply_changes h [e]) (t1 @ lt2);
        == { lemma_append_enforced_locally_0 pi h [e] (t1 @ lt2) }
        enforced_locally pi h ([e] @ (t1 @ lt2));
        == {}
        enforced_locally pi h (lt1 @ lt2);
      }

let lemma_append_enforced_locally pi:
  Lemma (forall h lt1 lt2.
      enforced_locally pi h lt1 /\
      enforced_locally pi (apply_changes h lt1) lt2 ==>
      enforced_locally pi h (lt1 @ lt2)) =
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_append_enforced_locally_0 pi))
  
let lemma_pi_enforced_locally (pi:monitorable_prop) (cmd:io_cmds) arg h :
  Lemma
    (requires (pi cmd arg h))
    (ensures (forall r. enforced_locally pi h [convert_call_to_event cmd arg r])) =
  introduce forall r. enforced_locally pi h [convert_call_to_event cmd arg r] with begin
    let e = convert_call_to_event cmd arg r in
    calc (==) {
      enforced_locally pi h [e];
      == {}
      (if has_event_respected_pi e pi h then enforced_locally pi (e::h) []
      else false);
      == {}
      pi cmd arg h;
    }
  end
