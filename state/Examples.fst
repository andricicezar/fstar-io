module Examples

open FStar.Preorder
open SharedRefs
open Witnessable

type grade =
| NotGraded
| MaxGrade
| MinGrade

instance witnessable_grade : witnessable grade = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
  satisfy_on_heap_monotonic = (fun _ _ _ _ -> ());
  pwitness = (fun _ _ -> (fun () -> ()));
}

let grade_preorder : preorder grade = fun g1 g2 ->
  match g1 with
  | NotGraded -> True
  | _ -> g1 == g2

let no_cycles (ll:linkedList int) (h:heap) = admit ()
let sorted (ll:linkedList int) (h:heap) = admit ()
let same_elements (ll:linkedList int) (h0 h1:heap) = admit ()

type student_solution =
  ll:linkedList int -> SST (option unit)
    (requires (fun h0 ->
      no_cycles ll h0 /\
      forall_refs_heap contains_pred h0 #(SLList SNat) ll /\ forall_refs_heap is_shared h0 #(SLList SNat) ll))
    (ensures (fun h0 r h1 ->
      (Some? r ==> no_cycles ll h1 /\ sorted ll h1 /\ same_elements ll h0 h1) /\
      modifies_only_shared h0 h1 /\ gets_shared Set.empty h0 h1))

let wss : witnessable (list (mref grade grade_preorder * student_solution)) = admit ()

let rec grading_done (sts: list (mref grade grade_preorder * student_solution)) h =
  match sts with
  | [] -> True
  | hd::tl -> sel h (fst hd) =!= NotGraded /\ grading_done tl h

let generate_llist (l:list int) : SST (linkedList int) (fun h0 -> True) (fun h0 r h1 -> True) = admit () (** not sure what specs are needed here **)
let share_llist (l:linkedList int) : SST unit (fun h0 -> True) (fun h0 r h1 -> True) = admit () (** not sure what specs are needed here **)

let rec auto_grader
  (l:list int)
  (sts: list (mref grade grade_preorder * student_solution))
  : SST unit
    (requires (fun h0 -> wss.satisfy_on_heap sts h0 (fun r h0 -> ~(is_shared r h0))))
    (ensures (fun h0 () h1 ->
      wss.satisfy_on_heap sts h1 (fun r h0 -> ~(is_shared r h0)) /\
      grading_done sts h1
      )) =
  match sts with
  | [] -> ()
  | (gr, hw)::tl -> begin
    let ll = generate_llist l in
    share_llist ll;
    admit ();
    (match hw ll with
    | Some _ -> sst_write'' gr MaxGrade
    | NoOps -> sst_write'' gr MinGrade);
    auto_grader l tl
  end
