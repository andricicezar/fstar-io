module Witnessable

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open FStar.Ghost

open FStar.Monotonic.Heap
open MST.Repr
open MST.Tot

open ShareableType

class witnessable (t:Type) = {
  satisfy : (
      x:t -> pred:(#a:_ -> #rel:_ -> mref a rel -> Type0) -> sat:Type0{
          forall __t. to_Type __t == t ==> (sat <==> forall_refs pred #__t x)});
}

let satisfy_on_heap #t {| c:witnessable t |} x h (pred:mref_heap_pred) =
  c.satisfy x (fun #a #rel r -> pred r h)

#set-options "--print_implicits"

unfold
let force_retype (#a #b:Type0) (x:a) : Pure b (requires (a == b)) (ensures (fun _ -> True)) = x

let lemma_forall_refs_heap_force_retype_refs (pred:mref_pred) #a #rel (x:mref a rel) b:
  Lemma
    (requires (pred #a x /\ a == b))
    (ensures (pred #b #rel (force_retype x))) = ()

instance witnessable_mref (t:Type) (rel:FStar.Preorder.preorder t) {| c:witnessable t |} : witnessable (mref t rel) = {
  satisfy = (fun (x:mref t rel) pred ->
    introduce forall __t. to_Type (SRef __t) == mref t rel ==> (pred x <==> forall_refs pred #(SRef __t) (force_retype x)) with begin
      introduce to_Type (SRef __t) == mref t rel ==> (pred x <==> forall_refs pred #(SRef __t) (force_retype x)) with _. begin
        introduce pred x ==>  forall_refs pred #(SRef __t) (force_retype x) with _. (
          admit ();
          lemma_forall_refs_heap_force_retype_refs pred #t #rel x (to_Type __t);
          assert (forall_refs pred #(SRef __t) (force_retype x)) by (norm [delta_only [`%forall_refs];zeta;iota]; dump "H"));
        introduce forall_refs pred #(SRef __t) (force_retype x) ==> pred x with _. (
          admit ();
          lemma_forall_refs_heap_force_retype_refs pred #(to_Type (SRef __t)) #rel x t)
      end
    end;
    //by (norm [delta_only [`%forall_refs];zeta;iota];

    pred x);
}

instance witnessable_ref (t:Type) {| c:witnessable t |} : witnessable (ref t) = {
  satisfy = (fun x pred -> pred x);
}

instance witnessable_unit : witnessable unit = {
  satisfy = (fun _ _ -> True);
}

instance witnessable_int : witnessable int = {
  satisfy = (fun _ _ -> True);
}

instance witnessable_refinement (t:Type) {| c:witnessable t |} (p:t -> Type0) : witnessable (x:t{p x}) = {
  satisfy = (fun (x:t{p x}) pred -> c.satisfy x pred);
}

instance witnessable_arrow
  (t1:Type) (t2:Type)
  (pre:t1 -> st_pre)
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0))) // TODO: one cannot have pre-post depending on outside things.
: witnessable (x:t1 -> ST t2 (pre x) (post x)) = {
  satisfy = (fun _ _ -> True);
}

instance witnessable_option (t:Type) {| c:witnessable t |} : witnessable (option t) = {
  satisfy = (fun x pred ->
    match x with
    | None -> True
    | Some x' -> c.satisfy x' pred);}

instance witnessable_pair (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (t1 * t2) = {
  satisfy = (fun (x1, x2) pred -> c1.satisfy x1 pred /\ c2.satisfy x2 pred);
}

instance witnessable_sum (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (either t1 t2) = {
  satisfy = (fun x pred ->
    match x with
    | Inl x1 -> c1.satisfy x1 pred
    | Inr x2 -> c2.satisfy x2 pred);
}

let rec forall_in_list (l:list 'a) (pred:'a -> Type0) : Type0 =
  match l with
  | [] -> True
  | hd::tl -> pred hd /\ forall_in_list tl pred

instance witnessable_list (t:Type) {| c:witnessable t |} : witnessable (list t) = {
  satisfy = (fun l pred ->
    forall_in_list l (fun x -> c.satisfy x pred));
}


instance witnessable_llist (t:Type) {| c:witnessable t |} : witnessable (linkedList t) = {
  satisfy = (fun l pred ->
    match l with
    | LLNil -> True
    | LLCons x xsref -> c.satisfy x pred /\ pred xsref);
}

instance witnessable_univ_raise (t:Type u#a) {| c:witnessable t |} : witnessable (raise_t u#a u#b t) = {
  satisfy = (fun x -> c.satisfy (downgrade_val x));
}
