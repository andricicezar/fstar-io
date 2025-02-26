module Witnessable

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Universe
open FStar.Ghost

open FStar.Monotonic.Heap
open MST.Repr
open MST.Tot

class witnessable (t:Type) = {
  satisfy : t -> (#a:_ -> #rel:_ -> mref a rel -> Type0) -> Type0;
  satisfy_on_heap : t -> heap -> mref_heap_pred -> Type0;
}
instance witnessable_mref (t:Type) (rel:FStar.Preorder.preorder t) {| c:witnessable t |} : witnessable (mref t rel) = {
  satisfy = (fun x pred -> pred x);
  satisfy_on_heap = (fun x h pred -> pred x h);
}

instance witnessable_ref (t:Type) {| c:witnessable t |} : witnessable (ref t) = {
  satisfy = (fun x pred -> pred x);
  satisfy_on_heap = (fun x h pred -> pred x h);
}

instance witnessable_unit : witnessable unit = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
}

instance witnessable_int : witnessable int = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
}

instance witnessable_refinement (t:Type) {| c:witnessable t |} (p:t -> Type0) : witnessable (x:t{p x}) = {
  satisfy = (fun (x:t{p x}) pred -> c.satisfy x pred);
  satisfy_on_heap = (fun (x:t{p x}) h pred -> c.satisfy_on_heap x h pred);
}

instance witnessable_arrow
  (t1:Type) (t2:Type)
  (pre:t1 -> st_pre)
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0))) // TODO: one cannot have pre-post depending on outside things.
: witnessable (x:t1 -> ST t2 (pre x) (post x)) = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
}

instance witnessable_option (t:Type) {| c:witnessable t |} : witnessable (option t) = {
  satisfy = (fun x pred ->
    match x with
    | None -> True
    | Some x' -> c.satisfy x' pred);
  satisfy_on_heap = (fun x h pred ->
    match x with
    | None -> True
    | Some x' -> c.satisfy_on_heap x' h pred);}

instance witnessable_pair (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (t1 * t2) = {
  satisfy = (fun (x1, x2) pred -> c1.satisfy x1 pred /\ c2.satisfy x2 pred);
  satisfy_on_heap = (fun (x1, x2) h pred -> c1.satisfy_on_heap x1 h pred /\ c2.satisfy_on_heap x2 h pred);
}

instance witnessable_sum (t1:Type) (t2:Type) {| c1:witnessable t1 |} {| c2:witnessable t2 |} : witnessable (either t1 t2) = {
  satisfy = (fun x pred ->
    match x with
    | Inl x1 -> c1.satisfy x1 pred
    | Inr x2 -> c2.satisfy x2 pred);
  satisfy_on_heap = (fun x h pred ->
    match x with
    | Inl x1 -> c1.satisfy_on_heap x1 h pred
    | Inr x2 -> c2.satisfy_on_heap x2 h pred);
}

let rec forall_in_list (l:list 'a) (pred:'a -> Type0) : Type0 =
  match l with
  | [] -> True
  | hd::tl -> pred hd /\ forall_in_list tl pred

instance witnessable_list (t:Type) {| c:witnessable t |} : witnessable (list t) = {
  satisfy = (fun l pred ->
    forall_in_list l (fun x -> c.satisfy x pred));
  satisfy_on_heap = (fun l h pred ->
    forall_in_list l (fun x -> c.satisfy_on_heap x h pred));
}


instance witnessable_llist (t:Type) {| c:witnessable t |} : witnessable (linkedList t) = {
  satisfy = (fun l pred ->
    match l with
    | LLNil -> True
    | LLCons x xsref -> c.satisfy x pred /\ pred xsref);
  satisfy_on_heap = (fun l h pred ->
    match l with
    | LLNil -> True
    | LLCons x xsref -> c.satisfy_on_heap x h pred /\ pred xsref h
  );
}

instance witnessable_univ_raise (t:Type u#a) {| c:witnessable t |} : witnessable (raise_t u#a u#b t) = {
  satisfy = (fun x -> c.satisfy (downgrade_val x));
  satisfy_on_heap = (fun x -> c.satisfy_on_heap (downgrade_val x));
}
