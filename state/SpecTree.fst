module SpecTree

open FStar.Ghost
open FStar.Monotonic.Heap
open MST.Tot
open Witnessable
open TargetLang

type err =
| Contract_failure : string -> err

type resexn a = either a err

instance witnessable_err : witnessable err = {
  satisfy = (fun _ _ -> True);
}

instance witnessable_resexn #t {| witnessable t |} : witnessable (resexn t) =
  witnessable_sum t err

(** **** Tree **)
type tree (a: Type) =
  | Leaf : tree a
  | EmptyNode: left: tree a -> right: tree a -> tree a
  | Node: data: a -> left: tree a -> right: tree a -> tree a

let root (t:(tree 'a){Node? t}) = Node?.data t
(** TODO: refactor these into two utils **)
let left (t:(tree 'a){Node? t \/ EmptyNode? t}) : tree 'a =
  match t with
  | Node _ lt _ -> lt
  | EmptyNode lt _ -> lt

let right (t:(tree 'a){Node? t \/ EmptyNode? t}) : tree 'a =
  match t with
  | Node _ _ rt -> rt
  | EmptyNode _ rt -> rt

let rec equal_trees (t1:tree 'a) (t2:tree 'a) =
  match t1, t2 with
  | Leaf, Leaf -> True
  | EmptyNode lhs1 rhs1, EmptyNode lhs2 rhs2 -> equal_trees lhs1 lhs2 /\ equal_trees rhs1 rhs2
  | Node x lhs1 rhs1, Node y lhs2 rhs2 -> x == y /\ equal_trees lhs1 lhs2 /\ equal_trees rhs1 rhs2
  | _, _ -> False

(* The function above is really just propositional equality. See this proof. *)
let rec equal_trees_prop (t1 t2 : tree 'a) : Lemma (equal_trees t1 t2 <==> t1 == t2)
  [SMTPat (equal_trees t1 t2)]
  =
  match t1, t2 with
  | Leaf,            Leaf -> ()
  | EmptyNode l1 r1, EmptyNode l2 r2
  | Node _ l1 r1,    Node _ l2 r2 -> equal_trees_prop l1 l2; equal_trees_prop r1 r2
  | _ -> ()

let rec map_tree (t:tree 'a) (f:'a -> 'b) : tree 'b =
  match t with
  | Leaf -> Leaf
  | EmptyNode lhs rhs -> EmptyNode (map_tree lhs f) (map_tree rhs f)
  | Node x lhs rhs -> Node (f x) (map_tree lhs f) (map_tree rhs f)

let rec map_fuse (t:tree 'a) (f:'a -> 'b) (g : 'b -> 'c)
  : Lemma (map_tree (map_tree t f) g == map_tree t (fun x -> g (f x)))
  =
  match t with
  | Leaf -> ()
  | EmptyNode lhs rhs -> map_fuse lhs f g; map_fuse rhs f g
  | Node x lhs rhs -> map_fuse lhs f g; map_fuse rhs f g

let rec map_id (t:tree 'a)
  : Lemma (map_tree t (fun x -> x) == t)
  =
  match t with
  | Leaf -> ()
  | EmptyNode lhs rhs -> map_id lhs; map_id rhs
  | Node x lhs rhs -> map_id lhs; map_id rhs

let rec map_ext (t:tree 'a) (f:'a -> 'b) (g : 'a -> 'b)
  : Lemma (requires (forall x. f x == g x))
          (ensures (map_tree t f == map_tree t g))
  =
  match t with
  | Leaf -> ()
  | EmptyNode lhs rhs -> map_ext lhs f g; map_ext rhs f g
  | Node x lhs rhs -> map_ext lhs f g; map_ext rhs f g


type cb_check pspec (t1:Type) (t2:Type) {| c2: witnessable t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
  (x:t1)
  (eh0:FStar.Ghost.erased heap{pre x eh0}) =
  (r:t2 -> ST (resexn unit) (fun h1 -> post_targetlang_arrow pspec eh0 r h1) (fun h1 rck h1' ->
    h1 == h1' /\ (Inl? rck ==> post x eh0 r h1)))

type select_check
  pspec
  (t1:Type) (t2:Type) {| c2: witnessable t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0))) =
  x:t1 -> ST (
    eh0:FStar.Ghost.erased heap{pre x eh0} & cb_check pspec t1 t2 #c2 pre post x eh0
  ) (pre x) (fun h0 r h1 -> FStar.Ghost.reveal (dfst r) == h0 /\ h0 == h1)

noeq
type pck_spec (pspec:targetlang_pspec) =
| Spec :
    bit:bool ->
    argt:Type u#a ->
    wt_argt:witnessable argt ->
    pre:(argt -> st_pre) ->
    rett:Type u#b ->
    wt_rett:witnessable rett ->
    (post:(x:argt -> h0:heap -> st_post' (resexn rett) (pre x h0)))
    -> pck_spec pspec


noeq
type hoc pspec : (s:pck_spec pspec) -> Type =
| EnforcePre :
    #s:(pck_spec pspec){Spec?.bit s == true} ->
    check:(select_check pspec (Spec?.argt s) unit
                        (pre_targetlang_arrow pspec #(Spec?.argt s) #(Spec?.wt_argt s))
                        (fun x _ _ h1 -> (Spec?.pre s) x h1)) ->
    c_post:(x:(Spec?.argt s) -> r:(resexn (Spec?.rett s)) -> Lemma (forall h0 h1. (Spec?.post s) x h0 r h1 ==> post_targetlang_arrow pspec #(resexn (Spec?.rett s)) #(witnessable_resexn #_ #(Spec?.wt_rett s)) h0 r h1))
    -> hoc pspec s

| EnforcePost :
    #s:(pck_spec pspec){Spec?.bit s == false} ->
    c_pre:(x:(Spec?.argt s) -> Lemma (forall h0. (Spec?.pre s) x h0 ==> pre_targetlang_arrow pspec #(Spec?.argt s) #(Spec?.wt_argt s) x h0)) ->
    c_post:(x:(Spec?.argt s) -> e:err -> Lemma (forall h0 h1. (Spec?.pre s) x h0 /\ post_targetlang_arrow pspec #_ #(witnessable_resexn #_ #(Spec?.wt_rett s)) h0 (Inr e) h1 ==> (Spec?.post s) x h0 (Inr e) h1)) ->
    check:(select_check pspec (Spec?.argt s) (resexn (Spec?.rett s)) #(witnessable_resexn #_ #(Spec?.wt_rett s)) (Spec?.pre s) (Spec?.post s))
    -> hoc pspec s

type pck_hoc pspec =
  s:pck_spec pspec & (hoc pspec s)

private
let myspec : pck_spec concrete_spec =
  Spec
    true
    (ref int)
    (witnessable_ref int)
    (fun x h -> sel h x > 5)
    unit
    witnessable_unit
    (fun _ -> post_targetlang_arrow concrete_spec)

private
let test_pre : hoc concrete_spec myspec =
  EnforcePre
    (fun (x:(Spec?.argt myspec)) ->
      let x : ref int = x in
      let eh0 = get_heap () in
      let check : cb_check concrete_spec (ref int) unit (pre_targetlang_arrow concrete_spec #(Spec?.argt myspec) #(Spec?.wt_argt myspec)) (fun x _ _ h1 -> (Spec?.pre myspec) x h1) x eh0 = (
        fun _ ->
          assert (witnessed (contains_pred x));
          recall (contains_pred x);
          if read x > 5 then Inl ()
          else Inr (Contract_failure "less than 5")
      ) in
      (| eh0, check |))
    (fun _ _ -> ())

private
let myspec' : pck_spec concrete_spec =
  Spec
    false
    (ref int)
    (witnessable_ref int)
    (pre_targetlang_arrow concrete_spec)
    unit
    witnessable_unit
    (fun x h0 r h1 -> (Inr? r \/ sel h1 x > 5) /\ post_targetlang_arrow concrete_spec h0 r h1)

private
let test_post : hoc concrete_spec myspec' =
  EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun x ->
      let x : ref int = x in
      let eh0 = get_heap () in
      let check : cb_check concrete_spec (ref int) (resexn unit) #(witnessable_resexn #_ #(Spec?.wt_rett myspec')) (Spec?.pre myspec') (Spec?.post myspec') x eh0 = (
        fun _ ->
          assert (witnessed (contains_pred x));
          recall (contains_pred x);
          if read x > 5 then Inl ()
          else Inr (Contract_failure "less than 5")
      ) in
      (| eh0, check |))

let spec_tree pspec = tree (pck_spec pspec)
let hoc_tree #pspec (st:spec_tree pspec) =
  hocs:(tree (pck_hoc pspec)){equal_trees st (map_tree hocs dfst)}
