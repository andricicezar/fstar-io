module SpecTree

open FStar.Ghost
open FStar.Monotonic.Heap
open MST.Tot
open Witnessable
open PolyIface

type err =
| Contract_failure : string -> err

type resexn (a:Type u#a) : Type u#a = either a err

instance witnessable_err : witnessable err = {
  satisfy = (fun _ _ -> True);
}
instance poly_iface_err a3p : poly_iface a3p err = {
  wt = witnessable_err;
}
 
instance witnessable_resexn t {| witnessable t |} : witnessable (resexn t) =
  witnessable_sum t err
instance poly_iface_resexn a3p t1 {| c1:poly_iface a3p t1 |} : poly_iface a3p (resexn t1) =
  poly_iface_sum a3p t1 #c1 err
 
(** **** Tree **)
type tree (a: Type u#a) =
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


type cb_check a3p (t1:Type) (t2:Type) {| c2: witnessable t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
  (x:t1)
  (eh0:FStar.Ghost.erased heap{pre x eh0}) =
  (r:t2 -> ST (resexn unit) (fun h1 -> post_poly_arrow a3p eh0 r h1) (fun h1 rck h1' ->
    h1 == h1' /\ (Inl? rck ==> post x eh0 r h1)))

type select_check
  a3p
  (t1:Type) (t2:Type) {| c2: witnessable t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0))) =
  x:t1 -> ST (
    eh0:FStar.Ghost.erased heap{pre x eh0} & cb_check a3p t1 t2 #c2 pre post x eh0
  ) (pre x) (fun h0 r h1 -> FStar.Ghost.reveal (dfst r) == h0 /\ h0 == h1)

open FStar.Tactics.Typeclasses

#set-options "--print_implicits --print_universes"

noeq
type pck_spec =
| SpecErr00 :
    bit:bool ->
    argt:Type u#0 ->
    wt_argt:witnessable argt ->
    pre:(argt -> st_pre) ->
    rett:Type u#0 ->
    wt_rett:witnessable rett ->
    (post:(x:argt -> h0:heap -> st_post' (resexn rett) (pre x h0))) ->
    pck_spec
| SpecErr10 :
    bit:bool ->
    argt:Type u#1 ->
    wt_argt:witnessable argt ->
    pre:(argt -> st_pre) ->
    rett:Type u#0 ->
    wt_rett:witnessable rett ->
    (post:(x:argt -> h0:heap -> st_post' (resexn rett) (pre x h0))) ->
    pck_spec
| Spec00 :
    bit:bool ->
    argt:Type u#0 ->
    wt_argt:witnessable argt ->
    pre:(argt -> st_pre) ->
    rett:Type u#0 ->
    wt_rett:witnessable rett ->
    (post:(x:argt -> h0:heap -> st_post' rett (pre x h0))) ->
    pck_spec
| Spec10 :
    bit:bool ->
    argt:Type u#1 ->
    wt_argt:witnessable argt ->
    pre:(argt -> st_pre) ->
    rett:Type u#0 ->
    wt_rett:witnessable rett ->
    (post:(x:argt -> h0:heap -> st_post' rett (pre x h0))) ->
    pck_spec

let argt0 (p:pck_spec{Spec00? p \/ SpecErr00? p}) : Type u#0 =
  match p with
  | SpecErr00 _ argt _ _ _ _ _ -> argt
  | Spec00 _ argt _ _ _ _ _ -> argt

let wt_argt0 (p:pck_spec{Spec00? p \/ SpecErr00? p}) : witnessable (argt0 p) =
  match p with
  | SpecErr00 _ _ wt _ _ _ _ -> wt
  | Spec00 _ _ wt _ _ _ _ -> wt

let argt1 (p:pck_spec{SpecErr10? p \/ Spec10? p}) : Type u#1 =
  match p with
  | SpecErr10 _ argt _ _ _ _ _ -> argt  
  | Spec10 _ argt _ _ _ _ _ -> argt

let wt_argt1 (p:pck_spec{SpecErr10? p \/ Spec10? p}) : witnessable (argt1 p) =
  match p with
  | SpecErr10 _ _ wt _ _ _ _ -> wt
  | Spec10 _ _ wt _ _ _ _ -> wt

let rett0 (p:pck_spec) : Type u#0 =
  match p with
  | SpecErr00 _ _ _ _ rett _ _ -> rett
  | SpecErr10 _ _ _ _ rett _ _ -> rett
  | Spec00 _ _ _ _ rett _ _ -> rett
  | Spec10 _ _ _ _ rett _ _ -> rett

let wt_rett0 (p:pck_spec) : witnessable (rett0 p) =
  match p with
  | SpecErr00 _ _ _ _ _ wt _ -> wt
  | SpecErr10 _ _ _ _ _ wt _ -> wt
  | Spec00 _ _ _ _ _ wt _ -> wt
  | Spec10 _ _ _ _ _ wt _ -> wt

let bit (p:pck_spec) : bool =
  match p with
  | SpecErr00 b _ _ _ _ _ _ -> b
  | SpecErr10 b _ _ _ _ _ _ -> b
  | Spec00 b _ _ _ _ _ _ -> b
  | Spec10 b _ _ _ _ _ _ -> b

let pre0 (p:pck_spec{Spec00? p \/ SpecErr00? p}) : argt0 p -> st_pre =
  match p with
  | SpecErr00 _ _ _ pre _ _ _ -> pre
  | Spec00 _ _ _ pre _ _ _ -> pre

let pre1 (p:pck_spec{SpecErr10? p \/ Spec10? p}) : argt1 p -> st_pre =
  match p with
  | SpecErr10 _ _ _ pre _ _ _ -> pre
  | Spec10 _ _ _ pre _ _ _ -> pre

noeq
type hoc a3p : (s:pck_spec) -> Type =
| TrivialPre :
    #s:pck_spec{Spec00? s /\ bit s == true} ->
    c_pre:(x:(argt0 s) -> 
        Lemma (forall h0. pre_poly_arrow a3p #(argt0 s) #(wt_argt0 s) x h0 ==> (pre0 s) x h0)) ->
    c_post:(x:(argt0 s) -> r:(rett0 s) -> 
        Lemma (forall h0 h1. (Spec00?.post s) x h0 r h1 ==> post_poly_arrow a3p #(rett0 s) #(wt_rett0 s) h0 r h1))
    -> hoc a3p s

| TrivialPost00 :
    #s:pck_spec{Spec00? s /\ bit s == false} ->
    c_pre:(x:(argt0 s) ->
        Lemma (forall h0. (pre0 s) x h0 ==> pre_poly_arrow a3p #(argt0 s) #(wt_argt0 s) x h0)) ->
    c_post:(x:(argt0 s) -> r:(rett0 s) -> 
        Lemma (forall h0 h1. post_poly_arrow a3p #(rett0 s) #(wt_rett0 s) h0 r h1 ==> (Spec00?.post s) x h0 r h1))
    -> hoc a3p s

| TrivialPost10 :
    #s:pck_spec{Spec10? s /\ bit s == false} ->
    c_pre:(x:(argt1 s) ->
        Lemma (forall h0. (pre1 s) x h0 ==> pre_poly_arrow a3p #(argt1 s) #(wt_argt1 s) x h0)) ->
    c_post:(x:(argt1 s) -> r:(rett0 s) -> 
        Lemma (forall h0 h1. post_poly_arrow a3p #(rett0 s) #(wt_rett0 s) h0 r h1 ==> (Spec10?.post s) x h0 r h1))
    -> hoc a3p s

| EnforcePre00 :
    #s:pck_spec{SpecErr00? s /\ bit s == true} ->
    check:(select_check a3p (argt0 s) unit
                        (pre_poly_arrow a3p #(argt0 s) #(wt_argt0 s))
                        (fun x _ _ h1 -> (pre0 s) x h1)) ->
    c_post:(x:(argt0 s) -> r:(resexn (rett0 s)) -> 
        Lemma (forall h0 h1. (SpecErr00?.post s) x h0 r h1 ==> post_poly_arrow a3p #(resexn (rett0 s)) #(witnessable_resexn _ #(wt_rett0 s)) h0 r h1))
    -> hoc a3p s

| EnforcePre10 :
    #s:pck_spec{SpecErr10? s /\ bit s == true} ->
    check:(select_check a3p (argt1 s) unit
                        (pre_poly_arrow a3p #(argt1 s) #(wt_argt1 s))
                        (fun x _ _ h1 -> (pre1 s) x h1)) ->
    c_post:(x:(argt1 s) -> r:(resexn (rett0 s)) -> 
        Lemma (forall h0 h1. (SpecErr10?.post s) x h0 r h1 ==> post_poly_arrow a3p #(resexn (rett0 s)) #(witnessable_resexn _ #(wt_rett0 s)) h0 r h1))
    -> hoc a3p s

| EnforcePost :
    #s:pck_spec{SpecErr00? s /\ bit s == false} ->
    c_pre:(x:(argt0 s) -> 
        Lemma (forall h0. (pre0 s) x h0 ==> pre_poly_arrow a3p #(argt0 s) #(wt_argt0 s) x h0)) ->
    c_post:(x:(argt0 s) -> e:err -> 
        Lemma (forall h0 h1. (pre0 s) x h0 /\ post_poly_arrow a3p #_ #(witnessable_resexn _ #(wt_rett0 s)) h0 (Inr e) h1 ==> (SpecErr00?.post s) x h0 (Inr e) h1)) ->
    check:(select_check a3p (argt0 s) (resexn (rett0 s)) #(witnessable_resexn _ #(wt_rett0 s)) (pre0 s) (SpecErr00?.post s))
    -> hoc a3p s

type pck_hoc a3p : Type =
  s:pck_spec & (hoc a3p s)

private
let myspec : pck_spec =
  SpecErr00
    true
    (ref int)
    (witnessable_ref int)
    (fun x h -> sel h x > 5)
    unit
    witnessable_unit
    (fun _ -> post_poly_arrow c3p)

private
let test_pre : hoc c3p myspec =
  EnforcePre00
    (fun (x:(argt0 myspec)) ->
      let x : ref int = x in
      let eh0 = get_heap () in
      let check : cb_check c3p (ref int) unit (pre_poly_arrow c3p #(argt0 myspec) #(wt_argt0 myspec)) (fun x _ _ h1 -> (pre0 myspec) x h1) x eh0 = (
        fun _ ->
          assert (witnessed (contains_pred x));
          recall (contains_pred x);
          if read x > 5 then Inl ()
          else Inr (Contract_failure "less than 5")
      ) in
      (| eh0, check |))
    (fun _ _ -> ())

private
let myspec' : pck_spec =
  SpecErr00
    false
    (ref int)
    (witnessable_ref int)
    (pre_poly_arrow c3p)
    unit
    witnessable_unit
    (fun x h0 r h1 -> (Inr? r \/ sel h1 x > 5) /\ post_poly_arrow c3p h0 r h1)

private
let test_post : hoc c3p myspec' =
  EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun x ->
      let x : ref int = x in
      let eh0 = get_heap () in
      let check : cb_check c3p (ref int) (resexn unit) #(witnessable_resexn _ #(wt_rett0 myspec')) (pre0 myspec') (SpecErr00?.post myspec') x eh0 = (
        fun _ ->
          assert (witnessed (contains_pred x));
          recall (contains_pred x);
          if read x > 5 then Inl ()
          else Inr (Contract_failure "less than 5")
      ) in
      (| eh0, check |))

type spec_tree : Type = tree pck_spec

let hoc_tree a3p (st:spec_tree) : Type =
  hocs:(tree (pck_hoc a3p)){equal_trees st (map_tree hocs dfst)}
