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
type spec : Type u#(max (1 + a) (1 + b)) =
| Spec :
    bit:bool -> (* true -> enforce pre, false -> enforce post *)
    err:bool ->
    argt:Type u#a ->
    wt_argt:witnessable argt -> (** asking for a witnessable type here helps the implementation of HoC to work only with this instance *)
    pre:(argt -> st_pre) ->
    rett:Type u#b ->
    wt_rett:witnessable rett ->
    (post:(x:argt -> h0:heap -> st_post' (if err then resexn rett else rett) (pre x h0))) ->
    spec

noeq
type uspec = 
| U00 : v:spec u#0 u#0 -> uspec 
| U01 : v:spec u#0 u#1 -> uspec
| U10 : v:spec u#1 u#0 -> uspec
| U11 : v:spec u#1 u#1 -> uspec

type pre_c_post a3p #a #b (c_b:witnessable b) (pre:a -> st_pre) (post:(x:a -> h0:heap -> st_post' b (pre x h0))) =
  x:a -> r:b -> Lemma (forall h0 h1. post x h0 r h1 ==> post_poly_arrow a3p #b #c_b h0 r h1)

type pre_check a3p a {| c:witnessable a |} (pre:a -> st_pre)=
  select_check a3p a unit (pre_poly_arrow a3p #a #c) (fun x _ _ h1 -> pre x h1)

noeq
type hoc a3p : (s:spec) -> Type =
| TrivialPre :
    #s:spec{s.err == false /\ s.bit == true} ->
    c_pre:(x:s.argt -> Lemma (forall h0. pre_poly_arrow a3p #s.argt #s.wt_argt x h0 ==> s.pre x h0)) -> 
    c_post:pre_c_post a3p s.wt_rett s.pre s.post
    -> hoc a3p s

| EnforcePre :
    #s:spec{s.err == true /\ s.bit == true} ->
    check:pre_check a3p s.argt #s.wt_argt s.pre ->
    c_post:pre_c_post a3p (witnessable_resexn _ #s.wt_rett) s.pre s.post
    -> hoc a3p s

| TrivialPost :
    #s:spec{s.err == false /\ s.bit == false} ->
    c_pre:(x:s.argt ->
        Lemma (forall h0. s.pre x h0 ==> pre_poly_arrow a3p #s.argt #s.wt_argt x h0)) ->
    c_post:(x:s.argt -> r:s.rett -> 
        Lemma (forall h0 h1. post_poly_arrow a3p #s.rett #s.wt_rett h0 r h1 ==> s.post x h0 r h1))
    -> hoc a3p s

| EnforcePost :
    #s:spec{s.err == true /\ s.bit == false} ->
    c_pre:(x:s.argt -> 
        Lemma (forall h0. s.pre x h0 ==> pre_poly_arrow a3p #s.argt #s.wt_argt x h0)) ->
    c_post:(x:s.argt -> e:err -> 
        Lemma (forall h0 h1. s.pre x h0 /\ post_poly_arrow a3p #_ #(witnessable_resexn _ #s.wt_rett) h0 (Inr e) h1 ==> s.post x h0 ((Inr e) <: resexn s.rett) h1)) ->
    check:(select_check a3p s.argt (resexn s.rett) #(witnessable_resexn _ #s.wt_rett) s.pre s.post)
    -> hoc a3p s

noeq
type uhoc a3p : (s:uspec) -> Type =
| U00hoc : #s:uspec{U00? s} -> hoc a3p (U00?.v s) -> uhoc a3p s
| U01hoc : #s:uspec{U01? s} -> hoc a3p (U01?.v s) -> uhoc a3p s
| U10hoc : #s:uspec{U10? s} -> hoc a3p (U10?.v s) -> uhoc a3p s
| U11hoc : #s:uspec{U11? s} -> hoc a3p (U11?.v s) -> uhoc a3p s

type pck_uhoc a3p : Type =
  s:uspec & (uhoc a3p s)

type spec_tree = tree uspec

let hoc_tree a3p (st:spec_tree) : Type =
  hocs:(tree (pck_uhoc a3p)){equal_trees st (map_tree hocs dfst)}
