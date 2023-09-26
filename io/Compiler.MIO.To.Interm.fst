module Compiler.MIO.To.Interm

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open Compiler.Languages
open TC.Checkable

(** **** Types **)
(** Dynamic check possibilities:
pre:
  trace -> bool
  'a -> trace -> bool

post:
  trace -> trace -> bool
  'a -> trace -> trace -> bool
  trace -> 'b -> trace -> bool
  'a -> trace -> 'b -> trace -> bool

All these dynamic checks can be encoded using:
  'a -> trace -> 'b -> trace -> bool
and do some hacks in the code.

One extra thing would be the dynamic checks to be also
used to do the refinements. Right now, a different checkable
typeclass is used for the refinements.
**)

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

(* From h', an extension of h, we can obtain the difference
(i.e. the local trace) just from the lengths. *)
let get_local_trace (h':trace) (h:trace) :
  Pure trace
    (requires (h' `suffix_of` h))
    (ensures (fun lt -> h == (apply_changes h' lt))) =
  suffix_of_length h' h;
  let n : nat = (List.length h) - (List.length h') in
  let (lt', ht) = List.Tot.Base.splitAt n h in
  lemma_splitAt_equal n h;
  lemma_splitAt_suffix h h';
  List.Tot.Properties.rev_involutive lt';
  assert (h == apply_changes h' (List.rev lt'));
  List.rev lt'

(* Dynamic check typ *)
type dc_typ (mst:mst) (#argt:Type u#a) (#rett:Type u#b) = argt -> mst.cst -> rett -> mst.cst -> bool

(* Postcondition for effectful dynamic check *)
unfold
let eff_dc_typ_cont_post (mst:mst) (dc:dc_typ mst) (s0:mst.cst) (x:'a) (y:'b) (h1:trace) ((s1,b):erased mst.cst * bool) (lt:trace) : Type0 =
  s1 `mst.models` h1 /\ (b <==> dc x s0 y s1) /\ lt == []

(* Effectful dynamic check for the result, given initial value and initial history *)
type eff_dc_typ_cont (mst:mst) (fl:erased tflag) (t1:Type u#a) (t2:Type u#b) (dc:dc_typ mst #t1 #t2) (x:t1) (s0:mst.cst) =
  y:t2 -> MIO (erased mst.cst * bool) mst fl (fun h1 -> True) (eff_dc_typ_cont_post mst dc s0 x y)
  
(* Effectful runtime check: given an x:t1 returns an erased trace and an
effectful function to check the result (t2) *)
type eff_dc_typ (mst:mst) (fl:erased tflag) (#t1 #t2:Type) (dc:dc_typ mst #t1 #t2) =
  x:t1 -> MIO (s0:erased mst.cst & eff_dc_typ_cont mst fl t1 t2 dc x s0)
             mst
             fl
             (fun _ -> True)
             (fun h0 (| s0, _ |) lt -> s0 `mst.models` h0 /\ lt == [])

(* Lifting a runtime check into an effectful check *)
val enforce_dc : (#mst:mst) -> (#argt:Type u#a) -> (#rett:Type u#b) -> 
  dc:dc_typ mst #argt #rett -> eff_dc_typ mst AllActions dc
#push-options "--compat_pre_core 1" // fixme
let enforce_dc #mst #argt #rett dc x =
  let s0 = get_state () in
  let cont : eff_dc_typ_cont mst AllActions argt rett dc x s0 =
    (fun y -> (
      let s1 = get_state () in
      (hide s1, dc x s0 y s1))) in
  (| hide s0,  cont |)
#pop-options

// todo: in HO cases, t1 or t2 should be unit since one can not write a
// runtime check that uses an MIO arrow. thus, one idea is to make the
// type of pck_dc here `pck_dc_typ (option t1) (option t2)`
type pck_dc mst = (argt:Type u#a & rett:Type u#b & dc_typ mst #argt #rett)

let arg_typ #mst (ctr:pck_dc mst) : Type = ctr._1
let ret_typ #mst (ctr:pck_dc mst) : Type = ctr._2

let check #mst (ctr:pck_dc mst) (arg:arg_typ ctr) (s0:mst.cst) (ret:ret_typ ctr) (s1:mst.cst) : bool =
  ctr._3 arg s0 ret s1


type eff_pck_dc mst (fl:erased tflag) = ctr:pck_dc mst & eff_dc_typ mst fl ctr._3

val make_dc_eff : mst:mst -> pck_dc u#a u#b mst -> eff_pck_dc u#a u#b mst AllActions
let make_dc_eff mst r = (| r, (enforce_dc #mst r._3) |)

type typ_eff_dcs mst (fl:erased tflag) (dcs:tree (pck_dc mst)) =
  eff_dcs:(tree (eff_pck_dc mst fl)){equal_trees dcs (map_tree eff_dcs dfst)}

(* Two helpers, to guide F* *)
let typ_left #mst (#fl:erased tflag) (#dcs:tree (pck_dc mst))
  ($t : typ_eff_dcs mst fl dcs{Node? t \/ EmptyNode? t})
  : typ_eff_dcs mst fl (left dcs)
  = left t

let typ_right #mst (#fl:erased tflag) (#dcs:tree (pck_dc mst))
  ($t : typ_eff_dcs mst fl dcs{Node? t \/ EmptyNode? t})
  : typ_eff_dcs mst fl (right dcs)
  = right t
  
let cong (#t1 #t2 : tree 'a) (f : 'a -> 'b) (_ : squash (t1 == t2)) : squash (map_tree t1 f == map_tree t2 f) = ()

let make_dcs_eff #mst (dcs:tree (pck_dc mst)) : typ_eff_dcs mst AllActions dcs =
  let r : tree (eff_pck_dc mst AllActions) = map_tree dcs (make_dc_eff mst) in
  let r_def : squash (r == map_tree dcs (make_dc_eff mst)) = () in
  let comp x = dfst (make_dc_eff mst x) in
  (* sigh, F* not being very helpful here *)
  calc (==) {
    map_tree r dfst;
    == { cong dfst r_def }
    map_tree (map_tree #(pck_dc mst) dcs (make_dc_eff mst)) dfst;
    == { map_fuse #_ #(eff_pck_dc mst AllActions) #_ dcs (make_dc_eff mst) dfst }
    map_tree dcs comp;
    == { map_ext dcs (fun x -> dfst (make_dc_eff mst x)) (fun x -> x) }
    map_tree dcs (fun x -> x);
    == { map_id dcs }
    dcs;
  };
  r

class exportable (styp : Type u#a) (fl:erased tflag) (pi:policy_spec) (mst:mst) (dcs:tree (pck_dc u#c u#d mst)) = {
  [@@@no_method]
  ityp : Type u#b;
  [@@@no_method]
  c_ityp : interm ityp fl pi mst;
  [@@@no_method]
  export : typ_eff_dcs mst fl dcs -> styp -> ityp;
}

class safe_importable (styp : Type u#a) (fl:erased tflag) (pi:policy_spec) (mst:mst) (dcs:tree (pck_dc u#c u#d mst)) = {
  [@@@no_method]
  ityp : Type u#b;
  [@@@no_method]
  c_ityp : interm ityp fl pi mst;
  [@@@no_method]
  safe_import : ityp -> typ_eff_dcs mst fl dcs -> styp; 
}

class importable (styp : Type u#a) (fl:erased tflag) (pi:policy_spec)  (mst:mst) (dcs:tree (pck_dc u#c u#d mst)) = {
  [@@@no_method]
  ityp : Type u#b; 
  [@@@no_method]
  c_ityp : interm ityp fl pi mst;
  [@@@no_method]
  import : ityp -> typ_eff_dcs mst fl dcs -> resexn styp;
}

instance interm_importable_super styp fl pi mst dcs (d : importable styp fl pi mst dcs) : interm d.ityp fl pi mst = d.c_ityp
instance interm_exportable_super styp fl pi mst dcs (d : exportable styp fl pi mst dcs) : interm d.ityp fl pi mst = d.c_ityp
instance interm_safe_importable_super styp fl pi mst dcs (d : safe_importable styp fl pi mst dcs) : interm d.ityp fl pi mst = d.c_ityp

(** *** Exportable instances **)

instance interm_is_exportable (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){Leaf? dcs}) t {| d1: interm t fl pi mst |} : exportable t fl pi mst dcs = {
  ityp = t;
  c_ityp = solve;
  export = (fun Leaf x -> x)
}

instance exportable_unit (#fl:erased tflag) (#pi:policy_spec) #mst : exportable unit fl pi mst Leaf = {
  ityp = unit;
  c_ityp = solve;
  export = (fun Leaf () -> ())
}

instance exportable_file_descr (#fl:erased tflag) (#pi:policy_spec) #mst : 
  exportable file_descr fl pi mst Leaf = {
  ityp = file_descr;
  c_ityp = solve;
  export = (fun Leaf fd -> fd)
}

instance exportable_bytes (#fl:erased tflag) (#pi:policy_spec) #mst :
  exportable Bytes.bytes fl pi mst Leaf = {
  ityp = Bytes.bytes;
  c_ityp = solve;
  export = (fun Leaf b -> b)
}

instance exportable_refinement (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:tree (pck_dc mst)) t {| d:exportable t fl pi mst dcs |} (p : t -> Type0) : exportable (x:t{p x}) fl pi mst dcs = {
  ityp = d.ityp;
  c_ityp = solve;
  export = d.export
}

instance exportable_option
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:tree (pck_dc mst))
  t1 {| d1:exportable t1 fl pi mst dcs |} :
  Tot (exportable (option t1) fl pi mst dcs) = {
  ityp = option d1.ityp;
  c_ityp = solve;
  export = (fun eff_dcs x -> match x with | Some x' -> Some (d1.export eff_dcs x') | None -> None)
}


instance exportable_pair
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 {| d1:exportable t1 fl pi mst (left dcs) |} t2 {| d2:exportable t2 fl pi mst (right dcs) |} :
  Tot (exportable (t1 * t2) fl pi mst dcs) = {
  ityp = d1.ityp * d2.ityp;
  c_ityp = solve;
  export = (fun eff_dcs (x, y) -> (d1.export (left eff_dcs) x, d2.export (right eff_dcs) y));
}

instance exportable_either
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 {| d1:exportable t1 fl pi mst (left dcs) |} t2 {| d2:exportable t2 fl pi mst (right dcs) |} :
  Tot (exportable (either t1 t2) fl pi mst dcs) = {
  ityp = either d1.ityp d2.ityp;
  c_ityp = solve;
  export = (fun eff_dcs x -> 
      match x with | Inl x -> Inl (d1.export (left eff_dcs) x) | Inr x -> Inr (d2.export (right eff_dcs) x))
}

(** *** Exportable arrows **)

#push-options "--compat_pre_core 1"
instance exportable_arrow_with_no_pre_and_no_post
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  (t1:Type) {| d1:importable t1 fl pi mst (left dcs) |}
  (t2:Type) {| d2:exportable t2 fl pi mst (right dcs) |} :
  exportable (t1 -> MIOpi (resexn t2) fl pi mst) fl pi mst dcs = {
    ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
    c_ityp = solve;
    export = (fun eff_dcs (f:(t1 -> MIOpi (resexn t2) fl pi mst)) (x:d1.ityp) ->
      match d1.import x (left eff_dcs) with
      | Inl x' -> begin
        match f x' with 
        | Inl x'' -> Inl (d2.export (right eff_dcs) x'') 
        | Inr err -> Inr err
      end
      | Inr err -> Inr err
    )
  }
#pop-options

(** This is a design choice for making proofs easier. One can remove the post-condition **)
instance exportable_arrow_post_args
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 {| d1:importable t1 fl pi mst (left dcs) |}
  t2 {| d2:exportable t2 fl pi mst (right dcs) |}
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c1 : squash (forall x h lt r. post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> MIO (resexn t2) mst fl (fun _ -> True) (post x)) fl pi mst dcs = {
    ityp = x:d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
    c_ityp = solve;
    export = (fun eff_dcs (f:(x:t1 -> MIO (resexn t2) mst fl (fun _ -> True) (post x))) ->
      let f' : t1 -> MIOpi (resexn t2) fl pi mst = f in
      (exportable_arrow_with_no_pre_and_no_post t1 #d1 t2 #d2).export eff_dcs f');
  }

instance exportable_arrow_post
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 {| d1:importable t1 fl pi mst (left dcs) |}
  t2 {| d2:exportable t2 fl pi mst (right dcs) |}
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c1 : squash (forall h lt r. post h r lt ==> enforced_locally pi h lt)) :
  exportable (t1 -> MIO (resexn t2) mst fl (fun _ -> True) post) fl pi mst dcs = 
  exportable_arrow_post_args t1 t2 (fun _ -> post)

let trivialize_new_post #a #b #mst (dc:dc_typ mst #a #unit) post :
  Tot (a -> trace -> resexn b -> trace -> Type0) =
    fun x h r lt -> exists s0. s0 `mst.models` h ==>
      (~(dc x s0 () s0) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (dc x s0 () s0 ==> post x h r lt) 

let enforce_pre
  #t1 #t2 #fl pi #mst
  (pre : trace -> Type0)
  (dc : dc_typ mst #unit #unit)
  (eff_dc : eff_dc_typ mst fl dc) 
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall s0 s1 h. s0 `mst.models` h /\ s1 `mst.models` h /\ dc () s0 () s1 ==> pre h))
  (#c_post : squash (forall h lt r. pre h /\ post h r lt ==> enforced_locally pi h lt))
  (f:(t1 -> MIO (resexn t2) mst fl pre post))
  (x:t1) :
  MIOpi (resexn t2) fl pi mst =
  let (| s0, eff_dc' |)  = eff_dc () in
  let (s1, b) = eff_dc' () in
  if b then f x
  else Inr Contract_failure
  
let enforce_pre_args
  #t1 #t2 #fl pi #mst
  (pre : t1 -> trace -> Type0)
  (dc : dc_typ mst #t1 #unit)
  (eff_dc : eff_dc_typ mst fl dc) 
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall x s0 s1 h. s0 `mst.models` h /\ s1 `mst.models` h /\ dc x s0 () s1 ==> pre x h))
  (#c_post : squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt))
  (f:(x:t1 -> MIO (resexn t2) mst fl (pre x) (post x)))
  (x:t1) :
  MIOpi (resexn t2) fl pi mst =
  let (| _, eff_dc' |) = eff_dc x in
  let (_, b) = eff_dc' () in
  if b then f x
  else Inr Contract_failure

val rityp_eff_dc : #mst:_ -> (#fl:erased tflag) -> (#a:Type u#a) -> (#b:Type u#b) -> (#c:Type{c == a}) -> (#d:Type{d == b}) -> (#dc:dc_typ mst #a #b) -> (t : eff_dc_typ mst fl dc) -> (eff_dc_typ mst fl #c #d dc)

#push-options "--compat_pre_core 1"
let rityp_eff_dc #mst #fl #a #b #c #d #dc eff_dc (x:c) = 
    let (| s0, cont |) = eff_dc x in
    let cont' : eff_dc_typ_cont mst fl c d  dc x s0 = (fun (y:d) -> cont y) in
    (| s0, cont' |)
#pop-options

instance exportable_arrow_pre_post_args
  (t1:Type) (t2:Type)
  (#fl:erased tflag)
  (#pi:policy_spec) 
  #mst
  (#dcs:(tree (pck_dc mst)){Node? dcs /\ arg_typ (root dcs) == t1 /\ (ret_typ (root dcs) == unit)})
  {| d1:importable t1 fl pi mst (left dcs) |}
  {| d2:exportable t2 fl pi mst (right dcs) |}
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall x s0 s1 h. s0 `mst.models` h /\ s1 `mst.models` h /\ check (root dcs) x s0 () s1 ==> pre x h))
  (#c_post : squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> MIO (resexn t2) mst fl (pre x) (post x)) fl pi mst dcs = {
    ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst; 
    c_ityp = solve;
    export = (fun eff_dcs (f:(x:t1 -> MIO (resexn t2) mst fl (pre x) (post x))) ->
      let (| (| a, b, dc |), eff_dc |) = root eff_dcs in
      let eff_dc : eff_dc_typ mst fl #t1 #unit dc = rityp_eff_dc eff_dc in
      let new_post = (fun _ h _ lt -> enforced_locally pi h lt) in
      let dcs' = (EmptyNode (left dcs) (right dcs)) in
      let d = (exportable_arrow_post_args #fl #pi #mst #dcs' t1 #d1 t2 #d2 new_post) in
      let eff_dcs' = (EmptyNode (left eff_dcs) (right eff_dcs)) in
      assert (forall x s0 s1. check (root dcs) x s0 () s1 == dc x s0 () s1);
      let f' = enforce_pre_args pi pre dc eff_dc post f in
      d.export eff_dcs' f'
    )
}

instance exportable_arrow_pre_post
  (t1:Type) (t2:Type) #fl #pi #mst
  (#dcs:(tree (pck_dc mst)){Node? dcs /\ arg_typ (root dcs) == unit /\ (ret_typ (root dcs) == unit)})
  {| d1:importable t1 fl pi mst (left dcs) |}
  {| d2:exportable t2 fl pi mst (right dcs) |}
  (pre : trace -> Type0)
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall s0 s1 h. s0 `mst.models` h /\ s1 `mst.models` h /\ check (root dcs) () s0 () s1 ==> pre h))
  (#c_post : squash (forall h lt r. pre h /\ post h r lt ==> enforced_locally pi h lt)) :
  exportable (t1 -> MIO (resexn t2) mst fl pre post) fl pi mst dcs = {
    ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst; 
    c_ityp = solve;
    export = (fun eff_dcs (f:(t1 -> MIO (resexn t2) mst fl pre post)) ->
      let (| (| a, b, dc |), eff_dc |) = root eff_dcs in
      let eff_dc : eff_dc_typ mst fl #unit #unit dc = rityp_eff_dc eff_dc in
      let new_post = (fun _ h _ lt -> enforced_locally pi h lt) in
      let dcs' = (EmptyNode (left dcs) (right dcs)) in
      let d = (exportable_arrow_post_args #fl #pi #mst #dcs' t1 #d1 t2 #d2 new_post) in
      let eff_dcs' = (EmptyNode (left eff_dcs) (right eff_dcs)) in
      assert (forall x s0 s1. check (root dcs) x s0 () s1 == dc x s0 () s1);
      let f' = enforce_pre pi pre dc eff_dc post f in
      d.export eff_dcs' f'
    )
}

    
(** *** Safe importable instances **)
let interm_is_safely_importable (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){Leaf? dcs}) #t (d:interm t fl pi mst) : safe_importable t fl pi mst dcs = {
  ityp = t;
  c_ityp = solve;
  safe_import = (fun x Leaf -> x); 
}

instance importable_unit (#fl:erased tflag) (#pi:policy_spec) #mst : importable unit fl pi mst Leaf = {
  ityp = unit;
  c_ityp = solve;
  import = (fun () Leaf -> Inl ())
}

instance importable_file_descr (#fl:erased tflag) (#pi:policy_spec) #mst : importable file_descr fl pi mst Leaf = {
  ityp = file_descr;
  c_ityp = solve;
  import = (fun fd Leaf -> Inl fd)
}

instance importable_bytes (#fl:erased tflag) (#pi:policy_spec) #mst : importable Bytes.bytes fl pi mst Leaf = {
  ityp = Bytes.bytes;
  c_ityp = solve;
  import = (fun b Leaf -> Inl b)
}

(** *** Importable instances **)

instance safe_importable_is_importable (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:tree (pck_dc mst)) #t (d:safe_importable t fl pi mst dcs) : importable t fl pi mst dcs = {
  ityp = d.ityp;
  c_ityp = solve;
  import = (fun x eff_dcs -> Inl (d.safe_import x eff_dcs))
}

instance importable_refinement
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:tree (pck_dc mst))
  t {| d:importable t fl pi mst dcs |}
  (rp : t -> Type0) {| d1:checkable rp |} :
  Tot (importable (x:t{rp x}) fl pi mst dcs) = {
  ityp = d.ityp;
  c_ityp = solve;
  import = (fun (x:d.ityp) eff_dcs ->
    (match d.import x eff_dcs with
    | Inl x ->
      if d1.check x then Inl x 
      else Inr Contract_failure
    | Inr err -> Inr err) <: resexn (x:t{rp x}))
}
    
instance importable_option
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:tree (pck_dc mst))
  t {| d:importable t fl pi mst dcs |} :
  Tot (importable (option t) fl pi mst dcs) = {
  ityp = option d.ityp;
  c_ityp = solve;
  import = (fun (x:option d.ityp) eff_dcs ->
    match x with
    | Some x' -> begin
      match d.import x' eff_dcs with
      | Inl x'' -> Inl (Some x'')
      | Inr err -> Inr err
    end
    | None -> Inr Contract_failure)
}

instance importable_pair
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 t2 {| d1:importable t1 fl pi mst (left dcs) |} {| d2:importable t2 fl pi mst (right dcs) |} :
  Tot (importable (t1 * t2) fl pi mst dcs) = {
  ityp = d1.ityp * d2.ityp;
  c_ityp = solve;
  import = (fun (x,y) eff_dcs ->
      match (d1.import x (left eff_dcs), d2.import y (right eff_dcs)) with
      | (Inl x, Inl y) -> Inl (x, y)
      | _ -> Inr Contract_failure)
}

instance importable_either
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 t2 {| d1:importable t1 fl pi mst (left dcs) |} {| d2:importable t2 fl pi mst (right dcs) |} :
  Tot (importable (either t1 t2) fl pi mst dcs) = {
  ityp = either d1.ityp d2.ityp;
  c_ityp = solve;
  import = (fun x eff_dcs ->
      match x with
      | Inl x' -> begin
        match d1.import x' (left eff_dcs) with
        | Inl x'' -> Inl (Inl x'')
        | Inr err -> Inr err
      end
      | Inr y -> begin
        match d2.import y (right eff_dcs) with
        | Inl y' -> Inl (Inr y')
        | Inr err -> Inr err
      end)
}

instance importable_dpair_refined
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 fl pi mst (left dcs) |} {| d2:importable t2 fl pi mst (right dcs) |}
  {| d3:checkable2 p |} :
  Tot (importable (x:t1 & y:t2{p x y}) fl pi mst dcs) = {
  ityp = d1.ityp & d2.ityp;
  c_ityp = solve;
  import = (fun ((x', y')) eff_dcs ->
      match (d1.import x' (left eff_dcs), d2.import y' (right eff_dcs)) with
       | (Inl x, Inl y) ->
            if check2 #t1 #t2 #p x y then Inl ((| x, y |) <: (x:t1 & y:t2{p x y})) else Inr Contract_failure
       | _ -> Inr Contract_failure)
}

(** *** Safe importable arrows **)
instance safe_importable_resexn
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:tree (pck_dc mst))
  t1 {| d1:importable t1 fl pi mst dcs |} :
  Tot (safe_importable (resexn t1) fl pi mst dcs) = {
  ityp = resexn d1.ityp;
  c_ityp = solve;
  safe_import = (fun x eff_dcs ->
      match x with
      | Inl x' -> d1.import x' eff_dcs 
      | Inr y -> Inr y)
}
    
#push-options "--compat_pre_core 1"
instance safe_importable_arrow
  (#fl:erased tflag) (#pi:policy_spec) #mst (#dcs:(tree (pck_dc mst)){EmptyNode? dcs})
  (t1:Type) {| d1:exportable t1 fl pi mst (left dcs) |}
  (t2:Type) {| d2:importable t2 fl pi mst (right dcs) |} : 
  safe_importable ((x:t1) -> MIOpi (resexn t2) fl pi mst) fl pi mst dcs = {
  ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
  c_ityp = solve;
  safe_import = (fun (f:d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst) eff_dcs (x:t1) -> 
    (let x' = d1.export (left eff_dcs) x in 
     let y : resexn d2.ityp = f x' in
     (safe_importable_resexn t2 #d2).safe_import y (right eff_dcs)) <: MIOpi (resexn t2) fl pi mst)
}
#pop-options

(** The following four should be unified but I had universe problems **)
let enforce_post_args_res
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:policy_spec)
  #mst
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (dc : dc_typ mst #t1 #(resexn t2))
  (eff_dc : eff_dc_typ mst fl dc) 
  (c1_post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2_post : squash (forall s0 s1 x h r lt . s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ dc x s0 r s1 ==> post x h r lt))
  (f:t1 -> MIOpi (resexn t2) fl pi mst)
  (x:t1) :
  MIO (resexn t2) mst fl (pre x) (post x) =
  let (| _, eff_dc' |) = eff_dc x in
  let r : resexn t2 = f x in
  let (_, b) = eff_dc' r in
  if b then r
  else Inr Contract_failure

let enforce_post_args
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:policy_spec)
  #mst
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (dc : dc_typ mst #t1 #unit)
  (eff_dc : eff_dc_typ mst fl dc) 
  (c1_post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2_post : squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ (dc x s0 () s1) ==> post x h r lt))
  (f:t1 -> MIOpi (resexn t2) fl pi mst)
  (x:t1) :
  MIO (resexn t2) mst fl (pre x) (post x) =
  let (| _, eff_dc' |) = eff_dc x in
  let r : resexn t2 = f x in
  let (_, b) = eff_dc' () in
  if b then r
  else Inr Contract_failure
  
let enforce_post_res
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:policy_spec)
  #mst
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (dc : dc_typ mst #unit #(resexn t2))
  (eff_dc : eff_dc_typ mst fl dc) 
  (c1_post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2_post : squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ (dc () s0 r s1) ==> post x h r lt))
  (f:t1 -> MIOpi (resexn t2) fl pi mst)
  (x:t1) :
  MIO (resexn t2) mst fl (pre x) (post x) =
  let (| _, eff_dc' |) = eff_dc () in
  let r : resexn t2 = f x in
  let (_, b) = eff_dc' r in
  if b then r
  else Inr Contract_failure

let enforce_post
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:policy_spec)
  #mst
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (dc : dc_typ mst #unit #unit)
  (eff_dc : eff_dc_typ mst fl dc) 
  (c1_post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2_post : squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ (dc () s0 () s1) ==> post x h r lt))
  (f:t1 -> MIOpi (resexn t2) fl pi mst)
  (x:t1) :
  MIO (resexn t2) mst fl (pre x) (post x) =
  let (| _, eff_dc' |) = eff_dc () in
  let r : resexn t2 = f x in
  let (_, b) = eff_dc' () in
  if b then r
  else Inr Contract_failure

instance safe_importable_arrow_pre_post_args_res
  (#t1:Type) (#t2:Type)
  (#fl:erased tflag)
  (#pi:policy_spec) 
  #mst
  (#dcs:(tree (pck_dc mst)){Node? dcs /\ (arg_typ (root dcs) == t1 /\ (ret_typ (root dcs) == (resexn t2))) })
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post: squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ check (root dcs) x s0 r s1 ==> post x h r lt)) 
  {| d1:exportable t1 fl pi mst (left dcs) |}
  {| d2:importable t2 fl pi mst (right dcs) |}:
  safe_importable (x:t1 -> MIO (resexn t2) mst fl (pre x) (post x)) fl pi mst dcs = {
   ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
  c_ityp = solve;
  safe_import = (fun (f:(d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst)) eff_dcs ->
    let dcs' = (EmptyNode (left dcs) (right dcs)) in
    let eff_dcs' = (EmptyNode (left eff_dcs) (right eff_dcs)) in
    let f' = (safe_importable_arrow #fl #pi #mst #dcs' t1 #d1 t2 #d2).safe_import f eff_dcs' in
    let (| dc_pck, eff_dc |) = root eff_dcs in
    assert (forall x r s0 s1. check (root dcs) x s0 r s1 == dc_pck._3 x s0 r s1);
    enforce_post_args_res pi pre post dc_pck._3 (rityp_eff_dc eff_dc) c1post c2post f')
  }

instance safe_importable_arrow_pre_post_res
  (#t1:Type) (#t2:Type)
  (#fl:erased tflag)
  (#pi:policy_spec) 
  #mst
  (#dcs:(tree (pck_dc mst)){Node? dcs /\ (arg_typ (root dcs) == unit /\ (ret_typ (root dcs) == (resexn t2))) })
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post : squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ ((check (root dcs)) () s0 r s1) ==> post x h r lt)) 
  {| d1:exportable t1 fl pi mst (left dcs) |}
  {| d2:importable t2 fl pi mst (right dcs) |}:
  safe_importable (x:t1 -> MIO (resexn t2) mst fl (pre x) (post x)) fl pi mst dcs = {
   ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
  c_ityp = solve;
  safe_import = (fun (f:(d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst)) eff_dcs ->
    let dcs' = (EmptyNode (left dcs) (right dcs)) in
    let eff_dcs' = (EmptyNode (left eff_dcs) (right eff_dcs)) in
    let f' = (safe_importable_arrow #fl #pi #mst #dcs' t1 #d1 t2 #d2).safe_import f eff_dcs' in
    let (| dc_pck, eff_dc |) = root eff_dcs in
    assert (forall x r s0 s1. check (root dcs) x s0 r s1 == dc_pck._3 x s0 r s1);
    enforce_post_res pi pre post dc_pck._3 (rityp_eff_dc eff_dc) c1post c2post f')
  }

instance safe_importable_arrow_pre_post_args
  (#t1:Type) (#t2:Type)
  (#fl:erased tflag)
  (#pi:policy_spec) 
  #mst
  (#dcs:(tree (pck_dc mst)){Node? dcs /\ (arg_typ (root dcs) == t1 /\ (ret_typ (root dcs) == unit)) })
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post : squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ ((check (root dcs)) x s0 () s1) ==> post x h r lt))
  {| d1:exportable t1 fl pi mst (left dcs) |}
  {| d2:importable t2 fl pi mst (right dcs) |} :
  safe_importable (x:t1 -> MIO (resexn t2) mst fl (pre x) (post x)) fl pi mst dcs = {
    ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
    c_ityp = solve;
    safe_import = (fun (f:(d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst)) eff_dcs ->
      let dcs' = (EmptyNode (left dcs) (right dcs)) in
      let eff_dcs' = (EmptyNode (left eff_dcs) (right eff_dcs)) in
      let f' = (safe_importable_arrow #fl #pi #mst #dcs' t1 #d1 t2 #d2).safe_import f eff_dcs' in
      let (| dc_pck, eff_dc |) = root eff_dcs in
      assert (forall x r s0 s1. check (root dcs) x s0 r s1 == dc_pck._3 x s0 r s1);
      enforce_post_args pi pre post dc_pck._3 (rityp_eff_dc eff_dc) c1post c2post f')
  }

instance safe_importable_arrow_pre_post
  (#t1:Type) (#t2:Type)
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)

  (#fl:erased tflag)
  (#pi:policy_spec) 
  #mst
  (#dcs:(tree (pck_dc mst)){Node? dcs /\ (arg_typ (root dcs) == unit /\ (ret_typ (root dcs) == unit)) })

  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post : squash (forall x h r lt s0 s1. s0 `mst.models` h /\ s1 `mst.models` (apply_changes h lt) /\ pre x h /\ enforced_locally pi h lt /\ check (root dcs) () s0 () s1 ==> post x h r lt)) 

  {| d1:exportable t1 fl pi mst (left dcs) |}
  {| d2:importable t2 fl pi mst (right dcs) |} :
  safe_importable (x:t1 -> MIO (resexn t2) mst fl (pre x) (post x)) fl pi mst dcs = {
    ityp = d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst;
    c_ityp = solve;
    safe_import = (fun (f:(d1.ityp -> MIOpi (resexn d2.ityp) fl pi mst)) eff_dcs ->
      let dcs' = (EmptyNode (left dcs) (right dcs)) in
      let eff_dcs' = (EmptyNode (left eff_dcs) (right eff_dcs)) in
      let f' = (safe_importable_arrow #fl #pi #mst #dcs' t1 #d1 t2 #d2).safe_import f eff_dcs' in
      let (| dc_pck, eff_dc |) = root eff_dcs in
      assert (forall x r s0 s1. check (root dcs) x s0 r s1 == dc_pck._3 x s0 r s1);
      enforce_post pi pre post dc_pck._3 (rityp_eff_dc eff_dc) c1post c2post f')
  }
