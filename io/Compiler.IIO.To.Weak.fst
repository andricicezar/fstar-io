module Compiler.IIO.To.Weak

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

let rec map_tree (t:tree 'a) (f:'a -> 'b) : tree 'b =
  match t with
  | Leaf -> Leaf
  | EmptyNode lhs rhs -> EmptyNode (map_tree lhs f) (map_tree rhs f)
  | Node x lhs rhs -> Node (f x) (map_tree lhs f) (map_tree rhs f)
  
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

type rc_typ (argt:Type u#a) (rett:Type u#b) = argt -> trace -> rett -> trace -> bool

let eff_rc_typ_cont_post (rc:rc_typ 'a 'b) (initial_h:erased trace) (x:'a) (y:'b) (current_h:trace) (b:bool) (lt:trace) : Type0 =
  (initial_h `suffix_of` current_h) /\
  (let the_lt = get_local_trace initial_h current_h in
  apply_changes initial_h the_lt == current_h /\ lt == [] /\ (b <==> rc x initial_h y the_lt))

type eff_rc_typ_cont (fl:erased tflag) (t1:Type u#a) (t2:Type u#b) (rc:rc_typ t1 t2) (x:t1) (initial_h:erased trace) =
  y:t2 -> IIO bool fl (fun h -> (initial_h `suffix_of` h)) (eff_rc_typ_cont_post rc initial_h x y)
  
type eff_rc_typ (fl:erased tflag) (#t1 #t2:Type) (rc:rc_typ t1 t2) =
  x:t1 -> IIO (initial_h:(erased trace) & eff_rc_typ_cont fl t1 t2 rc x initial_h) fl (fun _ -> True) (fun h (| initial_h, _ |) lt -> h == reveal initial_h /\ lt == [])

val enforce_rc : (#argt:Type u#a) -> (#rett:Type u#b) -> rc:rc_typ argt rett -> eff_rc_typ AllActions rc
let enforce_rc #argt #rett rc x =
  let initial_h = get_trace true in
  let cont : eff_rc_typ_cont AllActions argt rett rc x (hide initial_h) =
    (fun y -> (
      let current_h = get_trace true in
      let lt = get_local_trace initial_h current_h in
      rc x initial_h y lt)) in
  (| hide initial_h, cont |)

// todo: in HO cases, t1 or t2 should be unit since one can not write a
// runtime check that uses an IIO arrow. thus, one idea is to make the
// type of pck_rc here `pck_rc_typ (option t1) (option t2)`
type pck_rc = (argt:Type u#a & rett:Type u#b & rc_typ argt rett)

let arg_typ (ctr:pck_rc) : Type = Mkdtuple3?._1 ctr
let ret_typ (ctr:pck_rc) : Type = Mkdtuple3?._2 ctr

let check (ctr:pck_rc) (arg:arg_typ ctr) (h:trace) (ret:ret_typ ctr) (lt:trace) : bool =
  Mkdtuple3?._3 ctr arg h ret lt

type eff_pck_rc (fl:erased tflag) = ctr:pck_rc & eff_rc_typ fl (Mkdtuple3?._3 ctr)

val make_rc_eff : pck_rc u#a u#b -> eff_pck_rc u#a u#b AllActions
let make_rc_eff r = (| r, (enforce_rc (Mkdtuple3?._3 r)) |)

type typ_eff_rcs (fl:erased tflag) (rcs:tree pck_rc) =
  eff_rcs:(tree (eff_pck_rc fl)){
    equal_trees rcs (map_tree eff_rcs dfst)}

let make_rcs_eff (rcs:tree pck_rc) : typ_eff_rcs AllActions rcs =
  let r : tree (eff_pck_rc AllActions) = map_tree rcs make_rc_eff in
  assume (equal_trees rcs (map_tree r dfst));
  r

class exportable (styp : Type u#a) (pi:access_policy) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  wtyp : Type u#b;
  [@@@no_method]
  c_wtyp : weak wtyp fl pi;
  [@@@no_method]
  export : typ_eff_rcs fl rcs -> styp -> wtyp;
}

class safe_importable (styp : Type u#a) (pi:access_policy) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  swtyp : Type u#b;
  [@@@no_method]
  c_swtyp : weak swtyp fl pi;
  [@@@no_method]
  safe_import : swtyp -> typ_eff_rcs fl rcs -> styp; 
}

class importable (styp : Type u#a) (pi:access_policy) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  wtyp : Type u#b; 
  [@@@no_method]
  c_wtyp : weak wtyp fl pi;
  [@@@no_method]
  import : wtyp -> typ_eff_rcs fl rcs -> resexn styp;
}

(** *** Exportable instances **)

instance weak_is_exportable (#pi:access_policy) (#rcs:(tree pck_rc){Leaf? rcs}) (#fl:erased tflag) t {| d1: weak t fl pi |} : exportable t pi rcs fl = {
  wtyp = t;
  c_wtyp = d1;
  export = (fun Leaf x -> x)
}

instance exportable_unit (#pi:access_policy) (#fl:erased tflag) : exportable unit pi Leaf fl = {
  wtyp = unit;
  c_wtyp = weak_unit fl pi;
  export = (fun Leaf () -> ())
}

instance exportable_file_descr (#pi:access_policy) (#fl:erased tflag) : exportable file_descr pi Leaf fl = {
  wtyp = file_descr;
  c_wtyp = weak_file_descr fl pi;
  export = (fun Leaf fd -> fd)
}

instance exportable_bytes (#pi:access_policy) (#fl:erased tflag) : exportable Bytes.bytes pi Leaf fl = {
  wtyp = Bytes.bytes;
  c_wtyp = weak_bytes fl pi;
  export = (fun Leaf b -> b)
}

instance exportable_refinement (#pi:access_policy) (#rcs:tree pck_rc) (#fl:erased tflag) t {| d:exportable t pi rcs fl |} (p : t -> Type0) : exportable (x:t{p x}) pi rcs fl = {
  wtyp = d.wtyp;
  c_wtyp = d.c_wtyp;
  export = d.export
}

instance exportable_option
  (#pi:access_policy) (#rcs:tree pck_rc) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi rcs fl |} :
  Tot (exportable (option t1) pi rcs fl) = {
  wtyp = option d1.wtyp;
  c_wtyp = weak_option fl pi d1.wtyp #d1.c_wtyp;
  export = (fun eff_rcs x -> match x with | Some x' -> Some (d1.export eff_rcs x') | None -> None)
}


instance exportable_pair
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi (left rcs) fl |} t2 {| d2:exportable t2 pi (right rcs) fl |} :
  Tot (exportable (t1 * t2) pi rcs fl) = {
  wtyp = d1.wtyp * d2.wtyp;
  c_wtyp = weak_pair fl pi d1.wtyp #d1.c_wtyp d2.wtyp #d2.c_wtyp;
  export = (fun eff_rcs (x, y) -> (d1.export (left eff_rcs) x, d2.export (right eff_rcs) y));
}

instance exportable_either
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi (left rcs) fl |} t2 {| d2:exportable t2 pi (right rcs) fl |} :
  Tot (exportable (either t1 t2) pi rcs fl) = {
  wtyp = either d1.wtyp d2.wtyp;
  c_wtyp = weak_either fl pi d1.wtyp #d1.c_wtyp d2.wtyp #d2.c_wtyp;
  export = (fun eff_rcs x -> 
      match x with | Inl x -> Inl (d1.export (left eff_rcs) x) | Inr x -> Inr (d2.export (right eff_rcs) x))
}

(** *** Exportable arrows **)

instance exportable_arrow_with_no_pre_and_no_post
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  (t1:Type) {| d1:importable t1 pi (left rcs) fl |}
  (t2:Type) {| d2:exportable t2 pi (right rcs) fl|} :
  exportable (t1 -> IIOpi (resexn t2) fl pi) pi rcs fl = {
    wtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
    c_wtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
    export = (fun eff_rcs (f:(t1 -> IIOpi (resexn t2) fl pi)) (x:d1.wtyp) ->
      match d1.import x (left eff_rcs) with
      | Inl x' -> begin
        match f x' with 
        | Inl x'' -> Inl (d2.export (right eff_rcs) x'') 
        | Inr err -> Inr err
      end
      | Inr err -> Inr err
    )
  }

(** This is a design choice for making proofs easier. One can remove the post-condition **)
instance exportable_arrow_post_args
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:importable t1 pi (left rcs) fl |}
  t2 {| d2:exportable t2 pi (right rcs) fl |}
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c1 : squash (forall x h lt r. post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> IIO (resexn t2) fl (fun _ -> True) (post x)) pi rcs fl = {
    wtyp = x:d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
    c_wtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
    export = (fun eff_rcs (f:(x:t1 -> IIO (resexn t2) fl (fun _ -> True) (post x))) ->
      let f' : t1 -> IIOpi (resexn t2) fl pi = f in
      (exportable_arrow_with_no_pre_and_no_post t1 #d1 t2 #d2).export eff_rcs f');
  }

instance exportable_arrow_post
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:importable t1 pi (left rcs) fl |}
  t2 {| d2:exportable t2 pi (right rcs) fl |}
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c1 : squash (forall h lt r. post h r lt ==> enforced_locally pi h lt)) :
  exportable (t1 -> IIO (resexn t2) fl (fun _ -> True) post) pi rcs fl = 
  exportable_arrow_post_args t1 t2 (fun _ -> post)

let trivialize_new_post #a #b (pre: a -> trace -> bool) post :
  Tot (a -> trace -> resexn b -> trace -> Type0) =
    fun x h r lt -> 
      (~(pre x h) ==> r == (Inr Contract_failure) /\ lt == []) /\
      (pre x h ==> post x h r lt) 

let enforce_pre
  #t1 #t2
  (#fl:erased tflag)
  (pre : trace -> Type0)
  (rc : rc_typ unit unit)
  (eff_rc : eff_rc_typ fl rc) 
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall h. rc () h () [] ==> pre h))
  (f:(t1 -> IIO (resexn t2) fl pre post))
  (x:t1) :
  IIO (resexn t2) fl (fun _ -> True) (trivialize_new_post (fun x h -> rc () h () []) (fun _ -> post) ()) =
  let (| h, eff_rc' |) : (initial_h:(erased trace) & eff_rc_typ_cont fl unit unit rc () initial_h) = eff_rc () in
  if eff_rc' () then f x 
  else Inr Contract_failure

let enforce_pre_args
  #t1 #t2
  (#fl:erased tflag)
  (pre : t1 -> trace -> Type0)
  (rc : rc_typ t1 unit)
  (eff_rc : eff_rc_typ fl rc) 
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall h x. rc x h () [] ==> pre x h))
  (f:(x:t1 -> IIO (resexn t2) fl (pre x) (post x)))
  (x:t1) :
  IIO (resexn t2) fl (fun _ -> True) (trivialize_new_post (fun x h -> rc x h () []) post x) =
  let (| h, eff_rc' |) : (initial_h:(erased trace) & eff_rc_typ_cont fl t1 unit rc x initial_h) = eff_rc x in
  if eff_rc' () then f x 
  else Inr Contract_failure

let rwtyp_rc (#a #b #c #d:Type) (rc:rc_typ a b) : Pure (rc_typ c d) (requires (a == c /\ b == d)) (ensures (fun _ -> True)) = rc

val rwtyp_eff_rc : (#fl:erased tflag) -> (#a:Type u#a) -> (#b:Type u#b) -> (#c:Type{c == a}) -> (#d:Type{d == b}) -> (#rc:rc_typ a b) -> (t : eff_rc_typ fl rc) -> (eff_rc_typ fl #c #d (rwtyp_rc rc))
let rwtyp_eff_rc #fl #a #b #c #d #rc eff_rc (x:c) = 
    let (| initial_h, cont |) = eff_rc x in
    let cont' : eff_rc_typ_cont fl c d (rwtyp_rc rc) x initial_h = (fun (y:d) -> cont y) in
    (| initial_h, cont' |)

instance exportable_arrow_pre_post_args
  (t1:Type) (t2:Type)
  (#pi:access_policy) 
  (#rcs:(tree pck_rc){Node? rcs /\ arg_typ (root rcs) == t1 /\ (ret_typ (root rcs) == unit)})
  (#fl:erased tflag)
  {| d1:importable t1 pi (left rcs) fl |}
  {| d2:exportable t2 pi (right rcs) fl |}
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall h x. check (root rcs) x h () [] ==> pre x h))
  (#c1 : squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
    wtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi; 
    c_wtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
    export = (fun eff_rcs (f:(x:t1 -> IIO (resexn t2) fl (pre x) (post x))) ->
      let (| (| a, b, rc |), eff_rc |) = root eff_rcs in
      let eff_rc : eff_rc_typ fl #t1 #unit rc = rwtyp_eff_rc eff_rc in
      let f' = enforce_pre_args pre rc eff_rc post f in
      let rc_pre = (fun x h -> rc x h () []) in
      let new_post = trivialize_new_post rc_pre post in
      let rcs' = (EmptyNode (left rcs) (right rcs)) in
      let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
      let d = (exportable_arrow_post_args #pi #rcs' t1 #d1 t2 #d2 new_post) in
      d.export eff_rcs' f'
    )
}

instance exportable_arrow_pre_post
  (t1:Type) (t2:Type)
  (#pi:access_policy) 
  (#rcs:(tree pck_rc){Node? rcs /\ arg_typ (root rcs) == unit /\ (ret_typ (root rcs) == unit)})
  (#fl:erased tflag)
  {| d1:importable t1 pi (left rcs) fl |}
  {| d2:exportable t2 pi (right rcs) fl |}
  (pre : trace -> Type0)
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall h. (check (root rcs)) () h () [] ==> pre h))
  (#c1 : squash (forall h lt r. pre h /\ post h r lt ==> enforced_locally pi h lt)) :
  exportable (t1 -> IIO (resexn t2) fl pre post) pi rcs fl = {
    wtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi; 
    c_wtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
    export = (fun eff_rcs (f:(t1 -> IIO (resexn t2) fl pre post)) ->
      let (| (| a, b, rc |), eff_rc |) = root eff_rcs in
      let eff_rc : eff_rc_typ fl #unit #unit rc = rwtyp_eff_rc eff_rc in
      let f' = enforce_pre pre rc eff_rc post f in
      let rc_pre = (fun x h -> rc () h () []) in
      let new_post = trivialize_new_post rc_pre (fun _ -> post) in
      let rcs' = (EmptyNode (left rcs) (right rcs)) in
      let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
      let d = (exportable_arrow_post_args #_ #rcs' t1 #d1 t2 #d2 new_post) in
      d.export eff_rcs' f'
    )
}

    
(** *** Safe importable instances **)
let weak_is_safely_importable (#pi:access_policy) (#rcs:(tree pck_rc){Leaf? rcs}) (#fl:erased tflag) #t (d:weak t fl pi) : safe_importable t pi rcs fl = {
  swtyp = t;
  c_swtyp = d;
  safe_import = (fun x Leaf -> x); 
}

instance importable_unit (#pi:access_policy) (#fl:erased tflag) : importable unit pi Leaf fl = {
  wtyp = unit;
  c_wtyp = weak_unit fl pi;
  import = (fun () Leaf -> Inl ())
}

instance importable_file_descr (#pi:access_policy) (#fl:erased tflag) : importable file_descr pi Leaf fl = {
  wtyp = file_descr;
  c_wtyp = weak_file_descr fl pi;
  import = (fun fd Leaf -> Inl fd)
}

instance importable_bytes (#pi:access_policy) (#fl:erased tflag) : importable Bytes.bytes pi Leaf fl = {
  wtyp = Bytes.bytes;
  c_wtyp = weak_bytes fl pi;
  import = (fun b Leaf -> Inl b)
}

(** *** Importable instances **)

instance safe_importable_is_importable (#pi:access_policy) (#rcs:tree pck_rc) (#fl:erased tflag) #t (d:safe_importable t pi rcs fl) : importable t pi rcs fl = {
  wtyp = d.swtyp;
  c_wtyp = d.c_swtyp;
  import = (fun x eff_rcs -> Inl (d.safe_import x eff_rcs))
}

instance importable_refinement
  (#pi:access_policy) (#rcs:tree pck_rc) (#fl:erased tflag)
  t {| d:importable t pi rcs fl |}
  (rp : t -> Type0) {| d1:checkable rp |} :
  Tot (importable (x:t{rp x}) pi rcs fl) = {
  wtyp = d.wtyp;
  c_wtyp = d.c_wtyp;
  import = (fun (x:d.wtyp) eff_rcs ->
    (match d.import x eff_rcs with
    | Inl x ->
      if d1.check x then Inl x 
      else Inr Contract_failure
    | Inr err -> Inr err) <: resexn (x:t{rp x}))
}
    
instance importable_option
  (#pi:access_policy) (#rcs:tree pck_rc) (#fl:erased tflag)
  t {| d:importable t pi rcs fl |} :
  Tot (importable (option t) pi rcs fl) = {
  wtyp = option d.wtyp;
  c_wtyp = weak_option fl pi d.wtyp #d.c_wtyp;
  import = (fun (x:option d.wtyp) eff_rcs ->
    match x with
    | Some x' -> begin
      match d.import x' eff_rcs with
      | Inl x'' -> Inl (Some x'')
      | Inr err -> Inr err
    end
    | None -> Inr Contract_failure)
}

instance importable_pair
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 {| d1:importable t1 pi (left rcs) fl |} {| d2:importable t2 pi (right rcs) fl |} :
  Tot (importable (t1 * t2) pi rcs fl) = {
  wtyp = d1.wtyp * d2.wtyp;
  c_wtyp = weak_pair fl pi d1.wtyp #d1.c_wtyp d2.wtyp #d2.c_wtyp;
  import = (fun (x,y) eff_rcs ->
      match (d1.import x (left eff_rcs), d2.import y (right eff_rcs)) with
      | (Inl x, Inl y) -> Inl (x, y)
      | _ -> Inr Contract_failure)
}

instance importable_either
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 {| d1:importable t1 pi (left rcs) fl |} {| d2:importable t2 pi (right rcs) fl |} :
  Tot (importable (either t1 t2) pi rcs fl) = {
  wtyp = either d1.wtyp d2.wtyp;
  c_wtyp = weak_either fl pi d1.wtyp #d1.c_wtyp d2.wtyp #d2.c_wtyp;
  import = (fun x eff_rcs ->
      match x with
      | Inl x' -> begin
        match d1.import x' (left eff_rcs) with
        | Inl x'' -> Inl (Inl x'')
        | Inr err -> Inr err
      end
      | Inr y -> begin
        match d2.import y (right eff_rcs) with
        | Inl y' -> Inl (Inr y')
        | Inr err -> Inr err
      end)
}

instance importable_dpair_refined
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 pi (left rcs) fl |} {| d2:importable t2 pi (right rcs) fl |}
  {| d3:checkable2 p |} :
  Tot (importable (x:t1 & y:t2{p x y}) pi rcs fl) = {
  wtyp = d1.wtyp & d2.wtyp;
  c_wtyp = weak_pair fl pi d1.wtyp #d1.c_wtyp d2.wtyp #d2.c_wtyp;
  import = (fun ((x', y')) eff_rcs ->
      match (d1.import x' (left eff_rcs), d2.import y' (right eff_rcs)) with
       | (Inl x, Inl y) ->
            if check2 #t1 #t2 #p x y then Inl ((| x, y |) <: (x:t1 & y:t2{p x y})) else Inr Contract_failure
       | _ -> Inr Contract_failure)
}

(** *** Safe importable arrows **)
instance safe_importable_resexn
  (#pi:access_policy) (#rcs:tree pck_rc) (#fl:erased tflag)
  t1 {| d1:importable t1 pi rcs fl |} :
  Tot (safe_importable (resexn t1) pi rcs fl) = {
  swtyp = resexn d1.wtyp;
  c_swtyp = weak_resexn fl pi d1.wtyp #d1.c_wtyp;
  safe_import = (fun x eff_rcs ->
      match x with
      | Inl x' -> d1.import x' eff_rcs 
      | Inr y -> Inr y)
}
    
instance safe_importable_arrow
  (#pi:access_policy) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  (t1:Type) {| d1:exportable t1 pi (left rcs) fl |}
  (t2:Type) {| d2:importable t2 pi (right rcs) fl |} : 
  safe_importable ((x:t1) -> IIOpi (resexn t2) fl pi) pi rcs fl = {
  swtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
  c_swtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
  safe_import = (fun (f:d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi) eff_rcs (x:t1) -> 
    (let x' = d1.export (left eff_rcs) x in 
     let y : resexn d2.wtyp = f x' in
     (safe_importable_resexn t2 #d2).safe_import y (right eff_rcs)) <: IIOpi (resexn t2) fl pi)
}

(** The following four should be unified but I had universe problems **)
let enforce_post_args_res
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:access_policy)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (rc : rc_typ t1 (resexn t2))
  (eff_rc : eff_rc_typ fl rc) 
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2post : squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ (rc x h r lt) ==> post x h r lt))
  (f:t1 -> IIOpi (resexn t2) fl pi)
  (x:t1) :
  IIO (resexn t2) fl (pre x) (post x) by (explode ()) =
  let (| h, eff_rc' |) = eff_rc x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let r : resexn t2 = f x in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if eff_rc' r then r
  else Inr Contract_failure

let enforce_post_args
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:access_policy)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (rc : rc_typ t1 unit)
  (eff_rc : eff_rc_typ fl rc) 
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2post : squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ (rc x h () lt) ==> post x h r lt))
  (f:t1 -> IIOpi (resexn t2) fl pi)
  (x:t1) :
  IIO (resexn t2) fl (pre x) (post x) by (explode ()) =
  let (| h, eff_rc' |) = eff_rc x in
  Classical.forall_intro (lemma_suffixOf_append h);
  let r : resexn t2 = f x in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if eff_rc' () then r
  else Inr Contract_failure
  
let enforce_post_res
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:access_policy)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (rc : rc_typ unit (resexn t2))
  (eff_rc : eff_rc_typ fl rc) 
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2post : squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ (rc () h r lt) ==> post x h r lt))
  (f:t1 -> IIOpi (resexn t2) fl pi)
  (x:t1) :
  IIO (resexn t2) fl (pre x) (post x) by (explode ())=
  let (| h, eff_rc' |) = eff_rc () in
  Classical.forall_intro (lemma_suffixOf_append h);
  let r : resexn t2 = f x in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if eff_rc' r then r
  else Inr Contract_failure

let enforce_post
  (#t1:Type u#a)
  (#t2:Type u#b)
  (#fl:erased tflag)
  (pi:access_policy)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (rc : rc_typ unit unit)
  (eff_rc : eff_rc_typ fl rc) 
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> (post x h (Inr Contract_failure) lt)))
  (c2post : squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ (rc () h () lt) ==> post x h r lt))
  (f:t1 -> IIOpi (resexn t2) fl pi)
  (x:t1) :
  IIO (resexn t2) fl (pre x) (post x) by (explode ()) =
  let (| h, eff_rc' |) = eff_rc () in
  Classical.forall_intro (lemma_suffixOf_append h);
  let r : resexn t2 = f x in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if eff_rc' () then r
  else Inr Contract_failure

instance safe_importable_arrow_pre_post_args_res
  (#t1:Type) (#t2:Type)
  (#pi:access_policy) 
  (#rcs:(tree pck_rc){Node? rcs /\ (arg_typ (root rcs) == t1 /\ (ret_typ (root rcs) == (resexn t2))) })
  (#fl:erased tflag)
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post: squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ check (root rcs) x h r lt ==> post x h r lt)) 
  {| d1:exportable t1 pi (left rcs) fl |}
  {| d2:importable t2 pi (right rcs) fl |}:
  safe_importable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
   swtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
  c_swtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
  safe_import = (fun (f:(d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi)) eff_rcs ->
    let rcs' = (EmptyNode (left rcs) (right rcs)) in
    let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
    let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
    let (| rc_pck, eff_rc |) = root eff_rcs in
    enforce_post_args_res pi pre post (Mkdtuple3?._3 rc_pck) (rwtyp_eff_rc eff_rc) c1post c2post f')
  }

instance safe_importable_arrow_pre_post_res
  (#t1:Type) (#t2:Type)
  (#pi:access_policy) 
  (#rcs:(tree pck_rc){Node? rcs /\ (arg_typ (root rcs) == unit /\ (ret_typ (root rcs) == (resexn t2))) })
  (#fl:erased tflag)
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post: squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ ((Mkdtuple3?._3 (root rcs)) () h r lt) ==> post x h r lt)) 
  {| d1:exportable t1 pi (left rcs) fl |}
  {| d2:importable t2 pi (right rcs) fl |}:
  safe_importable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
   swtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
  c_swtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
  safe_import = (fun (f:(d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi)) eff_rcs ->
    let rcs' = (EmptyNode (left rcs) (right rcs)) in
    let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
    let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
    let (| rc_pck, eff_rc |) = root eff_rcs in
    enforce_post_res pi pre post (Mkdtuple3?._3 rc_pck) (rwtyp_eff_rc eff_rc) c1post c2post f')
  }

instance safe_importable_arrow_pre_post_args
  (#t1:Type) (#t2:Type)
  (#pi:access_policy) 
  (#rcs:(tree pck_rc){Node? rcs /\ (arg_typ (root rcs) == t1 /\ (ret_typ (root rcs) == unit)) })
  (#fl:erased tflag)
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post : squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ ((Mkdtuple3?._3 (root rcs)) x h () lt) ==> post x h r lt))
  {| d1:exportable t1 pi (left rcs) fl |}
  {| d2:importable t2 pi (right rcs) fl |} :
  safe_importable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
    swtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
    c_swtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
    safe_import = (fun (f:(d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi)) eff_rcs ->
      let rcs' = (EmptyNode (left rcs) (right rcs)) in
      let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
      let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
      let (| rc_pck, eff_rc |) = root eff_rcs in
      enforce_post_args pi pre post (Mkdtuple3?._3 rc_pck) (rwtyp_eff_rc eff_rc) c1post c2post f')
  }

instance safe_importable_arrow_pre_post
  (#t1:Type) (#t2:Type)
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)

  (#pi:access_policy) 
  (#rcs:(tree pck_rc){Node? rcs /\ (arg_typ (root rcs) == unit /\ (ret_typ (root rcs) == unit)) })

  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post : squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ check (root rcs) () h () lt ==> post x h r lt)) 

  (#fl:erased tflag)

  {| d1:exportable t1 pi (left rcs) fl |}
  {| d2:importable t2 pi (right rcs) fl |} :
  safe_importable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
    swtyp = d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi;
    c_swtyp = weak_arrow fl pi d1.c_wtyp (weak_resexn fl pi d2.wtyp #d2.c_wtyp);
    safe_import = (fun (f:(d1.wtyp -> IIOpi (resexn d2.wtyp) fl pi)) eff_rcs ->
      let rcs' = (EmptyNode (left rcs) (right rcs)) in
      let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
      let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
      let (| rc_pck, eff_rc |) = root eff_rcs in
      enforce_post pi pre post (Mkdtuple3?._3 rc_pck) (rwtyp_eff_rc eff_rc) c1post c2post f')
  }
