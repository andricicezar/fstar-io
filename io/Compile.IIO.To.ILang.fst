module Compile.IIO.To.ILang

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Ghost

open Compiler.Languages
open TC.Checkable

(** **** Types **)

(** **** Tree **)
type tree (a: Type) =
  | Leaf : tree a
  | EmptyNode: left: tree a -> right: tree a -> tree a
  | Node: data: a -> left: tree a -> right: tree a -> tree a

let root (t:(tree 'a){Node? t}) = Node?.data t
let eleft (t:(tree 'a){EmptyNode? t}) = EmptyNode?.left t
let eright (t:(tree 'a){EmptyNode? t}) = EmptyNode?.right t
let left (t:(tree 'a){Node? t}) = Node?.left t
let right (t:(tree 'a){Node? t}) = Node?.right t

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

type rc_typ (t1:Type u#a) (t2:Type u#b) = t1 -> trace -> t2 -> trace -> bool

type eff_rc_typ_cont (fl:erased tflag) (t1:Type u#a) (t2:Type u#b) (rc:rc_typ t1 t2) (x:t1) (initial_h:erased trace) =
  y:t2 -> IIO bool fl (fun h -> (initial_h `suffix_of` h)) (fun current_h b lt -> 
       (initial_h `suffix_of` current_h) /\
       (let the_lt = get_local_trace initial_h current_h in
       apply_changes initial_h the_lt == current_h /\ lt == [] /\ (b <==> rc x initial_h y the_lt)))
  
type eff_rc_typ (fl:erased tflag) (#t1 #t2:Type) (rc:rc_typ t1 t2) =
  x:t1 -> IIO (initial_h:(erased trace) & eff_rc_typ_cont fl t1 t2 rc x initial_h) fl (fun _ -> True) (fun h (| initial_h, _ |) lt -> h == reveal initial_h /\ lt == [])

val enforce_rc : (#a:Type u#a) -> (#b:Type u#b) -> rc:rc_typ a b -> eff_rc_typ AllActions rc
let enforce_rc #a #b rc x =
  let initial_h = get_trace () in
  let cont : eff_rc_typ_cont AllActions a b rc x (hide initial_h) = 
    (fun y -> ( 
      let current_h = get_trace () in
      let lt = get_local_trace initial_h current_h in 
      rc x initial_h y lt)) in
  (| hide initial_h, cont |)

type pck_rc = (t1:Type u#a & t2:Type u#b & rc_typ t1 t2)
type pck_eff_rc (fl:erased tflag) = pck:pck_rc & eff_rc_typ fl (Mkdtuple3?._3 pck)

val make_rc_eff : pck_rc u#a u#b -> pck_eff_rc u#a u#b AllActions
let make_rc_eff r = (| r, (enforce_rc (Mkdtuple3?._3 r)) |)

type typ_eff_rcs (fl:erased tflag) (rcs:tree pck_rc) = 
  eff_rcs:(tree (pck_eff_rc fl)){
    equal_trees rcs (map_tree eff_rcs dfst)}

let make_rcs_eff (rcs:tree pck_rc) : typ_eff_rcs AllActions rcs =
  let r : tree (pck_eff_rc AllActions) = map_tree rcs make_rc_eff in
  assume (equal_trees rcs (map_tree r dfst));
  r

class exportable (t : Type u#a) (pi:monitorable_prop) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  etype : Type u#b;
  [@@@no_method]
  c_etype : ilang etype pi;
  [@@@no_method]
  export : typ_eff_rcs fl rcs -> t -> etype;
}

class safe_importable (t : Type u#a) (pi:monitorable_prop) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  sitype : Type u#b;
  [@@@no_method]
  c_sitype : ilang sitype pi;
  [@@@no_method]
  safe_import : sitype -> (typ_eff_rcs fl rcs -> t); 
}

class importable (t : Type u#a) (pi:monitorable_prop) (rcs:tree (pck_rc u#c u#d)) (fl:erased tflag) = {
  [@@@no_method]
  itype : Type u#b; 
  [@@@no_method]
  c_itype : ilang itype pi;
  [@@@no_method]
  import : itype -> (typ_eff_rcs fl rcs -> resexn t);
}

(** *** Exportable instances **)

instance ilang_is_exportable (#pi:monitorable_prop) (#rcs:(tree pck_rc){Leaf? rcs}) (#fl:erased tflag) t {| d1: ilang t pi |} : exportable t pi rcs fl = {
  etype = t;
  c_etype = d1;
  export = (fun Leaf x -> x)
}

instance exportable_unit (#pi:monitorable_prop) (#fl:erased tflag) : exportable unit pi Leaf fl = {
  etype = unit;
  c_etype = ilang_unit pi;
  export = (fun Leaf () -> ())
}

instance exportable_file_descr (#pi:monitorable_prop) (#fl:erased tflag) : exportable file_descr pi Leaf fl = {
  etype = file_descr;
  c_etype = ilang_file_descr pi;
  export = (fun Leaf fd -> fd)
}

instance exportable_refinement (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag) t {| d:exportable t pi rcs fl |} (p : t -> Type0) : exportable (x:t{p x}) pi rcs fl = {
  etype = d.etype;
  c_etype = d.c_etype;
  export = d.export
}

instance exportable_option
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi rcs fl |} :
  Tot (exportable (option t1) pi rcs fl) = {
  etype = option d1.etype;
  c_etype = ilang_option pi d1.etype #d1.c_etype;
  export = (fun eff_rcs x -> match x with | Some x' -> Some (d1.export eff_rcs x') | None -> None)
}


instance exportable_pair
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi (eleft rcs) fl |} t2 {| d2:exportable t2 pi (eright rcs) fl |} :
  Tot (exportable (t1 * t2) pi rcs fl) = {
  etype = d1.etype * d2.etype;
  c_etype = ilang_pair pi d1.etype #d1.c_etype d2.etype #d2.c_etype;
  export = (fun eff_rcs (x, y) -> (d1.export (eleft eff_rcs) x, d2.export (eright eff_rcs) y));
}

instance exportable_either
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:exportable t1 pi (eleft rcs) fl |} t2 {| d2:exportable t2 pi (eright rcs) fl |} :
  Tot (exportable (either t1 t2) pi rcs fl) = {
  etype = either d1.etype d2.etype;
  c_etype = ilang_either pi d1.etype #d1.c_etype d2.etype #d2.c_etype;
  export = (fun eff_rcs x -> 
      match x with | Inl x -> Inl (d1.export (eleft eff_rcs) x) | Inr x -> Inr (d2.export (eright eff_rcs) x))
}

instance ilang_resexn (pi:monitorable_prop) t1 {| d1:ilang t1 pi |} : ilang (resexn t1) pi = { mldummy = () }

(** *** Exportable arrows **)

instance exportable_arrow_with_no_pre_and_no_post
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  (t1:Type) {| d1:importable t1 pi (eleft rcs) fl |}
  (t2:Type) {| d2:exportable t2 pi (eright rcs) fl|} :
  exportable (t1 -> IIOpi (resexn t2) fl pi) pi rcs fl = {
    etype = d1.itype -> IIOpi (resexn d2.etype) fl pi;
    c_etype = ilang_arrow pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(t1 -> IIOpi (resexn t2) fl pi)) (x:d1.itype) ->
      match d1.import x (eleft eff_rcs) with
      | Inl x' -> begin
        match f x' with 
        | Inl x'' -> Inl (d2.export (eright eff_rcs) x'') 
        | Inr err -> Inr err
      end
      | Inr err -> Inr err
    )
  }

(** This is a design choice for making proofs easier. One can remove the post-condition **)
instance exportable_arrow_post_args
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:importable t1 pi (eleft rcs) fl |}
  t2 {| d2:exportable t2 pi (eright rcs) fl |}
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c1 : squash (forall x h lt r. post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> IIO (resexn t2) fl (fun _ -> True) (post x)) pi rcs fl = {
    etype = x:d1.itype -> IIOpi (resexn d2.etype) fl pi;
    c_etype = ilang_arrow #fl pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(x:t1 -> IIO (resexn t2) fl (fun _ -> True) (post x))) ->
      let f' : t1 -> IIOpi (resexn t2) fl pi = f in
      (exportable_arrow_with_no_pre_and_no_post t1 #d1 t2 #d2).export eff_rcs f');
  }

instance exportable_arrow_post
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 {| d1:importable t1 pi (eleft rcs) fl |}
  t2 {| d2:exportable t2 pi (eright rcs) fl |}
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

let retype_rc (#a #b #c #d:Type) (rc:rc_typ a b) : Pure (rc_typ c d) (requires (a == c /\ b == d)) (ensures (fun _ -> True)) = rc

val retype_eff_rc : (#fl:erased tflag) -> (#a:Type u#a) -> (#b:Type u#b) -> (#c:Type{c == a}) -> (#d:Type{d == b}) -> (#rc:rc_typ a b) -> (t : eff_rc_typ fl rc) -> (eff_rc_typ fl #c #d (retype_rc rc))
let retype_eff_rc #fl #a #b #c #d #rc eff_rc (x:c) = 
    let (| initial_h, cont |) = eff_rc x in
    let cont' : eff_rc_typ_cont fl c d (retype_rc rc) x initial_h = (fun (y:d) -> cont y) in
    (| initial_h, cont' |)

instance exportable_arrow_pre_post_args
  (t1:Type) (t2:Type)
  (#pi:monitorable_prop) 
  (#rcs:(tree pck_rc){Node? rcs /\ Mkdtuple3?._1 (root rcs) == t1 /\ (Mkdtuple3?._2 (root rcs) == unit)})
  (#fl:erased tflag)
  {| d1:importable t1 pi (left rcs) fl |}
  {| d2:exportable t2 pi (right rcs) fl |}
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall h x. (Mkdtuple3?._3 (root rcs)) x h () [] ==> pre x h))
  (#c1 : squash (forall x h lt r. pre x h /\ post x h r lt ==> enforced_locally pi h lt)) :
  exportable (x:t1 -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
    etype = d1.itype -> IIOpi (resexn d2.etype) fl pi; 
    c_etype = ilang_arrow pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(x:t1 -> IIO (resexn t2) fl (pre x) (post x))) ->
      let (| (| a, b, rc |), eff_rc |) = root eff_rcs in
      let eff_rc : eff_rc_typ fl #t1 #unit rc = retype_eff_rc eff_rc in
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
  (#pi:monitorable_prop) 
  (#rcs:(tree pck_rc){Node? rcs /\ Mkdtuple3?._1 (root rcs) == unit /\ (Mkdtuple3?._2 (root rcs) == unit)})
  (#fl:erased tflag)
  {| d1:importable t1 pi (left rcs) fl |}
  {| d2:exportable t2 pi (right rcs) fl |}
  (pre : trace -> Type0)
  (post : trace -> resexn t2 -> trace -> Type0) 
  (#c_pre : squash (forall h. (Mkdtuple3?._3 (root rcs)) () h () [] ==> pre h))
  (#c1 : squash (forall h lt r. pre h /\ post h r lt ==> enforced_locally pi h lt)) :
  exportable (t1 -> IIO (resexn t2) fl pre post) pi rcs fl = {
    etype = d1.itype -> IIOpi (resexn d2.etype) fl pi; 
    c_etype = ilang_arrow pi d1.c_itype (ilang_resexn pi d2.etype #d2.c_etype);
    export = (fun eff_rcs (f:(t1 -> IIO (resexn t2) fl pre post)) ->
      let (| (| a, b, rc |), eff_rc |) = root eff_rcs in
      let eff_rc : eff_rc_typ fl #unit #unit rc = retype_eff_rc eff_rc in
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
let ilang_is_safely_importable (#pi:monitorable_prop) (#rcs:(tree pck_rc){Leaf? rcs}) (#fl:erased tflag) #t (d:ilang t pi) : safe_importable t pi rcs fl = {
  sitype = t;
  c_sitype = d;
  safe_import = (fun x Leaf -> x); 
}

instance importable_unit (#pi:monitorable_prop) (#fl:erased tflag) : importable unit pi Leaf fl = {
  itype = unit;
  c_itype = ilang_unit pi;
  import = (fun () Leaf -> Inl ())
}

instance importable_file_descr (#pi:monitorable_prop) (#fl:erased tflag) : importable file_descr pi Leaf fl = {
  itype = file_descr;
  c_itype = ilang_file_descr pi;
  import = (fun fd Leaf -> Inl fd)
}

(** *** Importable instances **)

instance safe_importable_is_importable (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag) #t (d:safe_importable t pi rcs fl) : importable t pi rcs fl = {
  itype = d.sitype;
  c_itype = d.c_sitype;
  import = (fun x eff_rcs -> Inl (d.safe_import x eff_rcs))
}

instance importable_refinement
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t {| d:importable t pi rcs fl |}
  (rp : t -> Type0) {| checkable rp |} :
  Tot (importable (x:t{rp x}) pi rcs fl) = {
  itype = d.itype;
  c_itype = d.c_itype;
  import = (fun (x:d.itype) eff_rcs ->
    (match d.import x eff_rcs with
    | Inl x ->
      if check #t #rp x then Inl x 
      else Inr Contract_failure
    | Inr err -> Inr err) <: resexn (x:t{rp x}))
}
    
instance importable_option
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t {| d:importable t pi rcs fl |} :
  Tot (importable (option t) pi rcs fl) = {
  itype = option d.itype;
  c_itype = ilang_option pi d.itype #d.c_itype;
  import = (fun (x:option d.itype) eff_rcs ->
    match x with
    | Some x' -> begin
      match d.import x' eff_rcs with
      | Inl x'' -> Inl (Some x'')
      | Inr err -> Inr err
    end
    | None -> Inr Contract_failure)
}

instance importable_pair
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 {| d1:importable t1 pi (eleft rcs) fl |} {| d2:importable t2 pi (eright rcs) fl |} :
  Tot (importable (t1 * t2) pi rcs fl) = {
  itype = d1.itype * d2.itype;
  c_itype = ilang_pair pi d1.itype #d1.c_itype d2.itype #d2.c_itype;
  import = (fun (x,y) eff_rcs ->
      match (d1.import x (eleft eff_rcs), d2.import y (eright eff_rcs)) with
      | (Inl x, Inl y) -> Inl (x, y)
      | _ -> Inr Contract_failure)
}

instance importable_either
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 {| d1:importable t1 pi (eleft rcs) fl |} {| d2:importable t2 pi (eright rcs) fl |} :
  Tot (importable (either t1 t2) pi rcs fl) = {
  itype = either d1.itype d2.itype;
  c_itype = ilang_either pi d1.itype #d1.c_itype d2.itype #d2.c_itype;
  import = (fun x eff_rcs ->
      match x with
      | Inl x' -> begin
        match d1.import x' (eleft eff_rcs) with
        | Inl x'' -> Inl (Inl x'')
        | Inr err -> Inr err
      end
      | Inr y -> begin
        match d2.import y (eright eff_rcs) with
        | Inl y' -> Inl (Inr y')
        | Inr err -> Inr err
      end)
}

instance importable_dpair_refined
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 pi (eleft rcs) fl |} {| d2:importable t2 pi (eright rcs) fl |}
  {| d3:checkable2 p |} :
  Tot (importable (x:t1 & y:t2{p x y}) pi rcs fl) = {
  itype = d1.itype & d2.itype;
  c_itype = ilang_pair pi d1.itype #d1.c_itype d2.itype #d2.c_itype;
  import = (fun ((x', y')) eff_rcs ->
      match (d1.import x' (eleft eff_rcs), d2.import y' (eright eff_rcs)) with
       | (Inl x, Inl y) ->
            if check2 #t1 #t2 #p x y then Inl ((| x, y |) <: (x:t1 & y:t2{p x y})) else Inr Contract_failure
       | _ -> Inr Contract_failure)
}

(** *** Safe importable arrows **)
instance safe_importable_resexn
  (#pi:monitorable_prop) (#rcs:tree pck_rc) (#fl:erased tflag)
  t1 {| d1:importable t1 pi rcs fl |} :
  Tot (safe_importable (resexn t1) pi rcs fl) = {
  sitype = resexn d1.itype;
  c_sitype = ilang_resexn pi d1.itype #d1.c_itype;
  safe_import = (fun x eff_rcs ->
      match x with
      | Inl x' -> d1.import x' eff_rcs 
      | Inr y -> Inr y)
}
    
instance safe_importable_arrow
  (#pi:monitorable_prop) (#rcs:(tree pck_rc){EmptyNode? rcs}) (#fl:erased tflag)
  (t1:Type) {| d1:exportable t1 pi (eleft rcs) fl |}
  (t2:Type) {| d2:importable t2 pi (eright rcs) fl |} : 
  safe_importable ((x:t1) -> IIOpi (resexn t2) fl pi) pi rcs fl = {
  sitype = d1.etype -> IIOpi (resexn d2.itype) fl pi;
  c_sitype = ilang_arrow pi d1.c_etype (ilang_resexn pi d2.itype #d2.c_itype);
  safe_import = (fun (f:d1.etype -> IIOpi (resexn d2.itype) fl pi) eff_rcs (x:t1) -> 
    (let x' = d1.export (eleft eff_rcs) x in 
     let y : resexn d2.itype = f x' in
     (safe_importable_resexn t2 #d2).safe_import y (eright eff_rcs)) <: IIOpi (resexn t2) fl pi)
}

let enforce_post_args
  (#t1 #t2:Type)
  (#fl:erased tflag)
  (pi:monitorable_prop)
  (pre:t1 -> trace -> Type0)
  (post:t1 -> trace -> resexn t2 -> trace -> Type0)
  (rc : rc_typ t1 (resexn t2))
  (eff_rc : eff_rc_typ fl t1 (resexn t2) rc) 
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
  
let enforce_post
  (#t1 #t2:Type)
  (#fl:erased tflag)
  (pi:monitorable_prop)
  (pre:trace -> Type0)
  (post:trace -> resexn t2 -> trace -> Type0)
  (rc : unit -> trace -> resexn t2 -> trace -> bool)
  (eff_rc : eff_rc_typ fl unit (resexn t2) rc) 
  (c1post : squash (forall h lt. pre h /\ enforced_locally pi h lt ==> (post h (Inr Contract_failure) lt)))
  (c2post : squash (forall h r lt. pre h /\ enforced_locally pi h lt /\ (rc () h r lt) ==> post h r lt))
  (f:t1 -> IIOpi (resexn t2) fl pi)
  (x:t1) :
  IIO (resexn t2) fl pre post by (explode ())=
  let (| h, eff_rc' |) = eff_rc () in
  Classical.forall_intro (lemma_suffixOf_append h);
  let r : resexn t2 = f x in
  Classical.forall_intro_2 (Classical.move_requires_2 (lemma_append_rev_inv_tail h));
  if eff_rc' r then r
  else Inr Contract_failure

instance safe_importable_arrow_pre_post_args
  (t1:Type) (t2:Type)
  (#pi:monitorable_prop) 
  (#rcs:(tree pck_rc){Node? rcs /\ (Mkdtuple3?._1 (root rcs) == t1 /\ (Mkdtuple3?._2 (root rcs) == (resexn t2))) })
  (#fl:erased tflag)
  {| d1:exportable t1 pi (left rcs) fl |}
  {| d2:importable t2 pi (right rcs) fl |}
  (pre : t1 -> trace -> Type0)
  (post : t1 -> trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall x h lt. pre x h /\ enforced_locally pi h lt ==> post x h (Inr Contract_failure) lt))
  (c2post: squash (forall x h r lt. pre x h /\ enforced_locally pi h lt /\ ((Mkdtuple3?._3 (root rcs)) x h r lt) ==> post x h r lt)) :
  safe_importable ((x:t1) -> IIO (resexn t2) fl (pre x) (post x)) pi rcs fl = {
  sitype = d1.etype -> IIOpi (resexn d2.itype) fl pi;
  c_sitype = ilang_arrow pi d1.c_etype (ilang_resexn pi d2.itype #d2.c_itype);
  safe_import = (fun (f:(d1.etype -> IIOpi (resexn d2.itype) fl pi)) eff_rcs ->
    let rcs' = (EmptyNode (left rcs) (right rcs)) in
    let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
    let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
    let (| rc_pck, eff_rc |) = root eff_rcs in
    enforce_post_args pi pre post (Mkdtuple3?._3 rc_pck) (retype_eff_rc eff_rc) c1post c2post f')
}

instance safe_importable_arrow_pre_post
  (#t1:Type) (#t2:Type)
  (#pi:monitorable_prop) 
  (#rcs:(tree pck_rc){Node? rcs /\ (Mkdtuple3?._1 (root rcs) == unit /\ (Mkdtuple3?._2 (root rcs) == (resexn t2))) })
  (#fl:erased tflag)
  (d1:exportable t1 pi (left rcs) fl)
  (d2:importable t2 pi (right rcs) fl)
  (pre : trace -> Type0)
  (post : trace -> resexn t2 -> trace -> Type0)
  (c1post : squash (forall h lt. pre h /\ enforced_locally pi h lt ==> post h (Inr Contract_failure) lt))
  (c2post: squash (forall h r lt. pre h /\ enforced_locally pi h lt /\ ((Mkdtuple3?._3 (root rcs)) () h r lt) ==> post h r lt)) :
  safe_importable (t1 -> IIO (resexn t2) fl pre post) pi rcs fl = {
  sitype = d1.etype -> IIOpi (resexn d2.itype) fl pi;
  c_sitype = ilang_arrow pi d1.c_etype (ilang_resexn pi d2.itype #d2.c_itype);
  safe_import = (fun (f:(d1.etype -> IIOpi (resexn d2.itype) fl pi)) eff_rcs ->
    let rcs' = (EmptyNode (left rcs) (right rcs)) in
    let eff_rcs' = (EmptyNode (left eff_rcs) (right eff_rcs)) in
    let f' = (safe_importable_arrow #_ #rcs' t1 #d1 t2 #d2).safe_import f eff_rcs' in
    let (| rc_pck, eff_rc |) = root eff_rcs in
    enforce_post pi pre post (Mkdtuple3?._3 rc_pck) (retype_eff_rc eff_rc) c1post c2post f')
}
