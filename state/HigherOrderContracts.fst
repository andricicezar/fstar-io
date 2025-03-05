module HigherOrderContracts

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs

open Witnessable
open PolyIface
open SpecTree

instance poly_iface_err a3p : poly_iface a3p err = {
  wt = witnessable_err
}

class exportable_from a3p (styp: Type u#a) (st:spec_tree) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : poly_iface a3p ityp;
  [@@@no_method] export : hoc_tree a3p st -> styp -> ityp;
  [@@@no_method] lemma_export_preserves_prref :
    x:styp -> prref:mref_pred -> hocs:hoc_tree a3p st -> Lemma (requires (c_styp.satisfy x prref)) (ensures (c_ityp.wt.satisfy (export hocs x) (prref)))
}

class safe_importable_to a3p (styp: Type u#a) (st:spec_tree) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : poly_iface a3p ityp;
  [@@@no_method] safe_import : ityp -> hoc_tree a3p st -> styp;
  [@@@no_method] lemma_safe_import_preserves_prref :
    x:ityp -> prref:mref_pred -> hocs:hoc_tree a3p st -> Lemma (requires (c_ityp.wt.satisfy x (prref))) (ensures (c_styp.satisfy (safe_import x hocs) (prref)))
}

class importable_to a3p (styp: Type u#a) (st:spec_tree) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : poly_iface a3p ityp;
  [@@@no_method] import : ityp -> hoc_tree a3p st -> resexn styp;
  [@@@no_method] lemma_import_preserves_prref :
    x:ityp -> prref:mref_pred -> hocs:hoc_tree a3p st -> Lemma (requires (c_ityp.wt.satisfy x prref)) (ensures ((witnessable_sum styp err).satisfy (import x hocs) prref))
}

(** Exportable instances **)
instance poly_iface_is_exportable t a3p {| c1:poly_iface a3p t |} : exportable_from a3p t Leaf = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ()) }

instance exportable_unit a3p : exportable_from a3p unit Leaf = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = poly_iface_unit _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_err a3p : exportable_from a3p err Leaf = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = poly_iface_err _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_int a3p : exportable_from a3p int Leaf = {
  c_styp = witnessable_int;
  ityp = int;
  c_ityp = poly_iface_int _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_option a3p t specs {| c:exportable_from a3p t specs |} : exportable_from a3p (option t) specs = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = poly_iface_option _ c.ityp #c.c_ityp;
  export = (fun hocs x -> match x with | Some x -> Some (c.export hocs x) | None -> None);
  lemma_export_preserves_prref = (fun x p hocs -> match x with | Some x -> c.lemma_export_preserves_prref x p hocs | None -> ())
}

instance exportable_sum a3p t1 t2 s1 s2 {| c1:exportable_from a3p t1 s1 |} {| c2:exportable_from a3p t2 s2 |} : exportable_from a3p (either t1 t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_sum t1 t2 #c1.c_styp #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = poly_iface_sum _ _ _ #c1.c_ityp #c2.c_ityp;
  export = (fun hocs x -> match x with | Inl x -> Inl (c1.export (left hocs) x) | Inr x -> Inr (c2.export (right hocs) x));
  lemma_export_preserves_prref = (fun x p hocs ->
    match x with | Inl x -> c1.lemma_export_preserves_prref x p (left hocs)| Inr x -> c2.lemma_export_preserves_prref x p (right hocs))
}

instance exportable_resexn a3p t spec {| c:exportable_from a3p t spec |} : exportable_from a3p (resexn t) (EmptyNode spec Leaf) =
  exportable_sum a3p t err spec Leaf #c #(exportable_err a3p)

instance exportable_pair a3p t1 t2 s1 s2 {| c1:exportable_from a3p t1 s1 |} {| c2:exportable_from a3p t2 s2 |} : exportable_from a3p (t1 * t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_pair t1 t2 #c1.c_styp #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = poly_iface_pair _ _ _ #c1.c_ityp #c2.c_ityp;
  export = (fun hocs (x1, x2) -> (c1.export (left hocs) x1, c2.export (right hocs) x2));
  lemma_export_preserves_prref = (fun (x1, x2) p hocs -> c1.lemma_export_preserves_prref x1 p (left hocs); c2.lemma_export_preserves_prref x2 p (right hocs))
}

instance exportable_ref a3p t {| c:tc_shareable_type t |} : exportable_from a3p (ref t) Leaf = {
  c_styp = witnessable_mref t _ #solve;
  ityp = ref t;
  c_ityp = poly_iface_ref _ t #c;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ());
}

instance exportable_llist a3p t {| c:tc_shareable_type t |} :
  exportable_from a3p (linkedList t) Leaf = {
  c_styp = solve ;
  ityp = linkedList t ;
  c_ityp = solve ;
  export = (fun Leaf x -> x) ;
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_refinement a3p t spec {| c:exportable_from a3p t spec |} (p:t->Type0) : exportable_from a3p (x:t{p x}) spec = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  export = (fun hocs x -> c.export hocs x);
  lemma_export_preserves_prref = (fun x -> c.lemma_export_preserves_prref x);
}

instance exportable_arrow
  a3p
  (t1:Type) (t2:Type)
  s1 s2
  {| c1:importable_to a3p t1 s1 |}
  {| c2:exportable_from a3p t2 s2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
 // (_:squash (forall x h0 r h1. post x h0 r h1 ==> post_poly_arrow a3p #(resexn t2) #(witnessable_sum t2 err #c2.c_styp) h0 r h1))
 // (check:select_check a3p t1 unit (pre_poly_arrow a3p #_ #c1.c_styp)
 //   (fun x _ _ h1 -> pre x h1))
                (** ^ the fact that the check has a pre-condition means that the check does not have to enforce it
                      e.g., the invariant on the heap **)
  : exportable_from a3p (x:t1 -> ST (resexn t2) (pre x) (post x)) //u#(max 1 a b) u#(max 1 a b) 
    (Node (SpecErr true t1 c1.c_styp pre t2 c2.c_styp post) s1 s2) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_resexn c2.ityp #c2.c_ityp.wt);
  c_ityp = poly_iface_arrow a3p c1.ityp (resexn c2.ityp) #c1.c_ityp #(poly_iface_sum a3p c2.ityp err #c2.c_ityp) ;
  export = (fun (hocs:hoc_tree a3p _) (f:(x:t1 -> ST (resexn t2) (pre x) (post x))) (x:c1.ityp) ->
    let Node (| _, myhoc |) lhs rhs : hoc_tree a3p _ = hocs in
    let EnforcePre check c_post = myhoc in
    match c1.import x lhs with
    | Inl x' -> begin
      c1.lemma_import_preserves_prref x (Mktuple3?._2 a3p) lhs;
      let (| _, cb_check |) = check x' in
      match cb_check () with
      | Inl _ -> begin
        let res : resexn t2 = f x' in
        c_post x' res;
        (exportable_resexn a3p t2 s2).lemma_export_preserves_prref res (Mktuple3?._2 a3p) (EmptyNode rhs Leaf);
        (exportable_resexn a3p t2 s2).export (EmptyNode rhs Leaf) res
      end
      | Inr err -> Inr err
    end
    | Inr err -> Inr err
  );
  lemma_export_preserves_prref = (fun _ _ _ -> ());
}

(** Importable instances **)
instance poly_iface_is_safely_importable a3p t {| c1:poly_iface a3p t |} : safe_importable_to a3p t Leaf = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance safe_importable_is_importable a3p t spec {| c1:safe_importable_to a3p t spec |} : importable_to a3p t spec = {
  c_styp = c1.c_styp;
  ityp = c1.ityp;
  c_ityp = c1.c_ityp;
  import = (fun x hocs -> Inl (c1.safe_import x hocs));
  lemma_import_preserves_prref = (fun x -> c1.lemma_safe_import_preserves_prref x);
}

instance safe_importable_unit a3p : safe_importable_to a3p unit Leaf = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = poly_iface_unit _;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance safe_importable_err a3p : safe_importable_to a3p err Leaf = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = poly_iface_err _;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance importable_option a3p t spec {| c:importable_to a3p t spec |} : importable_to a3p (option t) spec = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = poly_iface_option _ c.ityp #c.c_ityp;
  import = (fun x hocs ->
    match x with
    | Some x -> begin
      match c.import x hocs with
      | Inl x -> Inl (Some x)
      | Inr err -> Inr err
    end
    | None -> Inl None);
  lemma_import_preserves_prref = (fun x p hocs ->
    match x with
    | Some x -> c.lemma_import_preserves_prref x p hocs
    | None -> ())
}

instance importable_sum a3p t1 t2 s1 s2 {| c1:importable_to a3p t1 s1 |} {| c2:importable_to a3p t2 s2 |} : importable_to a3p (either t1 t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_sum t1 t2 #c1.c_styp #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = poly_iface_sum _ _ _ #c1.c_ityp #c2.c_ityp;
  import = (fun x hocs ->
    match x with
    | Inl x -> begin
      match c1.import x (left hocs) with
      | Inl x -> Inl (Inl x)
      | Inr err -> Inr err
    end
    | Inr x -> begin
      match c2.import x (right hocs) with
      | Inl x -> Inl (Inr x)
      | Inr err -> Inr err
    end);
  lemma_import_preserves_prref = (fun x p hocs ->
    match x with
    | Inl x -> c1.lemma_import_preserves_prref x p (left hocs)
    | Inr x -> c2.lemma_import_preserves_prref x p (right hocs))
}

instance importable_pair a3p t1 t2 s1 s2 {| c1:importable_to a3p t1 s1 |} {| c2:importable_to a3p t2 s2 |} : importable_to a3p (t1 * t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_pair t1 t2 #c1.c_styp #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = poly_iface_pair _ _ _ #c1.c_ityp #c2.c_ityp;
  import = (fun (x, x') hocs ->
    match c1.import x (left hocs) with
    | Inl x -> begin
      match c2.import x' (right hocs) with
      | Inl x' -> Inl (x,x')
      | Inr err -> Inr err
    end
    | Inr err -> Inr err);
  lemma_import_preserves_prref = (fun x p hocs ->
    c1.lemma_import_preserves_prref (fst x) p (left hocs);
    c2.lemma_import_preserves_prref (snd x) p (right hocs))
}

instance safe_importable_ref a3p t {| c:tc_shareable_type t |} : safe_importable_to a3p (ref t) Leaf = {
  c_styp = witnessable_mref t _ #solve;
  ityp = ref t;
  c_ityp = poly_iface_ref _ t;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance import_refinement a3p t spec {| c:importable_to a3p t spec |} (p:t->Type0) (check:(x:t -> r:bool{r ==> p x})): importable_to a3p (x:t{p x}) spec = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  import = (fun x hocs ->
    match (c.import x hocs) with
    | Inl x -> if check x then Inl x else Inr (Contract_failure "check of refinement failed")
    | Inr err -> Inr err);
  lemma_import_preserves_prref = (fun x -> c.lemma_import_preserves_prref x);
}

instance safe_importable_resexn a3p t s {| c:importable_to a3p t s |} : safe_importable_to a3p (resexn t) (EmptyNode s Leaf)= {
  c_styp = witnessable_sum t err #c.c_styp;
  ityp = resexn c.ityp;
  c_ityp = poly_iface_sum _ c.ityp err #c.c_ityp;
  safe_import = (fun x hocs ->
    match x with
    | Inl x -> begin
      match c.import x (left hocs) with
      | Inl x -> Inl x
      | Inr err -> Inr err
    end
    | Inr err -> Inr err
    );
  lemma_safe_import_preserves_prref = (fun x p hocs ->
    match x with
    | Inl x -> c.lemma_import_preserves_prref x p (left hocs)
    | Inr err -> ())
}

instance safe_importable_arrow
  a3p
  (t1:Type) (t2:Type)
  s1 s2
  {| c1:exportable_from a3p t1 s1 |}
  {| c2:importable_to a3p t2 s2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
 // (_:squash (forall (x:t1) h0. pre x h0 ==> pre_poly_arrow a3p #_ #c1.c_styp x h0))
//  (_:squash (forall (x:t1) h0 e h1. pre x h0 /\ post_poly_arrow a3p #_ #(witnessable_sum t2 err #c2.c_styp) h0 (Inr e) h1 ==> post x h0 (Inr e) h1))
//  (capture_check:select_check a3p t1 (resexn t2) #(witnessable_sum _ err #c2.c_styp) pre post)
  : safe_importable_to a3p (x:t1 -> ST (resexn t2) (pre x) (post x)) (Node (SpecErr false t1 c1.c_styp pre t2 c2.c_styp post) s1 s2) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_resexn c2.ityp #c2.c_ityp.wt);
  c_ityp = poly_iface_arrow _ c1.ityp (resexn c2.ityp) #_ #(poly_iface_sum _ c2.ityp err #c2.c_ityp);
  safe_import = (fun (f:mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp err #c2.c_ityp.wt)) (hocs:hoc_tree a3p _) (x:t1) ->
    let Node (| _, myhoc |) lhs rhs : hoc_tree a3p _ = hocs in
    let EnforcePost c_pre c_post check = myhoc in
    c_pre x;
    c1.lemma_export_preserves_prref x (Mktuple3?._2 a3p) lhs;
    let (| _, cb_check |) = check x in
    let x' = c1.export lhs x in
    let res : resexn c2.ityp = f x' in
    let fres = (safe_importable_resexn a3p t2 s2).safe_import res (EmptyNode rhs Leaf) in
    (safe_importable_resexn a3p t2 s2).lemma_safe_import_preserves_prref res (Mktuple3?._2 a3p) (EmptyNode rhs Leaf);
    match cb_check fres with
    | Inl _ -> fres
    | Inr err -> (c_post x err; (Inr err))
  );
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance safe_importable_arrow_safe
  a3p
  (t1:Type) (t2:Type)
  s1 s2
  {| c1:exportable_from a3p t1 s1 |}
  {| c2:safe_importable_to a3p t2 s2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
 // (_:squash (forall (x:t1) h0. pre x h0 ==> pre_poly_arrow a3p #_ #c1.c_styp x h0))
//  (_:squash (forall (x:t1) h0 r h1. pre x h0 /\ post_poly_arrow a3p #_ #c2.c_styp h0 r h1 ==> post x h0 r h1))
  : safe_importable_to a3p (x:t1 -> ST t2 (pre x) (post x)) (Node (Spec false t1 c1.c_styp pre t2 c2.c_styp post) s1 s2) = {
  c_styp = witnessable_arrow t1 t2 pre post;
  ityp = mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt c2.ityp #c2.c_ityp.wt;
  c_ityp = poly_iface_arrow _ c1.ityp c2.ityp #_ #c2.c_ityp;
  safe_import = (fun (f:mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt c2.ityp #c2.c_ityp.wt) hocs (x:t1) ->
    let Node (| _, myhoc |) lhs rhs : hoc_tree a3p _ = hocs in
    let TrivialPost c_pre c_post = myhoc in
    c_pre x;
    c1.lemma_export_preserves_prref x (Mktuple3?._2 a3p) lhs;
    let x' = c1.export lhs x in
    let res : c2.ityp = f x' in
    let fres = c2.safe_import res rhs in
    c_post x fres;
    c2.lemma_safe_import_preserves_prref res (Mktuple3?._2 a3p) rhs;
    fres
  );
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}