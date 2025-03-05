module HigherOrderContracts

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs

open Witnessable
open PolyIface
open SpecTree

instance targetlang_err pspec : targetlang pspec err = {
  wt = witnessable_err
}

class exportable_from pspec (styp: Type u#a) (st:spec_tree pspec) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang pspec ityp;
  [@@@no_method] export : hoc_tree st -> styp -> ityp;
  [@@@no_method] lemma_export_preserves_prref :
    x:styp -> prref:mref_pred -> hocs:hoc_tree st -> Lemma (requires (c_styp.satisfy x prref)) (ensures (c_ityp.wt.satisfy (export hocs x) (prref)))
}

class safe_importable_to pspec (styp: Type u#a) (st:spec_tree pspec) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang pspec ityp;
  [@@@no_method] safe_import : ityp -> hoc_tree st -> styp;
  [@@@no_method] lemma_safe_import_preserves_prref :
    x:ityp -> prref:mref_pred -> hocs:hoc_tree st -> Lemma (requires (c_ityp.wt.satisfy x (prref))) (ensures (c_styp.satisfy (safe_import x hocs) (prref)))
}

class importable_to pspec (styp: Type u#a) (st:spec_tree pspec) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang pspec ityp;
  [@@@no_method] import : ityp -> hoc_tree st -> resexn styp;
  [@@@no_method] lemma_import_preserves_prref :
    x:ityp -> prref:mref_pred -> hocs:hoc_tree st -> Lemma (requires (c_ityp.wt.satisfy x prref)) (ensures ((witnessable_sum styp err).satisfy (import x hocs) prref))
}

(** Exportable instances **)
instance targetlang_is_exportable t pspec {| c1:targetlang pspec t |} : exportable_from pspec t Leaf = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ()) }

instance exportable_unit pspec : exportable_from pspec unit Leaf = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = targetlang_unit _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_err pspec : exportable_from pspec err Leaf = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = targetlang_err _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_int pspec : exportable_from pspec int Leaf = {
  c_styp = witnessable_int;
  ityp = int;
  c_ityp = targetlang_int _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_option pspec t specs {| c:exportable_from pspec t specs |} : exportable_from pspec (option t) specs = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = targetlang_option _ c.ityp #c.c_ityp;
  export = (fun hocs x -> match x with | Some x -> Some (c.export hocs x) | None -> None);
  lemma_export_preserves_prref = (fun x p hocs -> match x with | Some x -> c.lemma_export_preserves_prref x p hocs | None -> ())
}

instance exportable_sum pspec t1 t2 s1 s2 {| c1:exportable_from pspec t1 s1 |} {| c2:exportable_from pspec t2 s2 |} : exportable_from pspec (either t1 t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_sum t1 t2 #c1.c_styp #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = targetlang_sum _ _ _ #c1.c_ityp #c2.c_ityp;
  export = (fun hocs x -> match x with | Inl x -> Inl (c1.export (left hocs) x) | Inr x -> Inr (c2.export (right hocs) x));
  lemma_export_preserves_prref = (fun x p hocs ->
    match x with | Inl x -> c1.lemma_export_preserves_prref x p (left hocs)| Inr x -> c2.lemma_export_preserves_prref x p (right hocs))
}

instance exportable_resexn pspec t spec {| c:exportable_from pspec t spec |} : exportable_from pspec (resexn t) (EmptyNode spec Leaf) =
  exportable_sum pspec t err spec Leaf #c #(exportable_err pspec)

instance exportable_pair pspec t1 t2 s1 s2 {| c1:exportable_from pspec t1 s1 |} {| c2:exportable_from pspec t2 s2 |} : exportable_from pspec (t1 * t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_pair t1 t2 #c1.c_styp #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = targetlang_pair _ _ _ #c1.c_ityp #c2.c_ityp;
  export = (fun hocs (x1, x2) -> (c1.export (left hocs) x1, c2.export (right hocs) x2));
  lemma_export_preserves_prref = (fun (x1, x2) p hocs -> c1.lemma_export_preserves_prref x1 p (left hocs); c2.lemma_export_preserves_prref x2 p (right hocs))
}

instance exportable_ref pspec t {| c:tc_shareable_type t |} : exportable_from pspec (ref t) Leaf = {
  c_styp = witnessable_mref t _ #solve;
  ityp = ref t;
  c_ityp = targetlang_ref _ t #c;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ _ -> ());
}

instance exportable_llist pspec t {| c:tc_shareable_type t |} :
  exportable_from pspec (linkedList t) Leaf = {
  c_styp = solve ;
  ityp = linkedList t ;
  c_ityp = solve ;
  export = (fun Leaf x -> x) ;
  lemma_export_preserves_prref = (fun _ _ _ -> ())
}

instance exportable_refinement pspec t spec {| c:exportable_from pspec t spec |} (p:t->Type0) : exportable_from pspec (x:t{p x}) spec = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  export = (fun hocs x -> c.export hocs x);
  lemma_export_preserves_prref = (fun x -> c.lemma_export_preserves_prref x);
}

instance exportable_arrow
  pspec
  (t1:Type) (t2:Type)
  s1 s2
  {| c1:importable_to pspec t1 s1 |}
  {| c2:exportable_from pspec t2 s2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
 // (_:squash (forall x h0 r h1. post x h0 r h1 ==> post_targetlang_arrow pspec #(resexn t2) #(witnessable_sum t2 err #c2.c_styp) h0 r h1))
 // (check:select_check pspec t1 unit (pre_targetlang_arrow pspec #_ #c1.c_styp)
 //   (fun x _ _ h1 -> pre x h1))
                (** ^ the fact that the check has a pre-condition means that the check does not have to enforce it
                      e.g., the invariant on the heap **)
  : exportable_from pspec (x:t1 -> ST (resexn t2) (pre x) (post x))
    (Node (SpecErr true t1 c1.c_styp pre t2 c2.c_styp post) s1 s2) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_targetlang_arrow pspec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_resexn #c2.ityp #c2.c_ityp.wt);
  c_ityp = targetlang_arrow pspec c1.ityp (resexn c2.ityp) #c1.c_ityp #(targetlang_sum pspec c2.ityp err #c2.c_ityp) ;
  export = (fun (hocs:hoc_tree _) (f:(x:t1 -> ST (resexn t2) (pre x) (post x))) (x:c1.ityp) ->
    let Node (| _, myhoc |) lhs rhs : hoc_tree _ = hocs in
    let EnforcePre check c_post = myhoc in
    match c1.import x lhs with
    | Inl x' -> begin
      c1.lemma_import_preserves_prref x (Mktuple3?._2 pspec) lhs;
      let (| _, cb_check |) = check x' in
      match cb_check () with
      | Inl _ -> begin
        let res : resexn t2 = f x' in
        c_post x' res;
        (exportable_resexn pspec t2 s2).lemma_export_preserves_prref res (Mktuple3?._2 pspec) (EmptyNode rhs Leaf);
        (exportable_resexn pspec t2 s2).export (EmptyNode rhs Leaf) res
      end
      | Inr err -> Inr err
    end
    | Inr err -> Inr err
  );
  lemma_export_preserves_prref = (fun _ _ _ -> ());
}

(** Importable instances **)
instance targetlang_is_safely_importable pspec t {| c1:targetlang pspec t |} : safe_importable_to pspec t Leaf = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance safe_importable_is_importable pspec t spec {| c1:safe_importable_to pspec t spec |} : importable_to pspec t spec = {
  c_styp = c1.c_styp;
  ityp = c1.ityp;
  c_ityp = c1.c_ityp;
  import = (fun x hocs -> Inl (c1.safe_import x hocs));
  lemma_import_preserves_prref = (fun x -> c1.lemma_safe_import_preserves_prref x);
}

instance safe_importable_unit pspec : safe_importable_to pspec unit Leaf = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = targetlang_unit _;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance safe_importable_err pspec : safe_importable_to pspec err Leaf = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = targetlang_err _;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance importable_option pspec t spec {| c:importable_to pspec t spec |} : importable_to pspec (option t) spec = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = targetlang_option _ c.ityp #c.c_ityp;
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

instance importable_sum pspec t1 t2 s1 s2 {| c1:importable_to pspec t1 s1 |} {| c2:importable_to pspec t2 s2 |} : importable_to pspec (either t1 t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_sum t1 t2 #c1.c_styp #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = targetlang_sum _ _ _ #c1.c_ityp #c2.c_ityp;
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

instance importable_pair pspec t1 t2 s1 s2 {| c1:importable_to pspec t1 s1 |} {| c2:importable_to pspec t2 s2 |} : importable_to pspec (t1 * t2) (EmptyNode s1 s2) = {
  c_styp = witnessable_pair t1 t2 #c1.c_styp #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = targetlang_pair _ _ _ #c1.c_ityp #c2.c_ityp;
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

instance safe_importable_ref pspec t {| c:tc_shareable_type t |} : safe_importable_to pspec (ref t) Leaf = {
  c_styp = witnessable_mref t _ #solve;
  ityp = ref t;
  c_ityp = targetlang_ref _ t;
  safe_import = (fun x Leaf -> x);
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance import_refinement pspec t spec {| c:importable_to pspec t spec |} (p:t->Type0) (check:(x:t -> r:bool{r ==> p x})): importable_to pspec (x:t{p x}) spec = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  import = (fun x hocs ->
    match (c.import x hocs) with
    | Inl x -> if check x then Inl x else Inr (Contract_failure "check of refinement failed")
    | Inr err -> Inr err);
  lemma_import_preserves_prref = (fun x -> c.lemma_import_preserves_prref x);
}

instance safe_importable_resexn pspec t s {| c:importable_to pspec t s |} : safe_importable_to pspec (resexn t) (EmptyNode s Leaf)= {
  c_styp = witnessable_sum t err #c.c_styp;
  ityp = resexn c.ityp;
  c_ityp = targetlang_sum _ c.ityp err #c.c_ityp;
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
  pspec
  (t1:Type) (t2:Type)
  s1 s2
  {| c1:exportable_from pspec t1 s1 |}
  {| c2:importable_to pspec t2 s2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
 // (_:squash (forall (x:t1) h0. pre x h0 ==> pre_targetlang_arrow pspec #_ #c1.c_styp x h0))
//  (_:squash (forall (x:t1) h0 e h1. pre x h0 /\ post_targetlang_arrow pspec #_ #(witnessable_sum t2 err #c2.c_styp) h0 (Inr e) h1 ==> post x h0 (Inr e) h1))
//  (capture_check:select_check pspec t1 (resexn t2) #(witnessable_sum _ err #c2.c_styp) pre post)
  : safe_importable_to pspec (x:t1 -> ST (resexn t2) (pre x) (post x)) (Node (SpecErr false t1 c1.c_styp pre t2 c2.c_styp post) s1 s2) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_targetlang_arrow pspec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_resexn #c2.ityp #c2.c_ityp.wt);
  c_ityp = targetlang_arrow _ c1.ityp (resexn c2.ityp) #_ #(targetlang_sum _ c2.ityp err #c2.c_ityp);
  safe_import = (fun (f:mk_targetlang_arrow pspec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp err #c2.c_ityp.wt)) (hocs:hoc_tree _) (x:t1) ->
    let Node (| _, myhoc |) lhs rhs : hoc_tree _ = hocs in
    let EnforcePost c_pre c_post check = myhoc in
    c_pre x;
    c1.lemma_export_preserves_prref x (Mktuple3?._2 pspec) lhs;
    let (| _, cb_check |) = check x in
    let x' = c1.export lhs x in
    let res : resexn c2.ityp = f x' in
    let fres = (safe_importable_resexn pspec t2 s2).safe_import res (EmptyNode rhs Leaf) in
    (safe_importable_resexn pspec t2 s2).lemma_safe_import_preserves_prref res (Mktuple3?._2 pspec) (EmptyNode rhs Leaf);
    match cb_check fres with
    | Inl _ -> fres
    | Inr err -> (c_post x err; (Inr err))
  );
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

instance safe_importable_arrow_safe
  pspec
  (t1:Type) (t2:Type)
  s1 s2
  {| c1:exportable_from pspec t1 s1 |}
  {| c2:safe_importable_to pspec t2 s2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
 // (_:squash (forall (x:t1) h0. pre x h0 ==> pre_targetlang_arrow pspec #_ #c1.c_styp x h0))
//  (_:squash (forall (x:t1) h0 r h1. pre x h0 /\ post_targetlang_arrow pspec #_ #c2.c_styp h0 r h1 ==> post x h0 r h1))
  : safe_importable_to pspec (x:t1 -> ST t2 (pre x) (post x)) (Node (Spec false t1 c1.c_styp pre t2 c2.c_styp post) s1 s2) = {
  c_styp = witnessable_arrow t1 t2 pre post;
  ityp = mk_targetlang_arrow pspec c1.ityp #c1.c_ityp.wt c2.ityp #c2.c_ityp.wt;
  c_ityp = targetlang_arrow _ c1.ityp c2.ityp #_ #c2.c_ityp;
  safe_import = (fun (f:mk_targetlang_arrow pspec c1.ityp #c1.c_ityp.wt c2.ityp #c2.c_ityp.wt) hocs (x:t1) ->
    let Node (| _, myhoc |) lhs rhs : hoc_tree _ = hocs in
    let TrivialPost c_pre c_post = myhoc in
    c_pre x;
    c1.lemma_export_preserves_prref x (Mktuple3?._2 pspec) lhs;
    let x' = c1.export lhs x in
    let res : c2.ityp = f x' in
    let fres = c2.safe_import res rhs in
    c_post x fres;
    c2.lemma_safe_import_preserves_prref res (Mktuple3?._2 pspec) rhs;
    fres
  );
  lemma_safe_import_preserves_prref = (fun _ _ _ -> ())
}

type f_eqx = x:ref int -> SST (resexn unit) (requires (fun h0 -> satisfy x (prref_c))) (ensures (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x))

let f_spec : pck_spec concrete_spec =
(SpecErr false (ref int) (exportable_refinement concrete_spec
                  (ref int)
                  Leaf
                  (fun _ -> l_True))
                .c_styp
              (fun x -> sst_pre (fun _ -> satisfy x prref_c))
              unit
              (safe_importable_is_importable concrete_spec unit Leaf).c_styp
              (fun x ->
                  sst_post (either unit err)
                    (fun _ -> satisfy x prref_c)
                    (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x)))

let f_eqx_is_safe_importable : safe_importable_to concrete_spec f_eqx (Node f_spec Leaf Leaf) =
  safe_importable_arrow concrete_spec
    (ref int) unit
    Leaf Leaf
    (fun x -> sst_pre (fun h0 -> satisfy x (prref_c)))
    (fun x -> sst_post _ _ (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x))


val unsafe_f : mk_interm_arrow (ref int) (resexn unit)
let unsafe_f x =
  recall (contains_pred x);
  recall (is_shared x);
  sst_write x 0;
  Inl ()

let f_hoc : hoc concrete_spec f_spec =
EnforcePost
    (fun _ -> ())
    (fun _ _ -> ())
    (fun rx ->
      let rx :ref int = rx in
      recall (contains_pred rx);
      let x = sst_read rx in
      let eh0 = get_heap () in
      let check : cb_check concrete_spec (ref int) (resexn unit) (fun x -> sst_pre (fun h0 -> satisfy x (prref_c))) (fun x -> sst_post _ _ (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x)) rx eh0 =
        (fun kres -> if x = sst_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))

let f_pkhoc : pck_hoc concrete_spec =
  (| f_spec, f_hoc |)

let f_tree : hoc_tree (Node f_spec Leaf Leaf) =
  Node f_pkhoc Leaf Leaf

let safe_f = f_eqx_is_safe_importable.safe_import unsafe_f f_tree

// x:ref int -> SST (y:ref int -> SST (resexn int) pre' post') pre post
//                                                   ^---^---cannot depend on x

type f_xeq5 = x:ref int -> SST (resexn int)
  (requires (fun h0 -> sel h0 x == 5 /\ satisfy x (prref_c)))
  (ensures (fun h0 r h1 -> (Inr? r \/ (Inl? r /\ Inl?.v r == 2)) /\ ((hrel_c) h0 h1)))

let f_xeq5_is_exportable : exportable_from concrete_spec f_xeq5 _ =
  exportable_arrow concrete_spec
    (ref int) int
    Leaf Leaf
    (fun x -> sst_pre (fun h0 -> sel h0 x == 5 /\ satisfy x (prref_c)))
    (fun x -> sst_post (resexn int) _ (fun h0 r h1 -> (Inr? r \/ (Inl? r /\ Inl?.v r == 2)) /\ ((hrel_c) h0 h1)))

let f_xeq5_spec : pck_spec concrete_spec =
  SpecErr true (ref ℤ) (safe_importable_is_importable concrete_spec (ref ℤ) Leaf).c_styp (λ x → sst_pre (λ h0 → sel h0 x == 5 ∧ satisfy x prref_c)) ℤ
(exportable_refinement concrete_spec ℤ Leaf (λ _ → l_True)).c_styp (λ x → sst_post (resexn ℤ) (λ h0 → sel h0 x == 5 ∧ satisfy x prref_c) (λ h0 r h1 → (Inr? r ∨ (Inl? r ∧ Inl?.v r == 2)) ∧ hrel_c h0 h1))

let f_xeq5_hoc : hoc concrete_spec f_xeq5_spec =
  EnforcePre
    (fun rx ->
      let rx :ref int = rx in
      let eh0 = get_heap () in
      let check : cb_check concrete_spec (ref int) _ (pre_targetlang_arrow concrete_spec #(SpecErr?.argt f_xeq5_spec) #(SpecErr?.wt_argt f_xeq5_spec)) (fun x _ _ h1 -> (SpecErr?.pre f_xeq5_spec) x h1) rx eh0 =
        (fun _ ->
          recall (contains_pred rx);
          if 5 = sst_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))
    (fun x r -> admit ())

let f_xeq5_pkhoc : pck_hoc concrete_spec =
  (| f_xeq5_spec, f_xeq5_hoc |)

let f_xeq5_tree : hoc_tree (Node f_xeq5_spec Leaf Leaf) =
  Node f_xeq5_pkhoc Leaf Leaf

val f_with_pre : f_xeq5
let f_with_pre x =
  recall (contains_pred x);
  let v = sst_read x in
  assert (v == 5);
  Inl (10 / v)

let f_with_dc = f_xeq5_is_exportable.export f_xeq5_tree f_with_pre

let gggtest =
  let x = sst_alloc_shared 0 in
  safe_f x

let _ =
  match gggtest with
  | Inl () ->
    IO.print_string "ok!\n"
  | Inr (Contract_failure s) ->
    IO.print_string ("Contract failure: " ^ s)
  | Inr e ->
    IO.print_string "another exn?!?!"
