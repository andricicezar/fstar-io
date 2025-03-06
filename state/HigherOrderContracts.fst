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
    x:styp -> hocs:hoc_tree a3p st -> Lemma (requires (c_styp.satisfy x (prref a3p))) (ensures (c_ityp.wt.satisfy (export hocs x) (prref a3p)))
}

class safe_importable_to a3p (styp: Type u#a) (st:spec_tree) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : poly_iface a3p ityp;
  [@@@no_method] safe_import : hoc_tree a3p st -> ityp -> styp;
  [@@@no_method] lemma_safe_import_preserves_prref :
    x:ityp -> hocs:hoc_tree a3p st -> Lemma (requires (c_ityp.wt.satisfy x (prref a3p))) (ensures (c_styp.satisfy (safe_import hocs x) (prref a3p)))
}

class importable_to a3p (styp: Type u#a) (st:spec_tree) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : poly_iface a3p ityp;
  [@@@no_method] import : hoc_tree a3p st -> ityp -> resexn styp;
  [@@@no_method] lemma_import_preserves_prref :
    x:ityp -> hocs:hoc_tree a3p st -> Lemma (requires (c_ityp.wt.satisfy x (prref a3p))) (ensures ((witnessable_sum styp err).satisfy (import hocs x) (prref a3p)))
}

(** Exportable instances **)
instance poly_iface_is_exportable a3p t {| c1:poly_iface a3p t |} : exportable_from a3p t Leaf = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ -> ()) }

let mk_exportable 
  #styp (c_styp:witnessable styp) 
  #ityp #a3p (c_ityp:poly_iface a3p ityp) 
  #st 
  (export:hoc_tree a3p st -> styp -> ityp) 
  (lemma: (x:styp -> hocs:hoc_tree a3p st -> Lemma (requires (c_styp.satisfy x (prref a3p))) (ensures (c_ityp.wt.satisfy (export hocs x) (prref a3p)))))
  : exportable_from a3p styp st = {
  c_styp = c_styp;
  ityp = ityp;
  c_ityp = c_ityp;
  export = export;
  lemma_export_preserves_prref = lemma
}

instance exportable_unit a3p : exportable_from a3p unit Leaf =
  mk_exportable 
    witnessable_unit 
    (poly_iface_unit a3p)  
    (fun Leaf x -> x) (fun _ _ -> ())

instance exportable_err a3p : exportable_from a3p err Leaf = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = poly_iface_err _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ -> ())
}

instance exportable_int a3p : exportable_from a3p int Leaf = {
  c_styp = witnessable_int;
  ityp = int;
  c_ityp = poly_iface_int _;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ -> ())
}

instance exportable_option a3p t st {| c:exportable_from a3p t st |} : exportable_from a3p (option t) st = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = poly_iface_option _ c.ityp #c.c_ityp;
  export = (fun hocs x -> match x with | Some x -> Some (c.export hocs x) | None -> None);
  lemma_export_preserves_prref = (fun x hocs -> match x with | Some x -> c.lemma_export_preserves_prref x hocs | None -> ())
}

instance exportable_sum a3p t1 st1 {| c1:exportable_from a3p t1 st1 |} t2 st2 {| c2:exportable_from a3p t2 st2 |} : exportable_from a3p (either t1 t2) (EmptyNode st1 st2) = {
  c_styp = witnessable_sum t1 #c1.c_styp t2 #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = poly_iface_sum _ _ #c1.c_ityp _ #c2.c_ityp;
  export = (fun hocs x -> match x with | Inl x -> Inl (c1.export (left hocs) x) | Inr x -> Inr (c2.export (right hocs) x));
  lemma_export_preserves_prref = (fun x hocs ->
    match x with | Inl x -> c1.lemma_export_preserves_prref x (left hocs)| Inr x -> c2.lemma_export_preserves_prref x (right hocs))
}

instance exportable_resexn a3p t st {| c:exportable_from a3p t st |} : exportable_from a3p (resexn t) (EmptyNode st Leaf) =
  exportable_sum a3p t st #c err Leaf #(exportable_err a3p)

instance exportable_pair a3p t1 st1 {| c1:exportable_from a3p t1 st1 |} t2 st2 {| c2:exportable_from a3p t2 st2 |} : exportable_from a3p (t1 * t2) (EmptyNode st1 st2) = {
  c_styp = witnessable_pair t1 #c1.c_styp t2 #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = poly_iface_pair _ _ #c1.c_ityp _ #c2.c_ityp;
  export = (fun hocs (x1, x2) -> (c1.export (left hocs) x1, c2.export (right hocs) x2));
  lemma_export_preserves_prref = (fun (x1, x2) hocs -> c1.lemma_export_preserves_prref x1 (left hocs); c2.lemma_export_preserves_prref x2 (right hocs))
}

instance exportable_ref a3p t {| c:tc_shareable_type t |} : exportable_from a3p (ref t) Leaf = {
  c_styp = witnessable_ref t #solve;
  ityp = ref t;
  c_ityp = poly_iface_ref a3p t #c;
  export = (fun Leaf x -> x);
  lemma_export_preserves_prref = (fun _ _ -> ());
}

instance exportable_llist a3p t {| c:tc_shareable_type t |} :
  exportable_from a3p (linkedList t) Leaf = {
  c_styp = solve ;
  ityp = linkedList t ;
  c_ityp = solve ;
  export = (fun Leaf x -> x) ;
  lemma_export_preserves_prref = (fun _ _ -> ())
}

instance exportable_refinement a3p t st {| c:exportable_from a3p t st |} (p:t->Type0) : exportable_from a3p (x:t{p x}) st = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  export = (fun hocs x -> c.export hocs x);
  lemma_export_preserves_prref = (fun x -> c.lemma_export_preserves_prref x);
}

instance exportable_arrow_err00
  a3p
  (t1:Type u#0) 
  st1
  {| c1:importable_to a3p t1 st1 |}
  (t2:Type u#0)
  st2
  {| c2:exportable_from a3p t2 st2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
  : exportable_from a3p (x:t1 -> ST (resexn t2) (pre x) (post x)) (Node (U00 (Spec true true t1 c1.c_styp pre t2 c2.c_styp post)) st1 st2) = 
  mk_exportable
    (witnessable_arrow t1 (resexn t2) pre post)
    (poly_iface_arrow a3p _ #c1.c_ityp _ #(poly_iface_resexn a3p c2.ityp #c2.c_ityp))
    (fun hocs f (x:c1.ityp) ->
      let Node (| _, U00hoc (EnforcePre check c_post) |) lhs rhs = hocs in
      match c1.import lhs x with
      | Inr err -> Inr err
      | Inl x' -> begin
        c1.lemma_import_preserves_prref x lhs;
        let (| _, cb_check |) = check x' in
        match cb_check () with
        | Inr err -> Inr err
        | Inl _ -> begin
          let res : resexn t2 = f x' in
          c_post x' res;
          (exportable_resexn a3p t2 st2).lemma_export_preserves_prref res (EmptyNode rhs Leaf);
          (exportable_resexn a3p t2 st2).export (EmptyNode rhs Leaf) res
        end
      end)
    (fun _ _ -> ())

instance exportable_arrow_err10
  a3p
  (t1:Type u#1) 
  st1
  {| c1:importable_to a3p t1 st1 |}
  (t2:Type u#0)
  st2
  {| c2:exportable_from a3p t2 st2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
  : exportable_from a3p (x:t1 -> ST (resexn t2) (pre x) (post x)) (Node (U10 (Spec true true t1 c1.c_styp pre t2 c2.c_styp post)) st1 st2) =
  mk_exportable
    (witnessable_arrow t1 (resexn t2) pre post)
    (poly_iface_arrow a3p _ #c1.c_ityp _ #(poly_iface_resexn a3p c2.ityp #c2.c_ityp))
    (fun hocs f (x:c1.ityp) ->
      let Node (| _, U10hoc (EnforcePre check c_post) |) lhs rhs = hocs in
      match c1.import lhs x with
      | Inr err -> Inr err
      | Inl x' -> begin
        c1.lemma_import_preserves_prref x lhs;
        let (| _, cb_check |) = check x' in
        match cb_check () with
        | Inr err -> Inr err
        | Inl _ -> begin
          let res : resexn t2 = f x' in
          c_post x' res;
          (exportable_resexn a3p t2 st2).lemma_export_preserves_prref res (EmptyNode rhs Leaf);
          (exportable_resexn a3p t2 st2).export (EmptyNode rhs Leaf) res
        end
      end)
    (fun _ _ -> ())

instance exportable_arrow00
  a3p
  (t1:Type u#0) 
  st1
  {| c1:safe_importable_to a3p t1 st1 |}
  (t2:Type u#0)
  st2
  {| c2:exportable_from a3p t2 st2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
  : exportable_from a3p (x:t1 -> ST t2 (pre x) (post x)) (Node (U00 (Spec true false t1 c1.c_styp pre t2 c2.c_styp post)) st1 st2) =
  mk_exportable
    (witnessable_arrow t1 t2 pre post)
    (poly_iface_arrow a3p _ #c1.c_ityp _ #c2.c_ityp)
    (fun hocs f (x:c1.ityp) ->
      let Node (| _, U00hoc (TrivialPre c_pre c_post) |) lhs rhs = hocs in
      let x' = c1.safe_import lhs x in
      c_pre x';
      c1.lemma_safe_import_preserves_prref x lhs;
      let res : t2 = f x' in
      c_post x' res;
      assert (forall h0 h1. post x' h0 res h1 ==> post_poly_arrow a3p #t2 #c2.c_styp h0 res h1) by (()); (** weird **)
      c2.lemma_export_preserves_prref res rhs;
      c2.export rhs res
    )
    (fun _ _ -> ())


(** Importable instances **)
instance poly_iface_is_safely_importable a3p t {| c1:poly_iface a3p t |} : safe_importable_to a3p t Leaf = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  safe_import = (fun Leaf x -> x);
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}

instance safe_importable_is_importable a3p t st {| c1:safe_importable_to a3p t st |} : importable_to a3p t st = {
  c_styp = c1.c_styp;
  ityp = c1.ityp;
  c_ityp = c1.c_ityp;
  import = (fun x hocs -> Inl (c1.safe_import x hocs));
  lemma_import_preserves_prref = (fun x -> c1.lemma_safe_import_preserves_prref x);
}

instance safe_importable_unit a3p : safe_importable_to a3p unit Leaf = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = poly_iface_unit a3p;
  safe_import = (fun Leaf x -> x);
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}

instance safe_importable_err a3p : safe_importable_to a3p err Leaf = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = poly_iface_err _;
  safe_import = (fun Leaf x -> x);
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}

instance importable_option a3p t st {| c:importable_to a3p t st |} : importable_to a3p (option t) st = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = poly_iface_option a3p c.ityp #c.c_ityp;
  import = (fun hocs x ->
    match x with
    | Some x -> begin
      match c.import hocs x with
      | Inl x -> Inl (Some x)
      | Inr err -> Inr err
    end
    | None -> Inl None);
  lemma_import_preserves_prref = (fun x hocs ->
    match x with
    | Some x -> c.lemma_import_preserves_prref x hocs
    | None -> ())
}

instance importable_sum a3p t1 st1 {| c1:importable_to a3p t1 st1 |} t2 st2 {| c2:importable_to a3p t2 st2 |} : importable_to a3p (either t1 t2) (EmptyNode st1 st2) = {
  c_styp = witnessable_sum t1 #c1.c_styp t2 #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = poly_iface_sum a3p _ #c1.c_ityp _ #c2.c_ityp;
  import = (fun hocs x ->
    match x with
    | Inl x -> begin
      match c1.import (left hocs) x with
      | Inl x -> Inl (Inl x)
      | Inr err -> Inr err
    end
    | Inr x -> begin
      match c2.import (right hocs) x with
      | Inl x -> Inl (Inr x)
      | Inr err -> Inr err
    end);
  lemma_import_preserves_prref = (fun x hocs ->
    match x with
    | Inl x -> c1.lemma_import_preserves_prref x (left hocs)
    | Inr x -> c2.lemma_import_preserves_prref x (right hocs))
}

instance importable_pair a3p t1 st1 {| c1:importable_to a3p t1 st1 |} t2 st2 {| c2:importable_to a3p t2 st2 |} : importable_to a3p (t1 * t2) (EmptyNode st1 st2) = {
  c_styp = witnessable_pair t1 #c1.c_styp t2 #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = poly_iface_pair a3p _ #c1.c_ityp _ #c2.c_ityp;
  import = (fun hocs (x, x') ->
    match c1.import (left hocs) x with
    | Inl x -> begin
      match c2.import (right hocs) x' with
      | Inl x' -> Inl (x,x')
      | Inr err -> Inr err
    end
    | Inr err -> Inr err);
  lemma_import_preserves_prref = (fun x hocs ->
    c1.lemma_import_preserves_prref (fst x) (left hocs);
    c2.lemma_import_preserves_prref (snd x) (right hocs))
}

instance safe_importable_ref a3p t {| c:tc_shareable_type t |} : safe_importable_to a3p (ref t) Leaf = {
  c_styp = witnessable_mref t _ #solve;
  ityp = ref t;
  c_ityp = poly_iface_ref _ t;
  safe_import = (fun Leaf x -> x);
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}

instance import_refinement a3p t st {| c:importable_to a3p t st |} (p:t->Type0) (check:(x:t -> r:bool{r ==> p x})): importable_to a3p (x:t{p x}) st = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  import = (fun hocs x ->
    match (c.import hocs x) with
    | Inl x -> if check x then Inl x else Inr (Contract_failure "check of refinement failed")
    | Inr err -> Inr err);
  lemma_import_preserves_prref = (fun x -> c.lemma_import_preserves_prref x);
}

instance safe_importable_resexn a3p t st {| c:importable_to a3p t st |} : safe_importable_to a3p (resexn t) (EmptyNode st Leaf)= {
  c_styp = witnessable_sum t #c.c_styp err;
  ityp = resexn c.ityp;
  c_ityp = poly_iface_resexn a3p c.ityp #c.c_ityp;
  safe_import = (fun hocs x ->
    match x with
    | Inl x -> begin
      match c.import (left hocs) x with
      | Inl x -> Inl x
      | Inr err -> Inr err
    end
    | Inr err -> Inr err
    );
  lemma_safe_import_preserves_prref = (fun x hocs ->
    match x with
    | Inl x -> c.lemma_import_preserves_prref x (left hocs)
    | Inr err -> ())
}

instance safe_importable_arrow_err00
  a3p
  (t1:Type u#0)
  st1
  {| c1:exportable_from a3p t1 st1 |}
  (t2:Type u#0)
  st2
  {| c2:importable_to a3p t2 st2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
  : safe_importable_to a3p (x:t1 -> ST (resexn t2) (pre x) (post x)) (Node (U00 (Spec false true t1 c1.c_styp pre t2 c2.c_styp post)) st1 st2) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_resexn c2.ityp #c2.c_ityp.wt);
  c_ityp = poly_iface_arrow a3p c1.ityp #c1.c_ityp (resexn c2.ityp) #(poly_iface_resexn a3p c2.ityp #c2.c_ityp);
  safe_import = (fun hocs (f:mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp #c2.c_ityp.wt err)) (x:t1) ->
    let Node (| _, U00hoc (EnforcePost c_pre c_post check) |) lhs rhs = hocs in
    c_pre x;
    c1.lemma_export_preserves_prref x lhs;
    let (| _, cb_check |) = check x in
    let x' = c1.export lhs x in
    let res : resexn c2.ityp = f x' in
    let fres = (safe_importable_resexn a3p t2 st2).safe_import (EmptyNode rhs Leaf) res in
    (safe_importable_resexn a3p t2 st2).lemma_safe_import_preserves_prref res (EmptyNode rhs Leaf);
    match cb_check fres with
    | Inl _ -> fres
    | Inr err -> (c_post x err; (Inr err))
  );
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}

instance safe_importable_arrow00
  a3p
  (t1:Type u#0)
  st1
  {| c1:exportable_from a3p t1 st1 |}
  (t2:Type u#0)
  st2
  {| c2:safe_importable_to a3p t2 st2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
  : safe_importable_to a3p (x:t1 -> ST t2 (pre x) (post x)) (Node (U00 (Spec false false t1 c1.c_styp pre t2 c2.c_styp post)) st1 st2) = {
  c_styp = witnessable_arrow t1 t2 pre post;
  ityp = mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt c2.ityp #c2.c_ityp.wt;
  c_ityp = poly_iface_arrow a3p c1.ityp #c1.c_ityp c2.ityp #c2.c_ityp;
  safe_import = (fun hocs f (x:t1) ->
    let Node (| _, U00hoc (TrivialPost c_pre c_post) |) lhs rhs = hocs in
    c_pre x;
    c1.lemma_export_preserves_prref x lhs;
    let x' = c1.export lhs x in
    let res : c2.ityp = f x' in
    let fres = c2.safe_import rhs res in
    c_post x fres;
    c2.lemma_safe_import_preserves_prref res rhs;
    fres
  );
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}

instance safe_importable_arrow10
  a3p
  (t1:Type u#1) 
  st1
  {| c1:exportable_from a3p t1 st1 |}
  (t2:Type u#0)
  st2
  {| c2:safe_importable_to a3p t2 st2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
  : safe_importable_to a3p (x:t1 -> ST t2 (pre x) (post x)) (Node (U10 (Spec false false t1 c1.c_styp pre t2 c2.c_styp post)) st1 st2) = {
  c_styp = witnessable_arrow t1 t2 pre post;
  ityp = mk_poly_arrow a3p c1.ityp #c1.c_ityp.wt c2.ityp #c2.c_ityp.wt;
  c_ityp = poly_iface_arrow a3p c1.ityp #c1.c_ityp c2.ityp #c2.c_ityp;
  safe_import = (fun hocs f (x:t1) ->
    let Node (| _, U10hoc (TrivialPost c_pre c_post) |) lhs rhs = hocs in
    c_pre x;
    c1.lemma_export_preserves_prref x lhs;
    let x' = c1.export lhs x in
    let res : c2.ityp = f x' in
    let fres = c2.safe_import rhs res in
    c_post x fres;
    c2.lemma_safe_import_preserves_prref res rhs;
    fres
  );
  lemma_safe_import_preserves_prref = (fun _ _ -> ())
}