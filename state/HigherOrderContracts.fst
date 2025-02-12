module HigherOrderContracts

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs

open Witnessable
open TargetLang

type err =
| Contract_failure : string -> err

instance witnessable_err : witnessable err = {
  satisfy = (fun _ _ -> True);
  satisfy_on_heap = (fun _ _ _ -> True);
  satisfy_on_heap_monotonic = (fun _ _ _ _ -> ());
  pwitness = (fun _ _ -> (fun () -> ()));
}

instance targetlang_err : targetlang default_spec err = {
  wt = witnessable_err
}

type resexn a = either a err

class exportable_from (styp: Type u#a) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang default_spec ityp;
  [@@@no_method] export : styp -> ityp;
  [@@@no_method] lemma_export_preserves_prref : x:styp -> Lemma (requires (c_styp.satisfy x (Mktuple3?._2 default_spec))) (ensures (c_ityp.wt.satisfy (export x) (Mktuple3?._2 default_spec)))
}

class safe_importable_to (styp: Type u#a) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang default_spec ityp;
  [@@@no_method] safe_import : ityp -> styp;
  [@@@no_method] lemma_safe_import_preserves_prref : x:ityp -> Lemma (requires (c_ityp.wt.satisfy x (Mktuple3?._2 default_spec))) (ensures (c_styp.satisfy (safe_import x) (Mktuple3?._2 default_spec)))
}

class importable_to (styp: Type u#a) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang default_spec ityp;
  [@@@no_method] import : ityp -> resexn styp;
  [@@@no_method] lemma_import_preserves_prref : x:ityp -> Lemma (requires (c_ityp.wt.satisfy x (Mktuple3?._2 default_spec))) (ensures ((witnessable_sum styp err).satisfy (import x) (Mktuple3?._2 default_spec)))
}

(** Exportable instances **)
instance targetlang_is_exportable t {| c1:targetlang default_spec t |} : exportable_from t = {
  c_styp = c1.wt; 
  ityp = t; 
  c_ityp = solve; 
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ()) }

instance exportable_unit : exportable_from unit = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = solve;
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ())
}

instance exportable_err : exportable_from err = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = solve;
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ())
}

instance exportable_int : exportable_from int = {
  c_styp = witnessable_int;
  ityp = int;
  c_ityp = solve;
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ())
}

instance exportable_option t {| c:exportable_from t |} : exportable_from (option t) = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = targetlang_option default_spec c.ityp #c.c_ityp;
  export = (fun x -> match x with | Some x -> Some (c.export x) | FStar.Pervasives.Native.None -> FStar.Pervasives.Native.None);
  lemma_export_preserves_prref = (fun x -> match x with | Some x -> c.lemma_export_preserves_prref x | FStar.Pervasives.Native.None -> ())
}

instance exportable_sum t1 t2 {| c1:exportable_from t1 |} {| c2:exportable_from t2 |} : exportable_from (either t1 t2) = {
  c_styp = witnessable_sum t1 t2 #c1.c_styp #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = targetlang_sum default_spec _ _ #c1.c_ityp #c2.c_ityp;
  export = (fun x -> match x with | Inl x -> Inl (c1.export x) | Inr x -> Inr (c2.export x));
  lemma_export_preserves_prref = (fun x -> 
    match x with | Inl x -> c1.lemma_export_preserves_prref x | Inr x -> c2.lemma_export_preserves_prref x)
}

instance exportable_resexn t {| c:exportable_from t |} : exportable_from (resexn t) = {
  c_styp = witnessable_sum t err #c.c_styp;
  ityp = resexn c.ityp;
  c_ityp = targetlang_sum default_spec c.ityp err #c.c_ityp;
  export = (fun x -> match x with | Inl x -> Inl (c.export x) | Inr err -> Inr err);
  lemma_export_preserves_prref = (fun x -> match x with | Inl x -> c.lemma_export_preserves_prref x | Inr err -> ())
}

instance exportable_pair t1 t2 {| c1:exportable_from t1 |} {| c2:exportable_from t2 |} : exportable_from (t1 * t2) = {
  c_styp = witnessable_pair t1 t2 #c1.c_styp #c2.c_styp;
  ityp = c1.ityp * c2.ityp;
  c_ityp = targetlang_pair default_spec _ _ #c1.c_ityp #c2.c_ityp;
  export = (fun (x1, x2) -> (c1.export x1, c2.export x2));
  lemma_export_preserves_prref = (fun (x1, x2) -> c1.lemma_export_preserves_prref x1; c2.lemma_export_preserves_prref x2)
}

instance exportable_ref t {| c:targetlang default_spec t |} : exportable_from (ref t) = {
  c_styp = witnessable_mref t _ #c.wt;
  ityp = ref t;
  c_ityp = solve;
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ());
}

instance exportable_llist t {| c:exportable_from t |} : exportable_from (linkedList t) = admit ()

instance exportable_refinement t {| c:exportable_from t |} (p:t->Type0) (check:(x:t -> r:bool{r ==> p x})): exportable_from (x:t{p x}) = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  export = (fun x -> c.export x);
  lemma_export_preserves_prref = (fun x -> c.lemma_export_preserves_prref x);
}

instance exportable_arrow 
  (t1:Type) (t2:Type)
  {| c1:importable_to t1 |}
  {| c2:exportable_from t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
  (_:squash (forall x h0 r h1. post x h0 r h1 ==> post_targetlang_arrow default_spec #(resexn t2) #(witnessable_sum t2 err #c2.c_styp) h0 r h1))
  (check:(x:t1 -> ST (either unit err) All (pre_targetlang_arrow default_spec #_ #c1.c_styp x) (fun h0 r h1 -> h0==h1 /\ (Inl? r ==> pre x h0)))) 
                             (** ^ the fact that the check has a pre-condition means that the check does not have to enforce it
                                 e.g., the invariant on the heap **)
  : exportable_from (x:t1 -> ST (resexn t2) All (pre x) (post x)) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_targetlang_arrow default_spec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp err #c2.c_ityp.wt);
  c_ityp = targetlang_arrow default_spec c1.ityp (resexn c2.ityp) #_ #(targetlang_sum default_spec c2.ityp err) ;
  export = (fun (f:(x:t1 -> ST (resexn t2) All (pre x) (post x))) (x:c1.ityp) ->
    match c1.import x with
    | Inl x' -> begin
      c1.lemma_import_preserves_prref x;
      match check x' with
      | Inl _ -> begin
        let res = f x' in
        (exportable_resexn t2).lemma_export_preserves_prref res;
        (exportable_resexn t2).export res
      end
      | Inr err -> Inr err
    end
    | Inr err -> Inr err
  );
  lemma_export_preserves_prref = (fun _  -> ());
}

(** Importable instances **)
instance targetlang_is_safely_importable t {| c1:targetlang default_spec t |} : safe_importable_to t = {
  c_styp = c1.wt;
  ityp = t;
  c_ityp = solve;
  safe_import = (fun x -> x);
  lemma_safe_import_preserves_prref = (fun _ -> ())
}

instance safe_importable_is_importable t {| c1:safe_importable_to t |} : importable_to t = {
  c_styp = c1.c_styp;
  ityp = c1.ityp;
  c_ityp = c1.c_ityp;
  import = (fun x -> Inl (c1.safe_import x));
  lemma_import_preserves_prref = (fun x -> c1.lemma_safe_import_preserves_prref x);
}

instance safe_importable_unit : safe_importable_to unit = {
  c_styp = witnessable_unit;
  ityp = unit;
  c_ityp = solve;
  safe_import = (fun x -> x);
  lemma_safe_import_preserves_prref = (fun _ -> ())
}

instance safe_importable_err : safe_importable_to err = {
  c_styp = witnessable_err;
  ityp = err;
  c_ityp = solve;
  safe_import = (fun x -> x);
  lemma_safe_import_preserves_prref = (fun _ -> ())
}

instance importable_option t {| c:importable_to t |} : importable_to (option t) = {
  c_styp = witnessable_option t #c.c_styp;
  ityp = option c.ityp;
  c_ityp = targetlang_option default_spec c.ityp #c.c_ityp;
  import = (fun x -> 
    match x with 
    | Some x -> begin
      match c.import x with
      | Inl x -> Inl (Some x)
      | Inr err -> Inr err
    end 
    | FStar.Pervasives.Native.None -> Inl FStar.Pervasives.Native.None);
  lemma_import_preserves_prref = (fun x -> 
    match x with 
    | Some x -> c.lemma_import_preserves_prref x
    | FStar.Pervasives.Native.None -> ())
}

instance importable_sum t1 t2 {| c1:importable_to t1 |} {| c2:importable_to t2 |} : importable_to (either t1 t2) = {
  c_styp = witnessable_sum t1 t2 #c1.c_styp #c2.c_styp;
  ityp = either c1.ityp c2.ityp;
  c_ityp = targetlang_sum default_spec _ _ #c1.c_ityp #c2.c_ityp;
  import = (fun x -> 
    match x with 
    | Inl x -> begin
      match c1.import x with
      | Inl x -> Inl (Inl x)
      | Inr err -> Inr err
    end 
    | Inr x -> begin
      match c2.import x with
      | Inl x -> Inl (Inr x)
      | Inr err -> Inr err
    end);
  lemma_import_preserves_prref = (fun x -> 
    match x with 
    | Inl x -> c1.lemma_import_preserves_prref x
    | Inr x -> c2.lemma_import_preserves_prref x)
}

instance safe_importable_ref t {| c:targetlang default_spec t |} : safe_importable_to (ref t) = {
  c_styp = witnessable_mref t _ #c.wt;
  ityp = ref t;
  c_ityp = solve;
  safe_import = (fun x -> x);
  lemma_safe_import_preserves_prref = (fun _ -> ())
}

instance importable_llits t {| c:importable_to t |} : importable_to (linkedList t) = admit ()

instance import_refinement t {| c:importable_to t |} (p:t->Type0) (check:(x:t -> r:bool{r ==> p x})): importable_to (x:t{p x}) = {
  c_styp = witnessable_refinement t #c.c_styp p;
  ityp = c.ityp;
  c_ityp = c.c_ityp;
  import = (fun x -> 
    match (c.import x) with
    | Inl x -> if check x then Inl x else Inr (Contract_failure "check of refinement failed")
    | Inr err -> Inr err);
  lemma_import_preserves_prref = (fun x -> c.lemma_import_preserves_prref x);
}

instance safe_importable_resexn t {| c:importable_to t |} : safe_importable_to (resexn t) = {
  c_styp = witnessable_sum t err #c.c_styp;
  ityp = resexn c.ityp;
  c_ityp = targetlang_sum default_spec c.ityp err #c.c_ityp;
  safe_import = (fun x ->
    match x with
    | Inl x -> begin
      match c.import x with
      | Inl x -> Inl x
      | Inr err -> Inr err
    end
    | Inr err -> Inr err
    );
  lemma_safe_import_preserves_prref = (fun x ->
    match x with
    | Inl x -> c.lemma_import_preserves_prref x
    | Inr err -> ())
}

type cb_capture_check (t1:Type) (t2:Type) {| c2: witnessable t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0)))
  (x:t1)
  (eh0:FStar.Ghost.erased heap{pre x eh0}) =
  (r:t2 -> ST (resexn unit) All (fun h1 -> post_targetlang_arrow default_spec eh0 r h1) (fun h1 rck h1' -> 
    h1 == h1' /\ (Inl? rck ==> post x eh0 r h1)))

type capture_check
  (t1:Type) (t2:Type) {| c2: witnessable t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' t2 (pre x h0))) =
  x:t1 -> ST (
    eh0:FStar.Ghost.erased heap{pre x eh0} & cb_capture_check t1 t2 #c2 pre post x eh0
  ) All (pre x) (fun h0 r h1 -> FStar.Ghost.reveal (dfst r) == h0 /\ h0 == h1)

instance safe_importable_arrow 
  (t1:Type) (t2:Type)
  {| c1:exportable_from t1 |}
  {| c2:importable_to t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
  (_:squash (forall (x:t1) h0. pre x h0 ==> pre_targetlang_arrow default_spec #_ #c1.c_styp x h0))
  (_:squash (forall (x:t1) h0 e h1. pre x h0 /\ post_targetlang_arrow default_spec #_ #(witnessable_sum t2 err #c2.c_styp) h0 (Inr e) h1 ==> post x h0 (Inr e) h1))
  (capture_check:capture_check t1 (resexn t2) #(witnessable_sum _ err #c2.c_styp) pre post)
  : safe_importable_to (x:t1 -> ST (resexn t2) All (pre x) (post x)) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_targetlang_arrow default_spec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp err #c2.c_ityp.wt);
  c_ityp = targetlang_arrow default_spec c1.ityp (resexn c2.ityp) #_ #(targetlang_sum default_spec c2.ityp err #c2.c_ityp);
  safe_import = (fun (f:mk_targetlang_arrow default_spec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp err #c2.c_ityp.wt)) (x:t1) ->
    c1.lemma_export_preserves_prref x;
    let (| _, check |) = capture_check x in
    let x' = c1.export x in
    let res : resexn c2.ityp = f x' in
    let fres = (safe_importable_resexn t2).safe_import res in
    (safe_importable_resexn t2).lemma_safe_import_preserves_prref res;
    match check fres with
    | Inl _ -> fres
    | Inr err -> Inr err
  );
  lemma_safe_import_preserves_prref = (fun _ -> ())
}

type f_eqx = x:ref int -> SST (resexn unit) (requires (fun h0 -> satisfy x (Mktuple3?._2 default_spec))) (ensures (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x))

let f_eqx_is_safe_importable : safe_importable_to f_eqx =
  safe_importable_arrow 
    (ref int) unit
    (fun x -> sst_pre (fun h0 -> satisfy x (Mktuple3?._2 default_spec))) 
    (fun x -> sst_post _ _ (fun h0 r h1 -> Inr? r \/ sel h0 x == sel h1 x)) 
    ()
    ()
    (fun (rx:ref int) ->
      recall (contains_pred rx);
      let x = sst_read' rx in
      let eh0 = get_heap () in
      let check : cb_capture_check (ref int) (resexn unit) _ _ rx eh0 = 
        (fun res -> if x = sst_read rx then Inl () else Inr (Contract_failure "x has changed")) in
      (| eh0, check |))

val unsafe_f : mk_targetlang_arrow default_spec (ref int) (resexn unit)
let unsafe_f x = 
  recall (contains_pred x);
  recall (is_shared x);
  sst_write x 0;
  Inl ()

let safe_f = f_eqx_is_safe_importable.safe_import unsafe_f

type f_xeq5 = x:ref int -> SST (resexn int) (requires (fun h0 -> sel h0 x == 5 /\ satisfy x (Mktuple3?._2 default_spec))) (ensures (fun h0 r h1 -> (Inr? r \/ (Inl? r /\ Inl?.v r == 2)) /\ ((Mktuple3?._3 default_spec) h0 h1)))
  
let f_xeq5_is_exportable : exportable_from f_xeq5 =
  exportable_arrow 
    (ref int) int
    (fun x -> sst_pre (fun h0 -> sel h0 x == 5 /\ satisfy x (Mktuple3?._2 default_spec))) 
    (fun x -> sst_post (resexn int) _ (fun h0 r h1 -> (Inr? r \/ (Inl? r /\ Inl?.v r == 2)) /\ ((Mktuple3?._3 default_spec) h0 h1)))
    ()
    (fun x ->
      recall (contains_pred x);
      if sst_read x = 5 then Inl ()
      else Inr (Contract_failure "x is not equal to 5"))

val f_with_pre : f_xeq5
let f_with_pre x = 
  recall (contains_pred x);
  let v = sst_read' x in
  assert (v == 5);
  Inl (10 / v)

let f_with_dc = f_xeq5_is_exportable.export f_with_pre
