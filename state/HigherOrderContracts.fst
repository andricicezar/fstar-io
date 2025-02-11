module HigherOrderContracts

open FStar.Tactics
open FStar.Tactics.Typeclasses

open SharedRefs

open Witnessable
open TargetLang

type resexn a = either a unit

class exportable_from (styp: Type u#a) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang default_spec ityp;
  [@@@no_method] export : styp -> ityp;
  [@@@no_method] lemma_export_preserves_prref : x:styp -> Lemma (requires (c_styp.satisfy x (Mktuple3?._2 default_spec))) (ensures (c_ityp.wt.satisfy (export x) (Mktuple3?._2 default_spec)))
}

class safe_importable_to (styp: Type u#a) = {
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang default_spec ityp;
  [@@@no_method] import : ityp -> styp;
}

class importable_to (styp: Type u#a) = {
  [@@@no_method] c_styp : witnessable styp;
  [@@@no_method] ityp : Type u#b;
  [@@@no_method] c_ityp : targetlang default_spec ityp;
  [@@@no_method] import : ityp -> resexn styp;
}

(** Exportable instances **)
instance targetlang_is_exportable t {| c1:targetlang default_spec t |} : exportable_from t = {
  c_styp = c1.wt; 
  ityp = t; 
  c_ityp = solve; 
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ()) }

instance exportable_unit : exportable_from unit = admit ()
instance exportable_sum t1 t2 {| c1:exportable_from t1 |} {| c2:exportable_from t2 |} : exportable_from (either t1 t2) = admit ()

instance exportable_ref t {| c:targetlang default_spec t |} : exportable_from (ref t) = {
  c_styp = witnessable_mref t _ #c.wt;
  ityp = ref t;
  c_ityp = solve;
  export = (fun x -> x);
  lemma_export_preserves_prref = (fun _ -> ())
}

instance exportable_arrow 
  (t1:Type) (t2:Type)
  {| c1:importable_to t1 |}
  {| c2:exportable_from t2 |}
  (pre:(t1 -> st_pre))
  (post:(x:t1 -> h0:heap -> st_post' (resexn t2) (pre x h0)))
  (_:squash (forall x h0 r h1. post x h0 r h1 ==>  post_targetlang_arrow default_spec #(resexn t2) #(witnessable_sum t2 unit #c2.c_styp) h0 r h1))
  (check:(x:t1 -> ST bool All (fun h0 -> (Mktuple3?._1 default_spec) h0) (fun h0 r h1 -> h0==h1 /\ (r ==> pre x h0)))) 
                             (** ^ the fact that the check has a pre-condition means that the check does not have to enforce it
                                 e.g., the invariant on the heap **)
  : exportable_from (x:t1 -> ST (resexn t2) All (pre x) (post x)) = {
  c_styp = witnessable_arrow t1 (resexn t2) pre post;
  ityp = mk_targetlang_arrow default_spec c1.ityp #c1.c_ityp.wt (resexn c2.ityp) #(witnessable_sum c2.ityp unit #c2.c_ityp.wt);
  c_ityp = targetlang_arrow default_spec c1.ityp (resexn c2.ityp) #_ #(targetlang_sum default_spec c2.ityp unit) ;
  export = (fun (f:(x:t1 -> ST (resexn t2) All (pre x) (post x))) (x:c1.ityp) ->
    match c1.import x with
    | Inl x -> begin
      if check x then begin
        match f x with
        | Inl r -> begin
          c2.lemma_export_preserves_prref r; (** the squash + this lemma imply the post-condition **)
          Inl (c2.export r)
        end
        | Inr unit -> Inr unit
      end
      else Inr ()
    end
    | Inr () -> Inr ()
  );
  lemma_export_preserves_prref = (fun _  -> ());
}
(** Importable instances **)
