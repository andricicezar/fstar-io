module RQ.SigeltAttrs

(** Postulated transport lemma: [set_sigelt_attrs] / [set_sigelt_quals] only
    modify sigelt metadata fields that are NOT exposed by [inspect_sigelt]
    (see FStar.Stubs.Reflection.V2.Builtins.fsti: [sigelt_view] carries
    neither attrs nor qualifiers). Therefore they preserve [sigelt_typing]
    and [sigelt_has_type], which are defined purely via [pack_sigelt] /
    [inspect_sigelt].

    F*'s stdlib does not expose this axiom. We postulate it here in an
    interface-only module so attaching [opaque_to_smt] / [Irreducible] to a
    checked splice does not force re-typechecking or SMT encoding of the
    derivation body. **)

open FStar.Reflection.Typing
open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Stubs.Reflection.V2.Builtins

val sigelt_typing_preserves
  (g:env) (se:sigelt) (ty:option typ)
  (attrs:list term) (quals:list qualifier)
  : Lemma
    (requires sigelt_typing g se /\ sigelt_has_type se ty)
    (ensures (let se' = set_sigelt_quals quals (set_sigelt_attrs attrs se) in
              sigelt_typing g se' /\ sigelt_has_type se' ty))
