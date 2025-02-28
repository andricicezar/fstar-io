From iris.program_logic Require Export atomic.
From iris.heap_lang Require Export primitive_laws notation proofmode.
From iris.base_logic.lib Require Import token.
From iris.base_logic Require Import invariants.

(** Written by Léon Ducruet **)

Context `{!heapGS Σ}.

Definition cb_spec (cb : val) (r r₁ : loc) : iProp Σ :=
  ∀ (r' : loc) v v',
  {{{ r ↦ #r' ∗ r' ↦ v ∗ r₁ ↦ v' }}}
    cb #()
  {{{ RET #(); True }}}.

Definition lib_spec (lib : val) (r r' : loc) (v : val) : iProp Σ :=
  {{{ r ↦ #r' ∗ r' ↦ v }}}
    lib #r
  {{{ (cb : val) (r'' : loc) v' v'', RET cb; cb_spec cb r r' ∗ r ↦ #r'' ∗ r' ↦ v' ∗ (r'' ↦ v'' ∨ ⌜r'' = r'⌝) }}}.

Definition lib : val :=
  λ: "r",
  let: "g" := ref #0 in
  (λ: <>, "g" <- !"g" + #1).

Lemma lib_spec_lib : (** to call the lib, one would need to know r' in advance **)
  ∀ (r r' : loc) (v : val),
  {{{ r ↦ #r' ∗ r' ↦ v }}}
    lib #r
  {{{ (cb : val) (r'' : loc) v' v'', RET cb; cb_spec cb r r' ∗ r ↦ #r'' ∗ r' ↦ v' ∗ (r'' ↦ v'' ∨ ⌜r'' = r'⌝) }}}.
Proof.
  iIntros (r r' v Φ) "(r & r') HΦ".
  rewrite/lib. wp_pures.
  wp_alloc g as "g". wp_pures.
  iApply "HΦ". iFrame "r r'".
  iSplitL; last by iRight.
  rewrite /cb_spec.
  clear.
  iMod (inv_alloc nroot ⊤ (∃ i : Z, g ↦ #i)%I with "[$g]") as "#inv".
  iIntros "!>" (r'' v v' Φ) "!>(r & r'' & r') HΦ".
  wp_pures. wp_bind (Load _). iInv "inv" as "(%i & g)".
  wp_load. iSplitL "g". { by iFrame. }
  iModIntro. wp_pures. iInv "inv" as "(%j & g)".
  wp_store. iFrame. by iApply "HΦ".
  Unshelve. apply inhabitant.
Qed.