module CriteriaStatic.STLC
module STLC = STLC

(** *** Intrinsic criteria, static quoting/unquoting  **)
type set_prop = nat -> Type0
let (⊆) (s0 s1:set_prop) : Type0 = forall res. s0 res ==> s1 res
let (≡) (s0 s1:set_prop) : Type0 = forall res. s0 res <==> s1 res

noeq type intS = { 
  ct_stlc : STLC.typ;
  // p_post : set_prop
}

type progS (i:intS) = STLC.elab_typ i.ct_stlc -> Tot nat
type ctxS (i:intS) = STLC.elab_typ i.ct_stlc
type wholeS = (unit -> Tot nat)

let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (fun () -> ps cs)

val behS : wholeS -> set_prop
let behS ws = fun x -> ws () == x

(** Target **)

noeq type intT = { ct : STLC.typ }

val comp_int : intS -> intT
let comp_int i = { ct = i.ct_stlc }

type progT (i:intT) = pt:STLC.exp & STLC.typing STLC.empty pt (STLC.TArr i.ct STLC.TNat)
type ctxT (i:intT) = ct:STLC.exp & STLC.typing STLC.empty ct i.ct
type wholeT = wt:STLC.exp & STLC.typing STLC.empty wt (STLC.TArr STLC.TUnit STLC.TNat)

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT = 
  let (| _, htp |) = pt in
  let (| _, htc |) = ct in
  STLC.thunk_exp (STLC.TyApp htp htc)

val behT : wt:wholeT -> set_prop 
let behT (| ew, htw |) = fun x -> STLC.sem (STLC.TyApp htw STLC.TyUnit) == x

(** Compiler correctness **)

open FStar.Tactics.V2
open FStar.Reflection.V2
open FStar.Reflection.Typing
let mk_squash (phi:term) : Tot term = pack_ln (Tv_App (`squash) (phi, Q_Explicit))

let t_unit = `()

let valid (g:env) (phi:term) : prop =
  squash (tot_typing g t_unit (mk_squash phi))

let cc (ws:wholeS) (wt:wholeT) =
  behS ws ≡ behT wt

val compile_whole_stat : 
  (g:env) ->
  (ws:term{tot_typing g ws (`wholeS)}) ->
  Tac (wt:term{
    tot_typing g wt (`wholeT) /\
    (** compiler correctness **)
    valid g (`(cc (`#ws) (`#wt)))
    (** soundness **)
    // in this PoC, we cannot type this because whole programs do not have an interface
    // valid g (`(behT (`#wt) ⊆ i.p_post))
  })
(** 
  If behT is an operational semantics, it has to be small-step because we have external non-determinism.
  Defining a denotational semantics for STLC is a challenge.

  behS is a denotational semantics.

  Relating the two will be a challenge. Usually, it is really hard to relate denotational and operational semantics
  of the same language. In this case, we have two different languages, one that it is shallowly embedded and one
  that is deeply embedded.
**)


// let soundness (#i:intS) (pt:progT (comp_int i)) =
//   forall (ct:ctxT (comp_int i)). behT (linkT pt ct) ⊆ i.p_post

(** The order of the quantifiers makes this RHC (Robust Hyperproperty Preservation) **)
let rhc (#i:intS) (ps:progS i) (pt:progT (comp_int i)) =
  forall (ct:ctxT (comp_int i)).
    exists (cs:ctxS i). behS (linkS ps cs) ≡ behT (linkT pt ct) 

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx ct = STLC.elab_exp (dsnd ct) STLC.vempty

let rhc_1 (#i:intS) (ps:progS i) (pt:progT (comp_int i)) =
  forall ct. behS (linkS ps (backtranslate_ctx ct)) ≡ behT (linkT pt ct) 

val compile_prog :
  (g:env) ->
  i:term{tot_typing g i (`intS)} ->
  ps:term{tot_typing g ps (`progS (`#i))} ->
  Tac (pt:term{
    tot_typing g pt (`progT (comp_int (`#i))) /\

    (** soundness **)
    // valid g (`(soundness (`#pt))) /\

    (** RHC **)
    valid g (`(rhc (`#ps) (`#pt)))
  })

  // Example of usage:
  // let i : intS = ...
  // let ps : progS i = ...
  // let g_ast : ast_env = ...

  //  %splice_t [pt;pt_sound;ps_pt_rhc] (compile_prog (`i) (`ps) (`g_ast))
  // // adds in environment the following:

  // let pt : progT (comp_int i g_ast) = ...
  // let pt_sound : squash (soundness pt) = ...
  // let ps_pt_rhc : squash (rhc ps pt) = ...

type rel = 
  #ty:STLC.typ -> 
  STLC.elab_typ ty ->             (** F* value **)
  #e:STLC.exp ->                  (** STLC value **)
  STLC.typing STLC.empty e ty -> 
  Type0

(** we want to instantiate this with the result of the compiler,
    which should give as a ws and a wt and a proof of ws `r` wt,
    thus no need for equivalence **)
let rel_whole (r:rel) (ws:wholeS) (wt:wholeT) : Type0 =
  ws `r` (dsnd wt) ==> cc ws wt

let rel_pprog (r:rel) i ps pt : Type0 =
  ps `r` (dsnd pt) ==> rhc_1 #i ps pt

val naive_rel : rel
let rec naive_rel #ty fst_e hte =
  (** TODO: is it ok to use eval in here? **)
  let (| stlc_e, hte |) = STLC.eval hte in
  match hte with
  | STLC.TyLam tv #_ #t' _ -> 
    let fst_f : STLC.elab_typ tv -> STLC.elab_typ t' = fst_e in
    forall (v:STLC.exp) (htv:STLC.typing STLC.empty v tv). 
      let fst_v : STLC.elab_typ tv = STLC.elab_exp htv STLC.vempty in
      let happ : STLC.typing STLC.empty (STLC.EApp stlc_e v) t' = STLC.TyApp hte htv in
      (fst_v `naive_rel` htv) <==> ((fst_f fst_v) `naive_rel` happ)
  | STLC.TyUnit -> fst_e == ()
  | STLC.TyZero -> fst_e == 0
  | STLC.TySucc hte' -> fst_e > 0 /\ (fst_e-1) `naive_rel` hte'
  | STLC.TyInl #_ #_ #t1 t2 ht1 ->
    let fst_sum : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fst_e in
    Inl? fst_sum /\ (Inl?.v fst_sum `naive_rel` ht1)
  | STLC.TyInr #_ #_ t1 #t2 ht2 ->
    let fst_sum : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fst_e in
    Inr? fst_sum /\ (Inr?.v fst_sum `naive_rel` ht2)
  | STLC.TyPair #_ #_ #_ #t1 #t2 ht1 ht2 ->
    let fst_pair : (STLC.elab_typ t1 * STLC.elab_typ t2) = fst_e in
    let (fst_fst, fst_snd) = fst_pair in
    (fst_fst `naive_rel` ht1) /\ (fst_snd `naive_rel` ht2)
