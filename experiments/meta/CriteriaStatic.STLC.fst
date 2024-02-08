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

