module CriteriaStatic.STLC
module STLC = STLC

(** *** Intrinsic criteria, static quoting/unquoting  **)
type set_prop = nat
let (⊆) (s0 s1:set_prop) : Type0 = False
let (≡) (s0 s1:set_prop) : Type0 = s0 == s1

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
let behS ws = ws ()

(** Target **)

noeq type intT = { ct : STLC.typ }

val comp_int : intS -> intT
let comp_int i = { ct = i.ct_stlc }

type progT (i:intT) = pt:STLC.exp{STLC.is_value pt} & STLC.typing STLC.empty pt (STLC.TArr i.ct STLC.TNat)
type ctxT (i:intT) = ct:STLC.exp{STLC.is_value ct} & STLC.typing STLC.empty ct i.ct
type wholeT = wt:STLC.exp{STLC.is_value wt} & STLC.typing STLC.empty wt (STLC.TArr STLC.TUnit STLC.TNat)

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT = 
  let (| _, htp |) = pt in
  let (| _, htc |) = ct in
  let (| ewt, htwt |) = STLC.thunk_exp (STLC.TyApp htp htc) in
  (| ewt, htwt |)

val behT : wt:wholeT -> set_prop 
let behT (| ew, htw |) = STLC.sem (STLC.TyApp htw STLC.TyUnit)

(** We can replace the refinement that pt, wt and ct are values,
    with a refinement that pt, ct and wt can be stepped purely to a value,
    and then we will need the following lemmas:

assume val pure_step_preserves_behT_wt (wt:wholeT)
 : Lemma (ensures (
    ~(STLC.is_value (dfst wt)) /\
    (forall (wt':wholeT). STLC.pure_step (dfst wt) (dfst wt') ==> 
      behT wt ≡ behT wt')))

assume val pure_step_preserves_behT_pt #i (pt:progT i) (ct:ctxT i)
 : Lemma (ensures (
    ~(STLC.is_value (dfst pt)) /\
    (forall (pt':progT i). STLC.pure_step (dfst pt) (dfst pt') ==> 
      behT (linkT pt ct) ≡ behT (linkT pt' ct))))

assume val pure_steps_preserves_behT_wt (wt:wholeT)
 : Lemma (ensures (
    forall (wt':wholeT). STLC.pure_steps (dfst wt) (dfst wt') ==> 
      behT wt ≡ behT wt'))

assume val pure_steps_preserves_behT_pt #i (pt:progT i) (ct:ctxT i)
 : Lemma (ensures (
    forall (pt':progT i). STLC.pure_steps (dfst pt) (dfst pt') ==> 
      behT (linkT pt ct) ≡ behT (linkT pt' ct)))
**) 

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

val (≍) : rel
let rec (≍) #ty fst_e hte =
  // forall stlc_e', hte', ss:steps stlc_e stlc_e'. is_value stlc_e' ==>
  (** First, we make sure that stlc_e contains a value. (fst_e is already a value)**)
  let (| stlc_e, hte |) = STLC.eval hte in (** TODO: is it ok to use eval in here? **)
  // assert (STLC.is_value stlc_e);
  match hte with
  // base types
  | STLC.TyUnit
  | STLC.TyZero
  | STLC.TySucc _ ->
    (** One can avoid using elab_exp, but using it simplifies proofs later **)
    fst_e == STLC.elab_exp hte STLC.vempty
  
  // polymorphic types
  | STLC.TyInl #_ #_ #t1 t2 ht1 ->
    let fst_sum : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fst_e in
    Inl? fst_sum /\ (Inl?.v fst_sum ≍ ht1)
  | STLC.TyInr #_ #_ t1 #t2 ht2 ->
    let fst_sum : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fst_e in
    Inr? fst_sum /\ (Inr?.v fst_sum ≍ ht2)
  | STLC.TyPair #_ #_ #_ #t1 #t2 ht1 ht2 ->
    let (fst_fst, fst_snd) : (STLC.elab_typ t1 * STLC.elab_typ t2) = fst_e in
    (fst_fst ≍ ht1) /\ (fst_snd ≍ ht2)

  // lambda
  | STLC.TyLam tv #_ #t' _ -> 
    let fst_f : STLC.elab_typ tv -> STLC.elab_typ t' = fst_e in
    forall v (htv:STLC.typing STLC.empty v tv). 
      let fst_v = STLC.elab_exp htv STLC.vempty in
      (fst_v ≍ htv) ==> ((fst_f fst_v) ≍ (STLC.TyApp hte htv))

let x1 : STLC.exp =
    STLC.ELam STLC.TNat (STLC.EVar 0)
let x1ty : STLC.typing STLC.empty x1 (STLC.TArr STLC.TNat STLC.TNat) =
    STLC.TyLam STLC.TNat (STLC.TyVar 0)

let test123 =
  assert ((fun (x:nat) -> x) ≍ x1ty) by (compute ())


(** we don't really need this since F* can figure it out by itself, but
    it is useful to keep track where it is used. If we change the refinement
    on pt, ct and wt, then we will need to replace it. **)
let eval_value_is_id (#e:STLC.exp) (#t:STLC.typ) (ht:STLC.typing STLC.empty e t)
  : Lemma (STLC.is_value e ==> STLC.eval ht == (| e, ht |)) = ()

let rel_implies_cc ws wt : Lemma (rel_whole (≍) ws wt) = 
  let (| ew, htw |) = wt in
  introduce 
    ws ≍ (dsnd wt)
  ==> 
    behS ws ≡ behT wt
  with _. begin
    assert (ws ≍ htw);
    // unfolding ≍
    let (| ewt', htwt' |) = STLC.eval htw in
    eval_value_is_id htw;
    assert (behT (| ewt', htwt' |) ≡ behT wt);
    assert (ws ≍ htwt'); // wt' is a value (Lam) and returns a nat
    assert (behS ws ≡ behT (| ewt', htwt' |));
    assert (behS ws ≡ behT wt)
  end

val elab_rel (#e:STLC.exp) (#t:STLC.typ) (ht:STLC.typing STLC.empty e t)
  : Lemma (STLC.elab_exp ht STLC.vempty ≍ ht)
let rec elab_rel #e #t ht =
  match ht with
  | STLC.TyUnit -> ()
  | STLC.TyZero -> ()
  | STLC.TySucc _ -> STLC.elab_invariant_to_eval ht
  | STLC.TyApp h1 h2 -> admit ()
  | _ -> admit ()

let rel_implies_rhc i ps pt : Lemma (rel_pprog (≍) i ps pt) = 
  introduce 
    ps ≍ (dsnd pt)
  ==> 
    (forall ct. behS (linkS ps (backtranslate_ctx ct)) ≡ behT (linkT pt ct) )
  with _. begin
    introduce 
      forall ct. behS (linkS ps (backtranslate_ctx ct)) ≡ behT (linkT pt ct)
    with begin
      // unfolding ≍
      let (| ept', htpt' |) = STLC.eval (dsnd pt) in
      eval_value_is_id (dsnd pt);
      assert (behT (linkT pt ct) ≡ behT (linkT (| ept', htpt' |) ct));

      // ps ≍ (dsnd pt) implies:
      assert (ps ≍ htpt');
      
      let cs = backtranslate_ctx ct in
      elab_rel (dsnd ct);
      assert (cs ≍ dsnd ct);

      let htbody = STLC.TyApp htpt' (dsnd ct) in
      assert (ps cs ≍ htbody);

      let (| ewt, htwt |) = STLC.thunk_exp htbody in
      let htwtapp = STLC.TyApp htwt STLC.TyUnit in
      assume (ps cs ≍ htwtapp); // this should be simple to prove

      assert (behS (linkS ps cs) ≡ behT (linkT (| ept', htpt' |) ct));
      assert (behS (linkS ps cs) ≡ behT (linkT pt ct))
    end
  end
