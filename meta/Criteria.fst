module Criteria
module STLC = STLC

(** Relation between First Order Values of F* and STLC **)
let rec (∽) (#t:STLC.fo_typ) (fs_v:STLC.elab_typ t) (#e:STLC.exp{STLC.is_value e}) (stlc_ht:STLC.typing STLC.empty e t) : Type0 =
  match stlc_ht with
  | STLC.TyUnit -> fs_v == ()
  | STLC.TyZero -> fs_v == 0
  | STLC.TySucc ht -> fs_v > 0 /\ (fs_v-1) ∽ ht
  
  | STLC.TyInl #_ #_ #t1 t2 ht1 ->
    let fst_inl : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fs_v in
    Inl? fst_inl /\ (Inl?.v fst_inl ∽ ht1)
  | STLC.TyInr #_ #_ t1 #t2 ht2 ->
    let fs_inr : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fs_v in
    Inr? fs_inr /\ (Inr?.v fs_inr ∽ ht2)
  | STLC.TyPair #_ #_ #_ #t1 #t2 ht_fst ht_snd ->
    let (fs_fst, fs_snd) : (STLC.elab_typ t1 * STLC.elab_typ t2) = fs_v in
    (fs_fst ∽ ht_fst) /\ (fs_snd ∽ ht_snd)

(** *** Intrinsic criteria, static quoting/unquoting  **)
type propS (t:STLC.fo_typ) = STLC.elab_typ t
type propT (t:STLC.fo_typ) = e:STLC.exp{STLC.is_value e} & STLC.typing STLC.empty e t (** first order STLC value **)

// let (⊆) (s0 s1:set_prop) : Type0 = False
let (≌) (#t:STLC.fo_typ) (ss:propS t) (st:propT t) : Type0 =
  ss ∽ (dsnd st)

noeq type intS = { 
  ct_stlc : STLC.typ;
  // p_post : set_prop
}

type progS (i:intS) = STLC.elab_typ i.ct_stlc -> Tot nat
type ctxS (i:intS) = STLC.elab_typ i.ct_stlc
type wholeS = (unit -> Tot nat)

let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (fun () -> ps cs)

val behS : wholeS -> propS (STLC.TNat)
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
  let htwt = STLC.thunk (STLC.TyApp htp htc) in
  (| _, htwt |)

val behT : wt:wholeT -> propT (STLC.TNat)
let behT (| ew, htw |) = STLC.eval (STLC.TyApp htw STLC.TyUnit)

(** We can replace the refinement that pt, wt and ct are values,
    with a refinement that pt, ct and wt can be stepped purely to a value,
    and then we will need the following lemmas:

assume val pure_step_preserves_behT_wt (wt:wholeT)
 : Lemma (ensures (
    ~(STLC.is_value (dfst wt)) /\
    (forall (wt':wholeT). STLC.pure_step (dfst wt) (dfst wt') ==> 
      behT wt ≌ behT wt')))

assume val pure_step_preserves_behT_pt #i (pt:progT i) (ct:ctxT i)
 : Lemma (ensures (
    ~(STLC.is_value (dfst pt)) /\
    (forall (pt':progT i). STLC.pure_step (dfst pt) (dfst pt') ==> 
      behT (linkT pt ct) ≌ behT (linkT pt' ct))))

assume val pure_steps_preserves_behT_wt (wt:wholeT)
 : Lemma (ensures (
    forall (wt':wholeT). STLC.pure_steps (dfst wt) (dfst wt') ==> 
      behT wt ≌ behT wt'))

assume val pure_steps_preserves_behT_pt #i (pt:progT i) (ct:ctxT i)
 : Lemma (ensures (
    forall (pt':progT i). STLC.pure_steps (dfst pt) (dfst pt') ==> 
      behT (linkT pt ct) ≌ behT (linkT pt' ct)))
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
  behS ws ≌ behT wt

val compile_whole : 
  (g:env) ->
  (ws:term{tot_typing g ws (`wholeS)}) ->
  Tac (wt:term{
    tot_typing g wt (`wholeT) /\
    (** compiler correctness **)
    valid g (`(cc (`#ws) (`#wt)))
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
    exists (cs:ctxS i). behS (linkS ps cs) ≌ behT (linkT pt ct) 

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx ct = STLC.elab_exp (dsnd ct) STLC.vempty

(** TODO: can we prove RrHP from this since we got rid off the exists? **)
let rhc_1 (#i:intS) (ps:progS i) (pt:progT (comp_int i)) =
  forall ct. behS (linkS ps (backtranslate_ctx ct)) ≌ behT (linkT pt ct) 

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

(** CA: If we will target Gradual Typing,
  then the type of the following relation will not work because
  it will not be able to elaborate a dynamic type to the static type of F*.
  aka, how would one define `elab_typ any = ?`
**)

type rel = 
  #ty:STLC.typ -> 
  STLC.elab_typ ty ->             (** F* value **)
  #e:STLC.exp ->                  (** STLC expression **)
  STLC.typing STLC.empty e ty -> 
  Type0

(** we want to instantiate this with the result of the compiler,
    which should give for a ws a wt and a proof of ws `r` wt **)
let rel_whole (r:rel) (ws:wholeS) (wt:wholeT) : Type0 =
  ws `r` (dsnd wt) ==> cc ws wt

let rel_pprog (r:rel) i ps pt : Type0 =
  ps `r` (dsnd pt) ==> rhc_1 #i ps pt

(** Cross-language logical relation,
    the logical relation is asymmetric because it relates always F* values with STLC's values and expressions *)
(** Note: usually, this is split into a relation on target values and on target expressions **)
val (≍) : rel
let rec (≍) #ty fs_v stlc_ht' =
  // forall stlc_e', hte', ss:steps stlc_e stlc_e'. is_value stlc_e' ==>
  (** First, we make sure that stlc_e contains a value. (fst_e is already a value)**)
  let (| stlc_e, stlc_ht |) = STLC.eval stlc_ht' in (** it is ok to use eval when it means a big-step operational semantics
                                                       and not an interpreter (in the longer run) **)
  // assert (STLC.is_value stlc_e);
  match stlc_ht with
  // base types
  | STLC.TyUnit
  | STLC.TyZero
  | STLC.TySucc _ ->
    (** One can avoid using elab_exp, but using it simplifies proofs later **)
    fs_v ∽ stlc_ht
  
  // polymorphic types
  | STLC.TyInl #_ #_ #t1 t2 ht1 ->
    let fst_inl : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fs_v in
    Inl? fst_inl /\ (Inl?.v fst_inl ≍ ht1)
  | STLC.TyInr #_ #_ t1 #t2 ht2 ->
    let fs_inr : either (STLC.elab_typ t1) (STLC.elab_typ t2) = fs_v in
    Inr? fs_inr /\ (Inr?.v fs_inr ≍ ht2)
  | STLC.TyPair #_ #_ #_ #t1 #t2 ht_fst ht_snd ->
    let (fs_fst, fs_snd) : (STLC.elab_typ t1 * STLC.elab_typ t2) = fs_v in
    (fs_fst ≍ ht_fst) /\ (fs_snd ≍ ht_snd)

  // lambda
  | STLC.TyAbs tv #_ #t' _ -> 
    let fs_f : STLC.elab_typ tv -> STLC.elab_typ t' = fs_v in
    forall stlc_x (ht_x:STLC.typing STLC.empty stlc_x tv). (** all values possible in STLC **)
      forall fs_x.
      // let fst_v = STLC.elab_exp htv STLC.vempty in (** this is non-standard, and it may produce problems in HO cases **)
        (fs_x ≍ ht_x) ==> ((fs_f fs_x) ≍ (STLC.TyApp stlc_ht ht_x))

let x1 : STLC.exp =
    STLC.EAbs STLC.TNat (STLC.EVar 0)
let x1ty : STLC.typing STLC.empty x1 (STLC.TArr STLC.TNat STLC.TNat) =
    STLC.TyAbs STLC.TNat (STLC.TyVar 0)

let test123 =
  assert ((fun (x:nat) -> x) ≍ x1ty) by (compute ())

// let x2 : STLC.exp =
//     STLC.EAbs STLC.TNat (STLC.EAbs STLC.TUnit (STLC.EVar 1))
// let x2ty : STLC.typing STLC.empty x2 (STLC.TArr STLC.TNat (STLC.TArr STLC.TUnit STLC.TNat)) =
//     STLC.TyAbs STLC.TNat (STLC.TyAbs STLC.TUnit (STLC.TyVar 1))

// let test1234 =
//   assert ((fun (x:nat) -> (fun () -> x)) ≍ x2ty) by (
//       compute ();
//       explode ();
//       dump "H"
//   )

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
    behS ws ≌ behT wt
  with _. begin
    assert (ws ≍ htw);
    // unfolding ≍
    let (| ewt', htwt' |) = STLC.eval htw in
    assert (ws ≍ htwt'); // wt' is a value (Lam) and returns a nat
    assert (behS ws ≌ behT (| ewt', htwt' |));
    eval_value_is_id htw;
    assert (behT (| ewt', htwt' |) == behT wt);
    assert (behS ws ≌ behT wt)
  end

val elab_rel (#e:STLC.exp) (#t:STLC.typ) (ht:STLC.typing STLC.empty e t)
  : Lemma (STLC.elab_exp ht STLC.vempty ≍ ht)
let rec elab_rel #e #t ht =
  match ht with
  | STLC.TyUnit -> ()
  | STLC.TyZero -> ()
  | STLC.TySucc _ -> admit ()
  | STLC.TyApp h1 h2 -> admit ()
  | _ -> admit ()

let rel_implies_rhc i ps pt : Lemma (rel_pprog (≍) i ps pt) = 
  introduce 
    ps ≍ (dsnd pt)
  ==> 
    (forall ct. behS (linkS ps (backtranslate_ctx ct)) ≌ behT (linkT pt ct) )
  with _. begin
    introduce 
      forall ct. behS (linkS ps (backtranslate_ctx ct)) ≌ behT (linkT pt ct)
    with begin
      admit ();
      // unfolding ≍
      let (| ept', htpt' |) = STLC.eval (dsnd pt) in
      eval_value_is_id (dsnd pt);
      assert (behT (linkT pt ct) == behT (linkT (| ept', htpt' |) ct));

      // ps ≍ (dsnd pt) implies:
      assert (ps ≍ htpt');
      
      let cs = backtranslate_ctx ct in
      elab_rel (dsnd ct);
      assert (cs ≍ dsnd ct);

      let htbody = STLC.TyApp htpt' (dsnd ct) in
      assert (ps cs ≍ htbody);

      let htwt = STLC.thunk htbody in
      let htwtapp = STLC.TyApp htwt STLC.TyUnit in
      assume (ps cs ≍ htwtapp); // this should be simple to prove

      assert (behS (linkS ps cs) ≌ behT (linkT (| ept', htpt' |) ct));
      assert (behS (linkS ps cs) ≌ behT (linkT pt ct))
    end
  end
