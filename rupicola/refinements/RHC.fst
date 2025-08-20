module RHC

open FStar.Tactics
open FStar.Tactics.Typeclasses

open STLC
open SyntacticTypes
open SemanticTyping
open EquivRel
open Compiler

noeq type intS = {
  ct : Type;
  comp_ct : compile_typ ct;
}

(* CA: this definition of progS is very comical! I have the compiled program inside the guarantee that it can be compiled :D **)
type progS (i:intS) = ps:(i.ct -> bool) & compile_closed #_ #(compile_typ_arrow _ bool #i.comp_ct) ps
type ctxS (i:intS) = i.ct
type wholeS = bool // CA: To be able to compile whole programs requires a proof that it can be compiled

let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (dfst ps) cs

type behS_t = bool

val behS : wholeS -> behS_t
let behS ws = ws

(** Target **)

noeq type intT = { ct : typ }

val comp_int : intS -> intT
let comp_int i = { ct = i.comp_ct.t }

type progT (i:intT) = pt:closed_exp{sem_typing empty pt (TArr i.ct TBool)}
type ctxT (i:intT) = ct:value{sem_typing empty ct i.ct}
type wholeT = wt:closed_exp{sem_typing empty wt TBool}

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  let wt = EApp pt ct in
  assume (is_closed wt);
  assume (sem_typing empty wt TBool);
  wt

assume val eval : t:typ -> e:closed_exp{sem_typing empty e t} -> elab_typ t
assume val eval_equiv (t:typ) (e:closed_exp{sem_typing empty e t}) : Lemma (t ∋ (eval t e, e))

type behT_t = bool

val behT : wt:wholeT -> bool
let behT wt =
  eval TBool wt

val rel_behs : behS_t -> behT_t -> Type0
[@"opaque_to_smt"]
let rel_behs = (==)

assume val lem_rel_beh (fs_e: wholeS) (e:wholeT) :
  Lemma
    (requires TBool ⦂ (fs_e, e))
    (ensures  (behS fs_e) `rel_behs` (behT e))

let compile_prog (#i:intS) (ps:progS i) : progT (comp_int i) =
  (dsnd ps).typing_proof ();
  (dsnd ps).e


(** The order of the quantifiers makes this RHC (Robust Hyperproperty Preservation) **)
let rhc (#i:intS) (ps:progS i) =
  forall (ct:ctxT (comp_int i)).
    exists (cs:ctxS i). behS (linkS ps cs) `rel_behs` behT (linkT (compile_prog ps) ct)

val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i
let backtranslate_ctx #i ct = eval i.comp_ct.t ct

let rhc_1 (#i:intS) (ps:progS i) =
  forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct)

let proof_rhc i ps : Lemma (rhc_1 #i ps) =
  introduce forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct) with begin
    let t : typ = (comp_int i).ct in
    let pt : exp = (dsnd ps).e in
    (dsnd ps).typing_proof ();
    let pt : progT (comp_int i) = pt in
    let ws : wholeS = (dfst ps) (backtranslate_ctx ct) in
    let wt : exp = EApp pt ct in
    assume (is_closed wt); // is_closed pt /\ is_closed ct ==> is_closed wt
    assume (sem_typing empty wt TBool);
    let wt : wholeT = wt in
    (dsnd ps).equiv_proof ();
    let ps' = dfst ps in
    lemma_compile_closed_in_equiv_rel ps' #(dsnd ps);
    assert ((TArr t TBool) ⦂ (ps', pt));
    lemma_compile_closed_arrow_is_elam #_ #_ #i.comp_ct ps' #(dsnd ps);
    assert (ELam? pt /\ is_closed pt /\ irred pt);
    eliminate forall (e':closed_exp). steps pt e' ==> irred e' ==> TArr t TBool ∋ (ps', e') with pt;
    assert (TArr t TBool ∋ (ps', pt)); (** this should be proveable **)
    eliminate forall (v:value) (fs_v:elab_typ t). t ∋ (fs_v, v) ==>
        TBool ⦂ (ps' fs_v, subst_beta v (ELam?.b pt))
      with ct (backtranslate_ctx ct);
    eval_equiv t ct;
    assert (TBool ⦂ (ps' (backtranslate_ctx ct), subst_beta ct (ELam?.b pt)));
    assume (sem_typing empty (subst_beta ct (ELam?.b pt)) TBool);
    lem_rel_beh (ps' (backtranslate_ctx ct)) (subst_beta ct (ELam?.b pt));
 //   assert ((ps' (backtranslate_ctx ct) == eval TBool (subst_beta ct (ELam?.b pt))));
    assume (behT (EApp pt ct) == behT (subst_beta ct (ELam?.b pt))); (** simple to prove **)
//    assert (behS ws == behT wt);
    ()
  end
