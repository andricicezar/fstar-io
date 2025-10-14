module RHC

open FStar.Tactics
open FStar.Tactics.Typeclasses

open STLC
open TypRel
open ExpRel
open Compiler

let my_rel_bool (fs_e:bool) (e:exp) : Type0 =
  (e == ETrue /\ fs_e == true) \/
  (e == EFalse /\ fs_e == false)

let lem_rel_beh' (fs_e: bool) (e:closed_exp) :
  Lemma
    (requires tbool ⦂ (fs_e, e))
    (**     vvv To have an existential here one needs normalization **)
    (ensures forall (e':closed_exp). steps e e' /\ irred e' ==>  my_rel_bool fs_e e')
= ()

assume val lem_rel_beh_arr (fs_e: bool -> bool) (e:closed_exp) :
  Lemma
    (requires (mk_arrow tbool tbool) ⦂ (fs_e, e)) (** here it is tbool because whole programs return booleans **)
    (ensures (forall fs_v (v:value). my_rel_bool fs_v v ==>
      (forall (e':closed_exp). steps (EApp e v) e' /\ irred e' ==>
        my_rel_bool (fs_e fs_v) e')))

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

assume type behS_t
assume val behS : wholeS -> behS_t

(** Target **)

noeq type intT = { ct : unit }

val comp_int : intS -> intT
let comp_int i = { ct = () }

type progT (i:intT) = closed_exp
type ctxT (i:intT) = ct:value//{sem_typing empty ct i.ct}
(** CA: syntactic typing necessary so that one can backtranslate and to know the type.
   **)
type wholeT = closed_exp

let linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  let wt = EApp pt ct in
  wt

assume type behT_t
assume val behT : wt:wholeT -> behT_t
assume val rel_behs : behS_t -> behT_t -> Type0

assume val backtranslate_ctx : (#i:intS) -> ctxT (comp_int i) -> ctxS i

(** CA: I suppose these two lemmas are the most hard core **)
assume val lem_rel_beh (fs_e: wholeS) (e:wholeT) :
  Lemma
    (requires tbool ⦂ (fs_e, e)) (** here it is tbool because whole programs return booleans **)
    (ensures  (behS fs_e) `rel_behs` (behT e))

assume val lem_bt_ctx i ct : Lemma (pack i.comp_ct ∋ (backtranslate_ctx #i ct, ct))

let compile_prog (#i:intS) (ps:progS i) : progT (comp_int i) =
  (dsnd ps).e

(** The order of the quantifiers makes this RHC (Robust Hyperproperty Preservation) **)
let rhc (#i:intS) (ps:progS i) =
  forall (ct:ctxT (comp_int i)).
    exists (cs:ctxS i). behS (linkS ps cs) `rel_behs` behT (linkT (compile_prog ps) ct)

let rhc_1 (#i:intS) (ps:progS i) =
  forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct)

let proof_rhc i ps : Lemma (rhc_1 #i ps) =
  introduce forall ct. behS (linkS ps (backtranslate_ctx ct)) `rel_behs` behT (linkT (compile_prog ps) ct) with begin
    let t : typsr = pack (i.comp_ct) in
    let pt : exp = (dsnd ps).e in
    let pt : progT (comp_int i) = pt in
    let ws : wholeS = (dfst ps) (backtranslate_ctx ct) in
    let wt : exp = EApp pt ct in
    let wt : wholeT = wt in
    (dsnd ps).equiv_proof ();
    let ps' = dfst ps in
    lemma_compile_closed_in_equiv_rel ps' #(dsnd ps);
    assert (mk_arrow t tbool ⦂ (ps', pt));
    lemma_compile_closed_arrow_is_elam #_ #_ #i.comp_ct ps' #(dsnd ps);
    assert (ELam? pt /\ is_closed pt /\ irred pt);
    eliminate forall (e':closed_exp). steps pt e' ==> irred e' ==> mk_arrow t tbool ∋ (ps', e') with pt;
    assert (mk_arrow t tbool ∋ (ps', pt));
    eliminate forall (v:value) (fs_v:get_Type t). t ∋ (fs_v, v) ==>
        tbool ⦂ (ps' fs_v, subst_beta v (ELam?.b pt))
      with ct (backtranslate_ctx ct);
    lem_bt_ctx i ct;
    assert (tbool ⦂ (ps' (backtranslate_ctx ct), subst_beta ct (ELam?.b pt)));
    lem_rel_beh (ps' (backtranslate_ctx ct)) (subst_beta ct (ELam?.b pt));
    assume (behT (EApp pt ct) == behT (subst_beta ct (ELam?.b pt))); (** simple to prove **)
    ()
  end
