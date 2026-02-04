module LogRelTargetSource

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open QTyp
open IO
open Trace

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∈) (t:qType) (p:(history * fs_val t * closed_exp)) : Tot Type0 (decreases %[get_rel t;0]) =
  let (h, fs_v, e) = p in
  match get_rel t with // way to "match" on F* types
  | QUnit -> fs_v == () /\ e == EUnit
  | QBool -> (fs_v == true /\ e == ETrue) \/ (fs_v == false /\ e == EFalse)
  | QFileDescriptor ->  e == EFileDescr fs_v
  | QArr #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> t2 = fs_v in
    match e with
    | ELam e' ->
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∈ (h++lt_v, fs_v, v) ==>
        pack qt2 ⊆ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QArrIO #t1 #t2 qt1 qt2 -> begin
    let fs_f : t1 -> io t2 = fs_v in
    match e with
    | ELam e' -> // instead quantify over h'' - extensions of the history:
      (forall (v:value) (fs_v:t1) (lt_v:local_trace h). pack qt1 ∈ (h++lt_v, fs_v, v) ==>
        pack qt2 ⫃ (h++lt_v, fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
  | QPair #t1 #t2 qt1 qt2 -> begin
    match e with
    | EPair e1 e2 -> (** e1 and e2 are values. no need to quantify over lts **)
        pack qt1 ∈ (h, fst #t1 #t2 fs_v, e1) /\ pack qt2 ∈ (h, snd #t1 #t2 fs_v, e2)
    | _ -> False
  end
  | QSum #t1 #t2 qt1 qt2 -> begin
    let fs_v : either t1 t2 = fs_v in
    match fs_v, e with
    | Inl fs_v', EInl e' -> pack qt1 ∈ (h, fs_v', e')
    | Inr fs_v', EInr e' -> pack qt2 ∈ (h, fs_v', e')
    | _ -> False
  end
                           (** vvvvvvvvvv defined over values **)
and (⊆) (t:qType) (p:history * fs_val t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  exists (e':closed_exp). e_beh e e' h [] /\ t ∈ (h, fs_e, e')
                           (** vvvvvvvvvv defined over producers **)
and (⫃) (t:qType) (p:history * fs_prod t * closed_exp) : Tot Type0 (decreases %[get_rel t;1]) =
  let (h, fs_e, e) = p in
  forall lt.
    (forall (fs_r:get_Type t). fs_beh fs_e h lt fs_r ==>
      exists e'. t ∈ (h++lt, fs_r, e') /\ e_beh e e' h lt)

let unroll_elam_io123 (t1 t2:qType) (h:history) (fs_e1:fs_val (t1 ^->!@ t2)) (e11:exp)
  : Lemma (requires (is_closed (ELam e11)) /\ ((t1 ^->!@ t2) ∈ (h, fs_e1, ELam e11)))
          (ensures (forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, fs_e1 fs_v, subst_beta v e11))) = admit ()

let unroll_elam_io123' (t1 t2:qType) (fs_e1:fs_val (t1 ^->!@ t2)) (e11:exp)
  : Lemma (requires (is_closed (ELam e11)) /\ (forall h. (t1 ^->!@ t2) ∈ (h, fs_e1, ELam e11)))
          (ensures (forall h (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, fs_e1 fs_v, subst_beta v e11))) =
  introduce forall h. forall (v:value) (fs_v:fs_val t1) (lt_v:local_trace h). t1 ∈ (h++lt_v, fs_v, v) ==> t2 ⫃ (h++lt_v, fs_e1 fs_v, subst_beta v e11) with begin
    unroll_elam_io123 t1 t2 h fs_e1 e11
  end
