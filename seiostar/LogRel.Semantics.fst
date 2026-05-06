module LogRel.Semantics

open LambdaIO
open IOStar
open QTypes.OpenValComp

unfold val fs_beh : #t:qType -> fs_comp t -> h:history -> hist_post h (fs_val t)
let fs_beh m = thetaP m

unfold val e_beh : closed_exp -> closed_exp -> h:history -> local_trace h -> Type0
let e_beh e e' h lt =
  steps e e' h lt /\ indexed_irred e' (h++lt)

let lem_fs_beh_call (o:io_ops) (args:fs_val (q_io_args o)) (res:fs_val (q_io_res o)) (h:history) :
  Lemma (requires (lem_q_io_args o;lem_q_io_res o;
                  io_post h o args res))
        (ensures (lem_q_io_args o; lem_q_io_res o;
        fs_beh #(q_io_res o) (q_io_call o args) h [op_to_ev o args res] res)) =
  lem_q_io_args o;lem_q_io_res o;
  match o with
  | OOpen -> lem_thetaP_call OOpen args res h
  | ORead -> lem_thetaP_call ORead args res h
  | OWrite -> lem_thetaP_call OWrite args res h
  | OClose -> lem_thetaP_call OClose args res h

let lem_fs_beh_return #a (x:fs_val a) (h:history) :
  Lemma (fs_beh (return x) h [] x) =
  lem_thetaP_return x h

let lem_fs_beh_bind #a #b (m:fs_comp a) (h:history) (lt1:local_trace h) (fs_r_m:fs_val a) (k:fs_val a -> fs_comp b) (lt2:local_trace (h++lt1)) (fs_r:fs_val b) :
  Lemma (requires fs_beh m h lt1 fs_r_m /\
                  fs_beh (k fs_r_m) (h++lt1) lt2 fs_r)
        (ensures fs_beh (fs_comp_bind m k) h (lt1@lt2) fs_r) =
  lem_thetaP_bind m h lt1 fs_r_m k lt2 fs_r
