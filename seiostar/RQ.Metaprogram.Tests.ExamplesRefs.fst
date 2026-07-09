module RQ.Metaprogram.Tests.ExamplesRefs

open FStar.Tactics
open IOStar
open RQ.TypingRelation
open RQ.TypingRelation.Tests
open RQ.Metaprogram
open QTypes.HelperTactics

open ExamplesRefs

%splice_t[tgt_incr_nat8] (generate_derivation "tgt_incr_nat8" (`incr_nat8))

%splice_t[tgt_incr_nat8'] (generate_derivation "tgt_incr_nat8'" (`incr_nat8'))

%splice_t[tgt_refbool] (generate_derivation "tgt_refbool" (`refbool))
%splice_t[tgt_falsepre] (generate_derivation "tgt_falsepre" (`falsepre))
%splice_t[tgt_just_true] (generate_derivation "tgt_just_true" (`just_true))
%splice_t[tgt_moving_ref] (generate_derivation "tgt_moving_ref" (`moving_ref))
%splice_t[tgt_always_false] (generate_derivation "tgt_always_false" (`always_false))
%splice_t[tgt_always_false_complex] (generate_derivation "tgt_always_false_complex" (`always_false_complex))
%splice_t[tgt_always_false_ho] (generate_derivation "tgt_always_false_ho" (`always_false_ho))

%splice_t[tgt_if_x] (generate_derivation "tgt_if_x" (`if_x))
%splice_t[tgt_if_seq] (generate_derivation "tgt_if_seq" (`if_seq))
%splice_t[tgt_seq_basic] (generate_derivation "tgt_seq_basic" (`seq_basic))
%splice_t[tgt_seq_qref] (generate_derivation "tgt_seq_qref" (`seq_qref))
%splice_t[tgt_seq_p_implies_q] (generate_derivation "tgt_seq_p_implies_q" (`seq_p_implies_q))
%splice_t[tgt_context] (generate_derivation "tgt_context" (`context))

%splice_t[tgt_needs_true] (generate_derivation "tgt_needs_true" (`needs_true))
%splice_t[tgt_proj_into_refined] (generate_derivation_using "tgt_proj_into_refined" (`proj_into_refined) [
 (`%needs_true, `tgt_needs_true)
])

%splice_t[tgt_refined_pair_inner] (generate_derivation "tgt_refined_pair_inner" (`refined_pair_inner))

%splice_t[tgt_refined_pair] (generate_derivation "tgt_refined_pair" (`refined_pair))

%splice_t[tgt_fun_beh_ref] (generate_derivation "tgt_fun_beh_ref" (`fun_beh_ref))
%splice_t[tgt_ret_refined_arg] (generate_derivation "tgt_ret_refined_arg" (`ret_refined_arg))
%splice_t[tgt_inl_refined_arg] (generate_derivation "tgt_inl_refined_arg" (`inl_refined_arg))
%splice_t[tgt_pure_validate] (generate_derivation "tgt_pure_validate" (`pure_validate))
%splice_t[tgt_pure_validate2] (generate_derivation "tgt_pure_validate2" (`pure_validate2))
%splice_t[tgt_pure_validate3] (generate_derivation "tgt_pure_validate3" (`pure_validate3))
