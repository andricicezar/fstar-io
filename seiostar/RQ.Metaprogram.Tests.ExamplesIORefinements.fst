module RQ.Metaprogram.Tests.ExamplesIORefinements

open FStar.Tactics
open IOStar
open RQ.TypingRelation
open RQ.TypingRelation.Tests
open RQ.Metaprogram
open QTypes.HelperTactics

open ExamplesIORefinements

%splice_t[tgt_simple_erase_ref] (generate_derivation "tgt_simple_erase_ref" (`simple_erase_ref))
%splice_t[tgt_simple_ref_id] (generate_derivation "tgt_simple_ref_id" (`simple_ref_id))
%splice_t[tgt_simple_reref_id] (generate_derivation "tgt_simple_reref_id" (`simple_reref_id))
%splice_t[tgt_simple_ref_bind] (generate_derivation "tgt_simple_ref_bind" (`simple_ref_bind))

%splice_t[tgt_io_ret_ref_true] (generate_derivation "tgt_io_ret_ref_true" (`io_ret_ref_true))
%splice_t[tgt_io_ret_ref_false] (generate_derivation "tgt_io_ret_ref_false" (`io_ret_ref_false))
%splice_t[tgt_io_negate_ref] (generate_derivation "tgt_io_negate_ref" (`io_negate_ref))
%splice_t[tgt_io_if_both_false] (generate_derivation "tgt_io_if_both_false" (`io_if_both_false))

%splice_t[tgt_io_bind_ret_ref] (generate_derivation "tgt_io_bind_ret_ref" (`io_bind_ret_ref))
%splice_t[tgt_io_call_ret_ref] (generate_derivation "tgt_io_call_ret_ref" (`io_call_ret_ref))
%splice_t[tgt_io_two_calls_ref] (generate_derivation "tgt_io_two_calls_ref" (`io_two_calls_ref))

%splice_t[tgt_io_pair_ref] (generate_derivation "tgt_io_pair_ref" (`io_pair_ref))
%splice_t[tgt_io_inl_ref] (generate_derivation "tgt_io_inl_ref" (`io_inl_ref))
%splice_t[tgt_io_inr_ref] (generate_derivation "tgt_io_inr_ref" (`io_inr_ref))

%splice_t[tgt_io_case_ref] (generate_derivation "tgt_io_case_ref" (`io_case_ref))
%splice_t[tgt_io_ifbang_ref] (generate_derivation "tgt_io_ifbang_ref" (`io_ifbang_ref))
%splice_t[tgt_io_matchbang_ref] (generate_derivation "tgt_io_matchbang_ref" (`io_matchbang_ref))

%splice_t[tgt_io_ghost_seq] (generate_derivation "tgt_io_ghost_seq" (`io_ghost_seq))
%splice_t[tgt_io_apply_callback] (generate_derivation "tgt_io_apply_callback" (`io_apply_callback))
