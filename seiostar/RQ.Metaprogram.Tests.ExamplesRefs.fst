module RQ.Metaprogram.Tests.ExamplesRefs

open FStar.Tactics
open IOStar
open RQ.TypingRelation
open RQ.TypingRelation.Tests
open RQ.Metaprogram
open QTypes.HelperTactics

open ExamplesRefs

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
