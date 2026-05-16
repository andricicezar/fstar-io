module RQ.Metaprogram.Tests.Examples

open FStar.Tactics
open IOStar
open RQ.TypingRelation
open RQ.TypingRelation.Tests
open RQ.Metaprogram
open QTypes.HelperTactics

open Examples

(* --- Basic --- *)

%splice_t[tgt1] (generate_derivation "tgt1" (`ut_unit))
%splice_t[tgt2] (generate_derivation "tgt2" (`ut_true))
%splice_t[tgt3] (generate_derivation "tgt3" (`ut_false))
%splice_t[tgt4] (generate_derivation "tgt4" (`constant))
%splice_t[tgt5] (generate_derivation "tgt5" (`identity))
%splice_t[tgt6] (generate_derivation "tgt6" (`thunked_id))
%splice_t[tgt7] (generate_derivation "tgt7" (`proj1))
%splice_t[tgt8] (generate_derivation "tgt8" (`proj2))
%splice_t[tgt9] (generate_derivation "tgt9" (`proj3))

%splice_t[tgt10] (generate_derivation "tgt10" (`apply_arg))
%splice_t[tgt11] (generate_derivation "tgt11" (`apply_arg2))
%splice_t[tgt12] (generate_derivation "tgt12" (`papply_arg2))

(* --- Bool --- *)

%splice_t[tgt13] (generate_derivation "tgt13" (`negb))
%splice_t[tgt14] (generate_derivation "tgt14" (`if2))
%splice_t[tgt15] (generate_derivation "tgt15" (`callback_return))
%splice_t[tgt16] (generate_derivation "tgt16" (`callback_return'))

%splice_t[tgt_anif] (generate_derivation "tgt_anif" (`anif))
%splice_t[tgt_const_str] (generate_derivation "tgt_const_str" (`const_str))
%splice_t[tgt_greeting] (generate_derivation "tgt_greeting" (`greeting))
%splice_t[tgt_negb_pred] (generate_derivation "tgt_negb_pred" (`negb_pred))

%splice_t[tgt_a_few_lets] (generate_derivation "tgt_a_few_lets" (`a_few_lets))

let three_lets : bool -> unit =
  fun x -> let p = (x, x) in let _y = x in let _z = fst p in ()

%splice_t[tgt_three_lets] (generate_derivation "tgt_three_lets" (`three_lets))

(* --- PairsSums --- *)

%splice_t[tgt_make_pair] (generate_derivation "tgt_make_pair" (`make_pair))
%splice_t[tgt_pair_of_functions] (generate_derivation "tgt_pair_of_functions" (`pair_of_functions))
%splice_t[tgt_pair_of_functions2] (generate_derivation "tgt_pair_of_functions2" (`pair_of_functions2))
%splice_t[tgt_fst_pair] (generate_derivation "tgt_fst_pair" (`fst_pair))
%splice_t[tgt_wrap_fst] (generate_derivation "tgt_wrap_fst" (`wrap_fst))
%splice_t[tgt_snd_pair] (generate_derivation "tgt_snd_pair" (`snd_pair))
%splice_t[tgt_wrap_snd] (generate_derivation "tgt_wrap_snd" (`wrap_snd))
// wrap_fst_pa / wrap_snd_pa are point-free (= fst / snd); metaprogram requires explicit lambdas
// %splice_t[tgt_wrap_fst_pa] (generate_derivation "tgt_wrap_fst_pa" (`wrap_fst_pa))
// %splice_t[tgt_wrap_snd_pa] (generate_derivation "tgt_wrap_snd_pa" (`wrap_snd_pa))

%splice_t[tgt_inl_true] (generate_derivation "tgt_inl_true" (`inl_true))
%splice_t[tgt_inr_unit] (generate_derivation "tgt_inr_unit" (`inr_unit))
%splice_t[tgt_return_either] (generate_derivation "tgt_return_either" (`return_either))
%splice_t[tgt_match_either] (generate_derivation "tgt_match_either" (`match_either))
// match_either' has Inr before Inl; metaprogram only supports Inl-first matches
// %splice_t[tgt_match_either'] (generate_derivation "tgt_match_either'" (`match_either'))
%splice_t[tgt_match_either_arg] (generate_derivation "tgt_match_either_arg" (`match_either_arg))

(* --- NatTopLevel --- *)

%splice_t[tgt_apply_top_level_def] (generate_derivation "tgt_apply_top_level_def" (`apply_top_level_def))
%splice_t[tgt_apply_top_level_def'] (generate_derivation "tgt_apply_top_level_def'" (`apply_top_level_def'))
%splice_t[tgt_papply_top_level_def] (generate_derivation "tgt_papply_top_level_def" (`papply__top_level_def))

%splice_t[tgt_nat_zero] (generate_derivation "tgt_nat_zero" (`nat_zero))
%splice_t[tgt_nat_one] (generate_derivation "tgt_nat_one" (`nat_one))
%splice_t[tgt_nat_two] (generate_derivation "tgt_nat_two" (`nat_two))
%splice_t[tgt_nat_succ_fn] (generate_derivation "tgt_nat_succ_fn" (`nat_succ_fn))
%splice_t[tgt_nat_add2] (generate_derivation "tgt_nat_add2" (`nat_add2))
%splice_t[tgt_nat_five1] (generate_derivation "tgt_nat_five1" (`nat_five1))
%splice_t[tgt_nat_five2] (generate_derivation "tgt_nat_five2" (`nat_five2))
%splice_t[tgt_fact_five] (generate_derivation "tgt_fact_five" (`fact_five))
