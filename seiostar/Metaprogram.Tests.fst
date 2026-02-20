module Metaprogram.Tests

open FStar.Tactics
open Metaprogram
open IO
open QExp
open QTyp

let hocf (agent:bool -> bool -> bool -> bool -> bool -> io bool) : io bool =
  agent true false false true true

%splice_t[tgt_f] (generate_derivation "tgt_f" (`hocf))

%splice_t[tgt1] (generate_derivation "tgt1" (`Examples.ut_unit))
let _ = assert (tgt1 #empty == test_ut_unit) by (trefl ())

%splice_t[tgt2] (generate_derivation "tgt2" (`Examples.ut_true))
let _ = assert (tgt2 #empty == test_ut_true) by (trefl ())

%splice_t[tgt3] (generate_derivation "tgt3" (`Examples.ut_false))
let _ = assert (tgt3 #empty == test_ut_false) by (trefl ())



%splice_t[tgt4] (generate_derivation "tgt4" (`Examples.constant))

let _ = assert (tgt4 #empty == test_constant) by (trefl ())

%splice_t[tgt5] (generate_derivation "tgt5" (`Examples.identity))
let _ = assert (tgt5 #empty == test_identity) by (trefl ())

%splice_t[tgt6] (generate_derivation "tgt6" (`Examples.thunked_id))
let _ = assert (tgt6 #empty == test_thunked_id) by (trefl ())

%splice_t[tgt7] (generate_derivation "tgt7" (`Examples.proj1)  )
let _ = assert (tgt7 #empty == test_proj1) by (trefl ())
%splice_t[tgt8] (generate_derivation "tgt8" (`Examples.proj2))
let _ = assert (tgt8 #empty == test_proj2) by (trefl ())
%splice_t[tgt9] (generate_derivation "tgt9" (`Examples.proj3))
let _ = assert (tgt9 #empty == test_proj3) by (trefl ())

%splice_t[tgt10] (generate_derivation "tgt10" (`Examples.apply_arg))
let _ = assert (tgt10 #empty == test_apply_arg) by (trefl ())


%splice_t[tgt11] (generate_derivation "tgt11" (`Examples.apply_arg2))
let _ = assert (tgt11 #empty == test_apply_arg2 ()) by (trefl ())


%splice_t[tgt12] (generate_derivation "tgt12" (`Examples.papply_arg2))
let _ = assert (tgt12 #empty == test_papply_arg2 ()) by (trefl ())

%splice_t[tgt13] (generate_derivation "tgt13" (`Examples.negb))
let _ = assert (tgt13 #empty == test_negb) by (trefl ())

%splice_t[tgt14] (generate_derivation "tgt14" (`Examples.if2))
let _ = assert (tgt14 #empty == test_if2 ()) by (trefl ())

%splice_t[tgt15] (generate_derivation "tgt15" (`Examples.callback_return))
let _ = assert (tgt15 #empty == test_callback_return ()) by (trefl ())


%splice_t[tgt_make_pair] (generate_derivation "tgt_make_pair" (`Examples.make_pair))
let _ = assert (tgt_make_pair #empty == test_make_pair) by (trefl ())

%splice_t[tgt_fst_pair] (generate_derivation "tgt_fst_pair" (`Examples.fst_pair))
let _ = assert (tgt_fst_pair #empty == test_fst_pair) by (trefl ())

%splice_t[tgt_wrap_fst] (generate_derivation "tgt_wrap_fst" (`Examples.wrap_fst))
let _ = assert (tgt_wrap_fst #empty == test_wrap_fst) by (trefl ())

%splice_t[tgt_snd_pair] (generate_derivation "tgt_snd_pair" (`Examples.snd_pair))
let _ = assert (tgt_snd_pair #empty == test_snd_pair) by (trefl ())

%splice_t[tgt_wrap_snd] (generate_derivation "tgt_wrap_snd" (`Examples.wrap_snd))
let _ = assert (tgt_wrap_snd #empty == test_wrap_snd) by (trefl ())

%splice_t[tgt_a_few_lets] (generate_derivation "tgt_a_few_lets" (`Examples.a_few_lets))
let _ = assert (tgt_a_few_lets #empty == QLambda Qtt) by (trefl ())

%splice_t[tgt_inl_true] (generate_derivation "tgt_inl_true" (`Examples.inl_true))
let _ = assert (tgt_inl_true #empty == test_inl_true) by (trefl ())

%splice_t[tgt_inr_unit] (generate_derivation "tgt_inr_unit" (`Examples.inr_unit))
let _ = assert (tgt_inr_unit #empty == test_inr_unit) by (trefl ())

%splice_t[tgt_return_either] (generate_derivation "tgt_return_either" (`Examples.return_either))
let _ = assert (tgt_return_either #empty == test_return_either ()) by (trefl ())

%splice_t[tgt_match_either] (generate_derivation "tgt_match_either" (`Examples.match_either))
let _ = assert (tgt_match_either #empty == test_match_either ()) by (trefl ())


%splice_t[tgt_match_either_arg] (generate_derivation "tgt_match_either_arg" (`Examples.match_either_arg))
let _ = assert (tgt_match_either_arg #empty == test_match_either_arg ()) by (trefl ())


%splice_t[tgt_apply_top_level_def] (generate_derivation "tgt_apply_top_level_def" (`Examples.apply_top_level_def))

%splice_t[tgt_apply_top_level_def'] (generate_derivation "tgt_apply_top_level_def'" (`Examples.apply_top_level_def'))

%splice_t[tgt_papply_top_level_def] (generate_derivation "tgt_papply_top_level_def" (`Examples.papply__top_level_def))

%splice_t[tgt16] (generate_derivation "tgt16" (`Examples.callback_return'))
let _ = assert (tgt16 #empty == test_callback_return' ()) by (trefl ())

%splice_t[tgt_pair_of_functions] (generate_derivation "tgt_pair_of_functions" (`Examples.pair_of_functions))
[@@ (preprocess_with simplify_qType)]
let test () = assert (tgt_pair_of_functions #empty == test_pair_of_functions ()) by (trefl ())

%splice_t[tgt_io_return] (generate_derivation "tgt_io_return" (`ExamplesIO.u_return))
%splice_t[tgt_apply_io_return] (generate_derivation "tgt_apply_io_return" (`ExamplesIO.apply_io_return))
%splice_t[tgt_apply_read] (generate_derivation "tgt_apply_read" (`ExamplesIO.apply_read))
%splice_t[tgt_apply_write_const] (generate_derivation "tgt_apply_write_const" (`ExamplesIO.apply_write_const))
%splice_t[tgt_apply_write] (generate_derivation "tgt_apply_write" (`ExamplesIO.apply_write))
%splice_t[tgt_apply_io_bind_const] (generate_derivation "tgt_apply_io_bind_const" (`ExamplesIO.apply_io_bind_const))
%splice_t[tgt_apply_io_bind_identity] (generate_derivation "tgt_apply_io_bind_identity" (`ExamplesIO.apply_io_bind_identity))
let _ = assert (tgt_apply_io_bind_identity #empty == test_apply_io_bind_identity) by (trefl ())

%splice_t[tgt_apply_io_bind_pure_if] (generate_derivation "tgt_apply_io_bind_pure_if" (`ExamplesIO.apply_io_bind_pure_if))
let _ = assert (tgt_apply_io_bind_pure_if #empty == test_apply_io_bind_pure_if ()) by (trefl ())

%splice_t[tgt_apply_io_bind_write] (generate_derivation "tgt_apply_io_bind_write" (`ExamplesIO.apply_io_bind_write))
let _ = assert (tgt_apply_io_bind_write #empty == test_apply_io_bind_write) by (trefl ())

%splice_t[tgt_apply_io_bind_read_write] (generate_derivation "tgt_apply_io_bind_read_write" (`ExamplesIO.apply_io_bind_read_write))
let _ = assert (tgt_apply_io_bind_read_write #empty == test_apply_io_bind_read_write ()) by (trefl ())

%splice_t[tgt_apply_io_bind_read_write' ] (generate_derivation "tgt_apply_io_bind_read_write'" (`ExamplesIO.apply_io_bind_read_write'))
let _ = assert (tgt_apply_io_bind_read_write' #empty == test_apply_io_bind_read_write' ()) by (trefl ())

%splice_t[tgt_apply_io_bind_read_if_write] (generate_derivation "tgt_apply_io_bind_read_if_write" (`ExamplesIO.apply_io_bind_read_if_write))
let _ = assert (tgt_apply_io_bind_read_if_write #empty == test_apply_io_bind_read_if_write ()) by (trefl ())


%splice_t[tgt_sendError400] (generate_derivation "tgt_sendError400" (`ExamplesIO.sendError400))
%splice_t[tgt_get_req] (generate_derivation "tgt_get_req" (`ExamplesIO.get_req))

%splice_t[tgt_open2_read_write] (generate_derivation "tgt_open2_read_write" (`ExamplesIO.open2_read_write))
