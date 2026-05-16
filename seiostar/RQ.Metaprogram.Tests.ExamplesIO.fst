module RQ.Metaprogram.Tests.ExamplesIO

open FStar.Tactics
open IOStar
open RQ.TypingRelation
open RQ.TypingRelation.Tests
open RQ.Metaprogram
open QTypes.HelperTactics

open ExamplesIO

%splice_t[tgt_io_return] (generate_derivation "tgt_io_return" (`u_return))
%splice_t[tgt_apply_io_return] (generate_derivation "tgt_apply_io_return" (`apply_io_return))
%splice_t[tgt_apply_read] (generate_derivation "tgt_apply_read" (`apply_read))
%splice_t[tgt_apply_write_const] (generate_derivation "tgt_apply_write_const" (`apply_write_const))
%splice_t[tgt_apply_write] (generate_derivation "tgt_apply_write" (`apply_write))

%splice_t[tgt_apply_io_bind_const] (generate_derivation "tgt_apply_io_bind_const" (`apply_io_bind_const))
%splice_t[tgt_apply_io_bind_identity] (generate_derivation "tgt_apply_io_bind_identity" (`apply_io_bind_identity))
%splice_t[tgt_apply_io_bind_pure_if] (generate_derivation "tgt_apply_io_bind_pure_if" (`apply_io_bind_pure_if))
%splice_t[tgt_apply_io_bind_write] (generate_derivation "tgt_apply_io_bind_write" (`apply_io_bind_write))
%splice_t[tgt_apply_io_bind_read_write] (generate_derivation "tgt_apply_io_bind_read_write" (`apply_io_bind_read_write))
%splice_t[tgt_apply_io_bind_read_write'] (generate_derivation "tgt_apply_io_bind_read_write'" (`apply_io_bind_read_write'))
%splice_t[tgt_apply_io_bind_read_if_write] (generate_derivation "tgt_apply_io_bind_read_if_write" (`apply_io_bind_read_if_write))

%splice_t[tgt_open2_read_write] (generate_derivation "tgt_open2_read_write" (`open2_read_write))
%splice_t[tgt_sendError400] (generate_derivation "tgt_sendError400" (`sendError400))
%splice_t[tgt_get_req] (generate_derivation "tgt_get_req" (`get_req))

let hocf (agent:bool -> bool -> bool -> bool -> bool -> io bool) : io bool =
  agent true false false true true

%splice_t[tgt_f] (generate_derivation "tgt_f" (`hocf))
