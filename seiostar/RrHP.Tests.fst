module RrHP.Tests

open FStar.Tactics.V1

open LambdaIO
open IOStar
open QTypes.OpenValComp
open RQ.TypingRelation
open Compilation
open RrHP
open ExamplesIO
open RQ.TypingRelation.Tests

let i_unit : intS = { ct = qUnit }
let i_bool : intS = { ct = qBool }

(** Tactic that unfolds a [d_test_*] triple far enough to expose the
    top-level [QLambdaIO] constructor, so [QLambdaIO? qs._3] reduces to [true]. *)
let unfold_qLambdaIO (d_test:string) (test:string) : Tac unit =
  norm [delta_only [
          d_test; test;
          `%mk_turniqet; `%mk_dturniqet;
          `%Mkdtuple2?._1; `%Mkdtuple2?._2;
          `%FStar.Pervasives.dfst; `%FStar.Pervasives.dsnd;
          `%Mkdtuple3?._3];
        zeta; iota]

(** Test 1: u_return — `() -> io bool` returning `true`. *)
let ps_u_return () : Tot (progS i_unit) =
  let qs = d_test_u_return () in
  assert (QLambdaIO? qs._3)
    by (unfold_qLambdaIO (`%d_test_u_return) (`%test_u_return));
  (| u_return, qs |)

(** Test 2: apply_io_return — `b -> io b` *)
let ps_apply_io_return () : Tot (progS i_bool) =
  let qs = d_test_apply_io_return () in
  assert (QLambdaIO? qs._3)
    by (unfold_qLambdaIO (`%d_test_apply_io_return) (`%test_apply_io_return));
  (| apply_io_return, qs |)

(** Test 3: apply_io_bind_const — `() -> io bool` with bind *)
let ps_apply_io_bind_const () : Tot (progS i_unit) =
  let qs = d_test_apply_io_bind_const () in
  assert (QLambdaIO? qs._3)
    by (unfold_qLambdaIO (`%d_test_apply_io_bind_const) (`%test_apply_io_bind_const));
  (| apply_io_bind_const, qs |)

(** Test 4: apply_io_bind_identity — `b -> io b` via bind *)
let ps_apply_io_bind_identity () : Tot (progS i_bool) =
  let qs = d_test_apply_io_bind_identity () in
  assert (QLambdaIO? qs._3)
    by (unfold_qLambdaIO (`%d_test_apply_io_bind_identity) (`%test_apply_io_bind_identity));
  (| apply_io_bind_identity, qs |)

(** Test 5: apply_io_bind_pure_if — `b -> io b` using if!@ *)
let ps_apply_io_bind_pure_if () : Tot (progS i_bool) =
  let qs = d_test_apply_io_bind_pure_if () in
  assert (QLambdaIO? qs._3)
    by (unfold_qLambdaIO (`%d_test_apply_io_bind_pure_if) (`%test_apply_io_bind_pure_if));
  (| apply_io_bind_pure_if, qs |)

(** Compiling each program through the compiler model *)
let compiled_u_return : progT (comp_int i_unit) = compile_prog (ps_u_return ())
let compiled_apply_io_return : progT (comp_int i_bool) = compile_prog (ps_apply_io_return ())
let compiled_apply_io_bind_const : progT (comp_int i_unit) = compile_prog (ps_apply_io_bind_const ())
let compiled_apply_io_bind_identity : progT (comp_int i_bool) = compile_prog (ps_apply_io_bind_identity ())
let compiled_apply_io_bind_pure_if : progT (comp_int i_bool) = compile_prog (ps_apply_io_bind_pure_if ())

(** RrHP applies to each instantiation *)
let rrhp_u_return : squash (rrhp i_unit) = proof_rrhp_1 i_unit; rrhp_1_implies_rrhp i_unit
let rrhp_apply_io_return : squash (rrhp i_bool) = proof_rrhp_1 i_bool; rrhp_1_implies_rrhp i_bool

(** Additional examples from ExamplesIORefinements.

    These programs do not fit the strict [progS i] shape (whose return type is
    hard-coded to [qBool]):
    - [io_ghost_seq]    : [(qUnit ^-> qUnitR q_ref) ^->!@ qUnitR q_ref]
    - [pure_validate]   : pure [^->] arrow, not [^->!@], and [qResexn (qStringR valid)] return
    - [io_ifbang_ref]   : [qBool ^->!@ qBoolR (fun y -> y == true)]

    We still reuse the [⊫] triples from [RQ.TypingRelation.Tests] and exercise
    the compiler on their typing derivations. *)

let triple_io_ifbang_ref () : Tot (_ ⊫ _) by (simplify_d ()) = d_test_ior_io_ifbang_ref ()
let compiled_io_ifbang_ref : exp = compile (triple_io_ifbang_ref ())._3

let triple_pure_validate () : Tot (_ ⊫ _) by (simplify_d ()) = d_test_ior_pure_validate ()
let compiled_pure_validate : exp = compile (triple_pure_validate ())._3
