module StaticQuote

open FStar.Tactics.V2

(**
   We simplified the problem, we're looking at 
   expressions, and the compiler computes the expression.
   We'll also add a translation between two "shallow embeddings".
**)

(** helper **)
let int_to_term (n:int) : term = 
  pack (Tv_Const (C_Int n))

(** this should be replaced by something in FStar.Reflection.Typing **)
assume val holds : term -> Tot Type0

assume val compile_eval : tm:term -> Tac (n:int & (holds (`(`#tm == `#(int_to_term n)))))

let p1_s : int = 1 + 2 + 3

(** fails because compile_eval is not implemented **)
[@expect_failure]
let p1_t : int = _ by (
  let v = compile_eval (`p1_s) in
  let vt = int_to_term (dfst v) in
  exact vt)

(** just a sketch for now, but we should also be able to get the proof **)
[@expect_failure]
let p1_proof : squash (p1_s == p1_t) = _ by (
  let v = compile_eval (`p1_s) in
  let vt = (dsnd v) in
  exact vt)
