module QuoteExtract

open FStar.Tactics.V2

type progS = int -> Pure int True (fun r -> r == 0)
type progT = term

(** *** Looking at soundness **)
assume val beh_t : term -> (int -> Type0)

(** Fails because quote is in the Tac effect **)
[@expect_failure]
let soudness_ideal : Type0 =
  forall (ps:progS) (cs:term).
     forall res. beh_t (Tv_App (quote ps) (cs, Q_Explicit)) res ==> res == 0
(** res == 0 is the post-condition of progS **)

(** Assuming that compilation gives us a refinement on the result that
    relates the source and target program, then we can state soundness
    like this: **)
let soudness (rel:progS -> progT -> Type0) : Type0 =
  forall (ps:progS) (cs:term).
    exists (pt:progT). ps `rel` pt /\
      (forall res. beh_t (Tv_App pt (cs, Q_Explicit)) res ==> res == 0)

(** beh_t should pick up the spec of pt **)
(** One could define rel, using the `validity` predicate from 
    FStar.Reflection.Typing, that allows us to reason about terms
    at the value level. However, this depends on the environment.

    A strong rel would be:
      rel (g:env) ps pt = validity g (eq2 ps pt)
      
    Funny enough, one could write one that does not look at ps and still prove soundness:
      rel (g:env) ps pt = validity g (has_type pt progS)
**)

(** *** Playing with tactics **)
val pretty_print : term -> Tac unit 
let pretty_print t =
  print (term_to_string t)

val compile0 : env -> string -> Tac progT
let compile0 e fnm =
  let f : term = string_to_term e fnm in
  let t : term = norm_term_env e [delta_only [fnm]] f in
  t

val compile1 : progS -> Tac progT
let compile1 ps =
  let f : term = quote ps in
  // TODO: one has to unfold the definition of ps, because f == Tv_FVar fv
  // let t : term = norm_term_env e [delta_only [`%ps]] f in
  f

(** CA: it seems that t_exact needs the syntax ...
val compile2 : env -> string -> progT
let compile2 e fnm =
  _ by (t_exact false true (compile0 e fnm))
**)

let fS (x:int) : int = x + 5

let fT : progT =
  _ by (
    let f = compile0 (top_env ()) "QuoteExtract.fS" in
    pretty_print f;
    t_exact true false (quote f))

val bfS : int -> int
let bfS =
  _ by (
    t_exact true false fT)

(** The definition of bfS extracts to:
    let (bfS : Prims.int -> Prims.int) = fun x -> x + (Prims.of_int (5))
  **)

let lemma () : Lemma (forall x. fS x == bfS x) = ()

val backtranslate : progT -> Tac progS
let backtranslate pt =
  FStar.Tactics.V2.Builtins.unquote pt

(** WOAW, no verification is going on **)
let xev () : Tac progS = 
  backtranslate (`"asd")

    
