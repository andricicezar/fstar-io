module QuoteExtract

open FStar.Tactics.V2

type progS = int -> Pure int True (fun r -> r == 0)
type progT = term // term is just syntax...

type ctxS = int
type ctxT = term

type wholeS = unit -> Pure int True (fun r -> r == 0)
type wholeT = term


type linkS (ps:progS) (cs:ctxS) : wholeS = fun () -> ps cs
type linkT (pt:progT) (ct:ctxT) : wholeT = Tv_App pt (ct, Q_Explicit)

(** *** Looking at soundness **)
assume val beh_t : wholeT -> (int -> Type0)

(** Fails because quote is in the Tac effect **)
[@expect_failure]
let soudness_ideal : Type0 =
  forall (ps:progS) (ct:ctxT).
     forall res. beh_t (linkT (quote ps) ct) res ==> res == 0
(** res == 0 is the post-condition of progS **)

(** Assuming that compilation gives us a refinement on the result that
    relates the source and target program, then we can state soundness
    like this: **)
let soudness (rel:progS -> progT -> Type0) : Type0 =
  forall (ps:progS) (ct:ctxT).
    (** CA: I think quantifying pt with a forall is the correct thing to do,
        since quote is partial (because of Tac). Also, if it is an exists, then
        one cannot provide a witness by using quote (again, because of Tac).
        
        However, because of the forall, we have to show that the assumption is not 
        a contradiction, which will make the entire theorem trivial.
        We need a proof that for a source program, there is at least a target program
        in relation with it. **)
    forall (pt:progT). ps `rel` pt ==>
      (forall res. beh_t (linkT pt ct) res ==> res == 0)

(** beh_t should pick up the spec of ps **)
(** One could define rel, using the `validity` predicate from 
    FStar.Reflection.Typing, that allows us to reason about terms
    at the value level. However, validity needs an environment.

    A strong rel would be:
      rel (g:env) ps pt = validity g (eq2 ps pt)
      
    Funny enough, one could not look at ps and still prove soundness:
      rel (g:env) _ pt = validity g (has_type pt progS)
**)

assume val beh_s : wholeS -> (int -> Type0)

let wcc (rel:wholeS -> wholeT -> Type0) : Type0 =
  forall (ws:wholeS).
    forall (wt:wholeT). ws `rel` wt ==>
      (forall res. beh_s ws res <==> beh_t wt res)

(** for wcc ^, one cannot use any hacks in defining beh_t.
    Also, beh_s unfolds to `beh_s0 (reify ws)`, so 
    this is very hard to prove.
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

    
