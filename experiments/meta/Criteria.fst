module Criteria

open FStar.Tactics.V2

type set_prop = int -> Type0
let (⊆) (s0 s1:set_prop) : Type0 = forall res. s0 res ==> s1 res
let (≍) (s0 s1:set_prop) : Type0 = forall res. s0 res <==> s1 res

noeq type intS = { ct : Type u#a; p_post : set_prop }
noeq type intT = { ct : Type u#a }

val comp_int : intS u#a -> intT u#a
let comp_int i = { ct = i.ct }

type progS (i:intS) = i.ct -> Pure int True i.p_post
type progT (i:intT) = term // term is just syntax...

type ctxS (i:intS) = i.ct
type ctxT (i:intT) = term

type wholeS = post:set_prop & (unit -> Pure int True post)
type wholeT = term

type linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (| i.p_post, (fun () -> ps cs) |)
type linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT =
  Tv_App pt (ct, Q_Explicit)

assume val behT : wholeT -> set_prop 

assume type pure_repr
assume val reify' : (unit -> Pure int True (fun _ -> True)) -> pure_repr
assume val behS0 : pure_repr -> set_prop

val behS : wholeS -> set_prop 
let behS (| _, ws |) = behS0 (reify' ws)

(** *** Looking at stating criteria extrinsically **)
(** Fails because quote is in the Tac effect **)
[@expect_failure]
let soudness_ideal : Type0 =
  forall i (ps:progS i) (ct:ctxT (comp_int i)).
     behT (linkT (quote ps) ct) ⊆ i.p_post

(** Assuming that compilation gives us a refinement on the result that
    relates the source and target program, then we can state soundness
    like this: **)
let soudness (rel:(#i:intS -> progS i -> progT (comp_int i) -> Type0)) : Type0 =
  forall i (ps:progS i) (ct:ctxT (comp_int i)).
    (** CA: I think quantifying pt with a forall is the correct thing to do,
        since quote is partial (because of Tac). Also, if it is an exists, then
        one cannot provide a witness by using quote (again, because of Tac).
        
        However, because of the forall, we have to show that the assumption is not 
        a contradiction, which will make the entire theorem trivial.
        We need a proof that for a source program, there is at least a target program
        in relation with it. **)
    forall (pt:progT (comp_int i)). ps `rel` pt ==>
      behT (linkT pt ct) ⊆ i.p_post

(** behT should pick up the spec of ps **)
(** One could define rel, using the `validity` predicate from 
    FStar.Reflection.Typing, that allows us to reason about terms
    at the value level. However, validity needs an environment.

    A strong rel would be:
      rel (g:env) ps pt = validity g (eq2 ps pt)
      
    Funny enough, one could not look at ps and still prove soundness:
      rel (g:env) _ pt = validity g (has_type pt progS)
**)

let wcc (rel:wholeS -> wholeT -> Type0) : Type0 =
  forall (ws:wholeS).
    forall (wt:wholeT). ws `rel` wt ==>
      behS ws ≍ behT wt

(** for wcc ^, one cannot use any hacks in defining behT.
    Also, behS unfolds to `behS0 (reify ws)`, so 
    this is very hard to prove.
**)

(** *** Looking at stating criteria intrinsically **)
val compile_whole : (ws:wholeS) -> Tac (wt:wholeT{
  (** compiler correctness **)
  behS ws ≍ behT wt 
})

val compile_prog_soundness : #i:intS -> ps:progS i -> Tac (pt:(progT (comp_int i)){
  (** soundness **)
  forall (ct:ctxT (comp_int i)). behT (linkT pt ct) ⊆ i.p_post 
  })

val compile_prog_rrhp :
  #i:intS ->
  ps:progS i ->
  rel:(ctxT (comp_int i) -> ctxS i -> Type0) ->
  Tac (pt:(progT (comp_int i)){
    (** TODO: the order of quantifiers changed **)
    forall (ct:ctxT (comp_int i)).
        exists (cs:ctxS i). 
        behT (linkT pt ct) ≍ behS (linkS ps cs) 
  })
  (** can one provide a witness for cs? **)

(** Problem: unqoute is in the Tac effect **)
[@expect_failure]
val compile_prog_rrhp : #i:intS -> ps:progS i -> Tac (pt:(progT (comp_int i)){
  (** RrHP **)
  forall (ct:ctxT (comp_int i)). 
    let cs : ctxS i = FStar.Tactics.V2.Builtins.unquote ct in
    behT (linkT pt ct) ≍ behS (linkS ps cs) 
  })
