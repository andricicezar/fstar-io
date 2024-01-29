module CriteriaStatic

(** *** Intrinsic criteria, static quoting/unquoting  **)

type set_prop = int -> Type0
let (⊆) (s0 s1:set_prop) : Type0 = forall res. s0 res ==> s1 res
let (≡) (s0 s1:set_prop) : Type0 = forall res. s0 res <==> s1 res

noeq type intS = { ct : Type u#a; p_post : set_prop }

type progS (i:intS) = i.ct -> Pure int True i.p_post
type ctxS (i:intS) = i.ct
type wholeS = post:set_prop & (unit -> Pure int True post)

let linkS (#i:intS) (ps:progS i) (cs:ctxS i) : wholeS =
  (| i.p_post, (fun () -> ps cs) |)

assume type pure_repr
assume val reify' : (unit -> Pure int True (fun _ -> True)) -> pure_repr
assume val behS0 : pure_repr -> set_prop

val behS : wholeS -> set_prop 
let behS (| _, ws |) = behS0 (reify' ws)

(** Target **)
assume type ast_typ
assume type ast_exp
assume type ast_env
assume type ast_typing (g:ast_env) (a:ast_exp) (t:ast_typ)

noeq type intT = { ct : ast_typ; g : ast_env; }

assume val comp_int : intS u#a -> ast_env -> intT

// TODO: g does not appear hear
type progT (i:intT) = pt:ast_exp//{ast_typing i.g pt ...}
type ctxT (i:intT) = ct:ast_exp//{ast_typing i.g ct ...}
type wholeT = wt:ast_exp//{ast_typing i.g wt ...}

assume val linkT (#i:intT) (pt:progT i) (ct:ctxT i) : wholeT

assume val behT : wt:wholeT -> set_prop 

open FStar.Tactics.V2
open FStar.Reflection.V2
open FStar.Reflection.Typing
let mk_squash (phi:term) : Tot term = pack_ln (Tv_App (`squash) (phi, Q_Explicit))

let t_unit = `()

let valid (g:env) (phi:term) : prop =
  squash (tot_typing g t_unit (mk_squash phi))

// TODO: (`wholeS) elaborates to FVar, so we need to unfold that to get the type
val compile_whole_stat : 
  (g:env) ->
  (ws:term{tot_typing g ws (`wholeS)}) ->
  (g_ast : term{tot_typing g g_ast (`ast_env)}) ->
  Tac (wt:term{
    tot_typing g wt (`wholeT) /\
    (** compiler correctness **)
    valid g (`(behS (`#ws) ≡ behT (`#wt)))

    (** soundness **)
    // in this PoC, we cannot type this because whole programs do not have an interface
    // valid g (`(behT (`#wt) ⊆ i.p_post))
  })

let soundness (#i:intS) (#g_ast:ast_env) (pt:progT (comp_int i g_ast)) =
  forall (ct:ctxT (comp_int i g_ast)). behT (linkT pt ct) ⊆ i.p_post

(** The order of the quantifiers makes this RHC (Robust Hyperproperty Preservation) **)
(** TODO: why cannot we change the order of the quantifiers to have RrHC **)
let rhc (#i:intS) (#g_ast:ast_env) (ps:progS i) (pt:progT (comp_int i g_ast)) =
  forall (ct:ctxT (comp_int i g_ast)).
    exists (cs:ctxS i). behS (linkS ps cs) ≡ behT (linkT pt ct)

val compile_prog :
  (g:env) ->
  i:term{tot_typing g i (`intS)} ->
  ps:term{tot_typing g ps (`progS (`#i))} ->
  (g_ast : term{tot_typing g g_ast (`ast_env)}) ->
  Tac (pt:term{
    tot_typing g pt (`progT (comp_int (`#i) (`#g_ast))) /\

    (** soundness **)
    valid g (`(soundness (`#pt))) /\

    (** RHC **)
    valid g (`(rhc (`#ps) (`#pt)))
  })

  // Example of usage:
  // let i : intS = ...
  // let ps : progS i = ...
  // let g_ast : ast_env = ...

  //  %splice_t [pt;pt_sound;ps_pt_rhc] (compile_prog (`i) (`ps) (`g_ast))
  // // adds in environment the following:

  // let pt : progT (comp_int i g_ast) = ...
  // let pt_sound : squash (soundness pt) = ...
  // let ps_pt_rhc : squash (rhc ps pt) = ...