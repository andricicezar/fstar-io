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
