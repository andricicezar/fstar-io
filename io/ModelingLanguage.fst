module ModelingLanguage

open Free
open IO
open IO.Sig
open TC.Monitorable.Hist
open IIO
open ILang

noeq type monad = {
  m : Type u#a -> Type u#(max 1 a);
  cmds : Type;
  sig : op_sig cmds;
  ret : #a:Type -> a -> m a
}

type acts (mon:monad) = op:mon.cmds -> arg:mon.sig.args op -> mon.m (mon.sig.res op arg)

(* TODO: our monad also needs a way to represent failure,
         or is it enough to have it in actions? *)

(* will eventually need a signature and what not;
   I think we need to pass the abstract monad inside is we want to support higher-order types.
   in this case I conflated alpha + beta = ct, and gamma + delta = pt *)
assume val ct : (m:Type->Type) -> Type0
assume val pt : (m:Type->Type) -> Type0

let ctx : Type = mon:monad -> acts mon -> ct mon.m

val free : monad
let free = {
  m = iio;
  cmds = io_cmds;
  sig = io_sig;
  ret = iio_return;
}

let prog : Type = ctx -> pt free.m

let stuff = string (* TODO: cheating, to be fixed later *)
let  pi_type = monitorable_prop
assume val check_get_trace : pi_type -> cmd:io_cmds -> io_sig.args cmd -> free.m bool
assume val bind_free : #a:Type -> #b:Type -> free.m a -> (a -> free.m b) -> free.m b

let whole : Type = pt free.m

val free_acts : acts free
(** CA: I can not reify here an IO computation because there is no way to prove the pre-condition **)
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg

(** CA: I would like this to be obtained by reifing the compilation of the IO primitives.
A solution will be to reify IIO.Primitives.dynamic_call.
Otherwise, we can implement it again here and show equivalence between this 
implenetation and the compilation **)
let wrapped_acts (pi:pi_type) : acts free = 
  fun cmd arg ->
    bind_free
      (check_get_trace pi cmd arg)
      (fun b -> if b then free_acts cmd arg else free.ret #(io_sig.res cmd arg) (Inr Common.Contract_failure))

let link (p:prog) (c:ctx) : whole = p c

(* used to state transparency *)
(* forall p c pi. link_no_check p c ~> t /\ t \in pi => link p c ~> t *)
(* let link_no_check (p:prog) (c:ctx) : whole = p (c free free_acts) -- TODO: can't write this any more *)

(* new attempt -- but we lose connection between p and ip ... so in the next attempts we take p = compile ip *)
(* forall p c pi. link p c ~> t /\ t \in pi => exists ip. link (compile ip) c ~> t *)

(* switch to my version of transparency? -- TODO needs ccompile and that's not easy because ctx has abstract mon *)
(* forall ip ic pi. ilink ip ic ~> t [/\ t \in pi] => link (compile pi ip) (ccompile ic) ~> t *)
(* let ccompile (ic:ictx) : ctx = fun (mon:monad) (a:acts) (x:alpha) -> (ccompile (reify (ic (backtranslate x)))) <: ct mon.m *)
(* we again need type classes, by example:
   ct mon.m = alpha -> mon.m beta
   ictx for this = alpha -> IIO beta pi
   where backtranslatable alpha and compilable beta are typeclass constraints
*)

(* new idea, fixed to account for the fact that certain things checked by wrapped_acts are not in pi: *)
(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)

noeq
type interface = {
  pi : pi_type;
  ctx_in : Type;
  ctx_out : Type;
  prog_out : Type; 
}

let ictx (i:interface) = x:i.ctx_in -> IIOpi i.ctx_out i.pi
let iwhole (i:interface) = unit -> IIOpi i.prog_out i.pi

let iprog (i:interface) = ictx i -> iwhole i
(* TODO: this needs to be/include IIO pi arrow; which may bring back reification? in compile_whole? on the argument of compile_whole? *)

(* TODO: these will need to be type-classes depending on structure of ct and pt *)
assume val backtranslate : (#i:interface) -> ct free.m -> ictx i

val compile_whole : (#i:interface) -> iwhole i -> pt free.m
let compile_whole #i w call_cmd () : iio i.prog_out =
  admit ()

let compile (i:interface) (ip:iprog i) (ca:acts free) : prog = fun (c:ctx) -> compile_whole (ip (backtranslate (c free ca)))


(* now we can better write backtranslate; TODO: but to typecheck it we need parametricity? *)

(* soundness *)
(* forall ip c pi. compile ip `link pi` c ~> t => t \in pi *)

(* Example:
   ct free.m = alpha -> free.m beta
   ictx for this = alpha -> IIO beta pi
*)

assume val alpha : Type0
assume val beta : Type0
(* let bt (pi:...) (f : (alpha -> free.m beta)) (a:alpha) : IIO beta pi = *)
(*   IIO?.reflect (f a) (\* TODO: but how do he get that pi holds, if we can get actions that weren't wrapped, as done in link_no_check! *\) *)

(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)
