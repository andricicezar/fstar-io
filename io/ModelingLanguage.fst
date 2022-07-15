module ModelingLanguage

open Free
open IO
open IO.Sig
open TC.Monitorable.Hist
open IIO

(* TODO: our monad also needs a way to represent failure,
         or is it enough to have it in actions? *)
noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
}

type acts (mon:monad) = op:io_cmds -> arg:io_sig.args op -> mon.m (io_sig.res op arg)

//type mon_bind (mon:monad) = #a:Type u#a -> #b:Type u#b -> mon.m a -> (a -> mon.m b) -> mon.m b

val free : monad
let free = { m = iio; ret = iio_return; }

let pi_type = monitorable_prop

noeq
type interface = {
  pi : pi_type;
  ictx_in : Type u#a;
  ictx_out : Type u#b;
  iprog_out : Type u#c; 

  ctx_in : Type u#a;
  ctx_out : Type u#b;
  prog_out : Type u#c; 
}

(** *** Intermediate Lang **)
type ictx (i:interface) = x:i.ictx_in -> ILang.IIOpi i.ictx_out i.pi
type iprog (i:interface) = ictx i -> ILang.IIOpi i.iprog_out i.pi
type iwhole (i:interface) = unit -> ILang.IIOpi i.iprog_out i.pi
let ilink (i:interface) (ip:iprog i) (ic:ictx i) : iwhole i = fun () -> ip ic

(** *** Target Lang **)
(* will eventually need a signature and what not;
   I think we need to pass the abstract monad inside is we want to support higher-order types.
   in this case I conflated alpha + beta = ct, and gamma + delta = pt *)
type ct (i:interface) (mon:monad) = i.ctx_in -> mon.m i.ctx_out
type pt (i:interface) (mon:monad) = mon.m i.prog_out 

type ctx (i:interface) = mon:monad -> acts mon -> ct i mon
type prog (i:interface) = ctx i -> pt i free

type whole (i:interface) (mon:monad) = unit -> pt i mon
let link (i:interface) (p:prog i) (c:ctx i) : whole i free = fun () -> p c

(* TODO: these should be replaced by typeclasses *)
assume val backtranslate' : (i:interface) -> i.ctx_out -> i.ictx_out
assume val compile' : (i:interface) -> i.ictx_in -> i.ctx_in
assume val compile'' : (i:interface) -> i.iprog_out -> i.prog_out

(** *** Backtranslate **)
assume val wrap : pi_type -> acts free -> acts free

(* TODO: the wrap does not have the intended effect *)
val backtranslate : (i:interface) -> ctx i -> acts free -> ictx i
let backtranslate i c (ca:acts free) (x:i.ictx_in) : ILang.IIOpi i.ictx_out i.pi =
  let c : ct i free = c free (wrap i.pi ca) in
  let tree : iio i.ctx_out = c (compile' i x) in
  assume (tree `has_type` dm_iio i.ctx_out (ILang.pi_hist i.ctx_out i.pi)); 
  let dm_tree : dm_iio i.ctx_out (ILang.pi_hist i.ctx_out i.pi) = tree in
  let r : i.ctx_out = IIOwp?.reflect dm_tree in
  backtranslate' i r

(* Case 1: We want to backtranslate a first order context. It should be rather simple to 
do that **)

(* Case 2: We want to backtranslate a higher order context. **)

(* now we can better write backtranslate; TODO: but to typecheck it we need parametricity? *)


(** *** Compilation **)
let compile (i:interface) (ip:iprog i) (ca:acts free) : prog i = 
  fun (c:ctx i) -> 
    let tree : dm_iio i.iprog_out (ILang.pi_hist _ i.pi) = 
      reify (ip (backtranslate i c ca)) in
    iio_bind tree (fun x -> free.ret (compile'' i x))

(** *** soundness *)
(* forall ip c pi. compile ip `link pi` c ~> t => t \in pi *)

(* Example:
   ct free.m = alpha -> free.m beta
   ictx for this = alpha -> IIO beta pi
*)


(** *** Transparency **)
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

assume val alpha : Type0
assume val beta : Type0
(* let bt (pi:...) (f : (alpha -> free.m beta)) (a:alpha) : IIO beta pi = *)
(*   IIO?.reflect (f a) (\* TODO: but how do he get that pi holds, if we can get actions that weren't wrapped, as done in link_no_check! *\) *)

(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)


val free_acts : acts free
(** CA: I can not reify here an IO computation because there is no way to prove the pre-condition **)
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg

assume val check_get_trace : pi_type -> cmd:io_cmds -> io_sig.args cmd -> free.m bool
(** CA: I would like this to be obtained by reifing the compilation of the IO primitives.
A solution will be to reify IIO.Primitives.dynamic_call.
Otherwise, we can implement it again here and show equivalence between this 
implenetation and the compilation **)
let wrapped_acts (pi:pi_type) : acts free = 
  fun cmd arg ->
    iio_bind
      (check_get_trace pi cmd arg)
      (fun b -> if b then free_acts cmd arg else free.ret #(io_sig.res cmd arg) (Inr Common.Contract_failure))
