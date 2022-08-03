module ModelingLanguage

noeq type monad = {
  m : Type -> Type;
  ret : #a:Type -> a -> m a
}

noeq type acts (mon:monad) = {
  read : string -> mon.m (option string);
}
(* TODO: our monad also needs a way to represent failure,
         or is it enough to have it in actions? *)

(* will eventually need a signature and what not;
   I think we need to pass the abstract monad inside is we want to support higher-order types.
   in this case I conflated alpha + beta = ct, and gamma + delta = pt *)
assume val ct : (m:Type->Type) -> Type0
assume val pt : (m:Type->Type) -> Type0

let ctx : Type = mon:monad -> acts mon -> ct mon.m

assume val free : monad

let prog : Type = ctx -> pt free.m

let stuff = string (* TODO: cheating, to be fixed later *)
assume val pi_type : Type0
assume val check_get_trace : stuff -> pi_type -> free.m bool
assume val bind_free : #a:Type -> #b:Type -> free.m a -> (a -> free.m b) -> free.m b

let whole : Type = pt free.m

assume val free_acts : acts free

(* TODO: wrapper should probably take a pi *)
let wrapped_acts (pi:pi_type) : acts free = {
  read = fun s ->
    bind_free (check_get_trace s pi) (fun b -> if b then free_acts.read s else free.ret None)
}

let link (p:prog) (c:ctx) : whole = p c

(** *** Transparency **)
(* Attempt 1 *)
(* forall p c pi. link_no_check p c ~> t /\ t \in pi => link p c ~> t *)
(* let link_no_check (p:prog) (c:ctx) : whole = p (c free free_acts) -- TODO: can't write this any more *)
(* CA: we can not write this because p expects a `c` instrumented with `pi` *)

(* Attempt 2 *)
(* we lose connection between p and ip ... so in the next attempts we take p = compile ip *)
(* forall p c pi. link p c ~> t /\ t \in pi => exists ip. link (compile ip) c ~> t *)

(* Attempt 3 *)
(* switch to my version of transparency? -- TODO needs ccompile and that's not easy because ctx has abstract mon *)
(* forall ip ic pi. ilink ip ic ~> t [/\ t \in pi] => link (compile pi ip) (ccompile ic) ~> t *)
(* let ccompile (ic:ictx) : ctx = fun (mon:monad) (a:acts) (x:alpha) -> (ccompile (reify (ic (backtranslate x)))) <: ct mon.m *)
(* we again need type classes, by example:
   ct mon.m = alpha -> mon.m beta
   ictx for this = alpha -> IIO beta pi
   where backtranslatable alpha and compilable beta are typeclass constraints
*)

(* Attempt 4 *)
(* new idea, fixed to account for the fact that certain things checked by wrapped_acts are not in pi: *)
(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)
(* CA: `ip` expects a `c` instrumented with `pi`, thus, we can not state transparency like this without 
       relaxing the input type of `ip`, thus, this has the same problem as the first attempt of transparency *)

assume val ictx : Type0
assume val iwhole : Type0
let iprog : Type0 = ictx -> iwhole
(* TODO: this needs to be/include IIO pi arrow; which may bring back reification? in compile_whole? on the argument of compile_whole? *)

(* TODO: these will need to be type-classes depending on structure of ct and pt *)
assume val backtranslate : ct free.m -> ictx
assume val compile_whole : iwhole -> pt free.m

let compile (ip:iprog) (ca:acts free) : prog = fun (c:ctx) -> compile_whole (ip (backtranslate (c free ca)))


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
