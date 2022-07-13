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

let prog : Type = mon:monad -> a:acts mon -> ct mon.m -> pt mon.m

assume val free : monad
let stuff = string (* TODO: cheating, to be fixed later *)
assume val check_get_trace : stuff -> free.m bool
assume val bind_free : #a:Type -> #b:Type -> free.m a -> (a -> free.m b) -> free.m b

let whole : Type = pt free.m

assume val free_acts : acts free

(* TODO: wrapper should probably take a pi *)
let wrapped_acts : acts free = {
  read = fun s ->
    bind_free (check_get_trace s) (fun b -> if b then free_acts.read s else free.ret None)
}

let link (p:prog) (c:ctx) : whole = (p free free_acts (c free wrapped_acts))

(* used to state transparency *)
(* forall p c pi. link_no_check p c ~> t /\ t \in pi => link p c ~> t *)
let link_no_check (p:prog) (c:ctx) : whole = (p free free_acts (c free free_acts))

assume val ictx : Type0
assume val iwhole : Type0
let iprog : Type0 = ictx -> iwhole
(* TODO: this needs to be/include IIO pi arrow; which may bring back reification? in compile_whole? on the argument of compile_whole? *)

assume val backtranslate (mon:monad) : ct mon.m -> ictx
assume val compile_whole (mon:monad) : iwhole -> pt mon.m

let compile (p:iprog) : prog = fun mon a c -> compile_whole mon (p (backtranslate mon c))




(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)
