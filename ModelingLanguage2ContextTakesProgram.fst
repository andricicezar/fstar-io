module ModelingLanguage2ContextTakesProgram
(* Trying to swap program and context, as we did the first time we spoke about effect parametricity *)
(* This is just a thought exercise for now, since it would require changes to higher languages too *)
(* It's also unclear what the gain would be given that we now anyway try to support full higher-order *)

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

let prog : Type = mon:monad -> acts mon -> pt mon.m

let ctx : Type = mon:monad -> acts mon -> prog -> ct mon.m

assume val free : monad

let stuff = string (* TODO: cheating, to be fixed later *)
assume val pi_type : Type0
assume val check_get_trace : stuff -> pi_type -> free.m bool
assume val bind_free : #a:Type -> #b:Type -> free.m a -> (a -> free.m b) -> free.m b

let whole : Type = ct free.m

assume val free_acts : acts free

(* TODO: wrapper should probably take a pi *)

let wrapped_acts (pi:pi_type) : acts free = {
  read = fun s ->
    bind_free (check_get_trace s pi) (fun b -> if b then free_acts.read s else free.ret None)
}

let link (p:prog) (c:ctx) (pi:pi_type) : whole = c free (wrapped_acts pi) p

(* back to the original way to state transparency *)
(* forall p c pi. link_no_check p c ~> t /\ t \in pi => link p c pi ~> t *)
let link_no_check (p:prog) (c:ctx) : whole = c free free_acts p

(* new idea is now special case of the above? *)
(* forall ip c pi. link true (compile ip) c ~> t /\ t \in pi => link pi (compile ip) c ~> t *)
(* not equivalent! ... link_no_check (compile ip) c ... *)
(* `free_acts` is not equivalent to `wrapped_acts true`:
    certain things checked by wrapped_acts are not in pi!
    this means that this way of stating transparency is anyway not good enough! *)

(*** The rest of the file as before, still needs update *)



assume val ictx : Type0
assume val iwhole : Type0
let iprog : Type0 = ictx -> iwhole
(* TODO: this needs to be/include IIO pi arrow; which may bring back reification? in compile_whole? on the argument of compile_whole? *)

(* TODO: these will need to be type-classes depending on structure of ct and pt *)
assume val backtranslate : ct free.m -> ictx
assume val compile_whole : iwhole -> pt free.m

let compile (ip:iprog) : prog = fun (c:ctx) -> compile_whole (ip (backtranslate (c free wrapped_acts)))


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
