module ModelingLanguage

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot

open Free
open IO
open IO.Sig
open TC.Monitorable.Hist
open IIO

(* TODO: state properties: soundness, transparency, RTP **)

(* TODO : think about higher-order **)


(* TODO: our monad also needs a way to represent failure,
         or is it enough to have it in actions? *)
noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
}

type acts (mon:monad) = op:io_cmds -> arg:io_sig.args op -> mon.m (io_sig.res op arg)

//type mon_bind (mon:monad) = #a:Type u#a -> #b:Type u#b -> mon.m u#a a -> (a -> mon.m u#b b) -> mon.m u#b b

val free : monad
let free = { m = iio; ret = iio_return; }

let pi_type = monitorable_prop

noeq
type interface = {
  (* intermediate level *)
  ictx_in : Type u#a;
  ictx_out : Type u#a;
  iprog_out : Type u#a; 

  (* target level *)
  ctx_in : Type u#a;
  ctx_out : Type u#a;
  prog_out : Type u#a; 
}

//  vpi  : pi_type; (* the statically verified monitorable property (part of partial program's spec) *)
//  ipi : pi_type;  (* the instrumented monitorable property (part of context's spec) *)
type r_vpi_ipi (vpi ipi:pi_type) = squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt)

(** *** Intermediate Lang **)
type ictx (i:interface) (ipi:pi_type)   =  x:i.ictx_in -> ILang.IIOpi i.ictx_out ipi
type iprog (i:interface) (vpi:pi_type)  = (x:i.ictx_in -> ILang.IIOpi i.ictx_out vpi) -> ILang.IIOpi i.iprog_out vpi
type iwhole (i:interface) (vpi:pi_type) = unit -> ILang.IIOpi i.iprog_out vpi
let ilink 
  (i:interface) 
  (vpi ipi:pi_type) 
  (_ : r_vpi_ipi vpi ipi)
  (ip:iprog i vpi) 
  (ic:ictx i ipi) : 
  iwhole i vpi = 
  fun () -> ip ic

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


(** *** Parametricity **)
noeq
type monad_p (mon:monad) = {
  m_p : a:Type -> a_p:(a -> Type) -> x:(mon.m a) -> Type;
  ret_p : a:Type -> a_p:(a -> Type) -> (x:a) -> x_p:(a_p x) -> Lemma (m_p a a_p (mon.ret x));
}

(* TODO: *)
[@@ "opaque_to_smt"]
type io_cmds_p (cmd:io_cmds) =
  True

(* TODO: *)
[@@ "opaque_to_smt"]
type io_sig_args_p (op:io_cmds) (arg:io_sig.args op) =
  True

(* TODO: *)
[@@ "opaque_to_smt"]
type io_sig_res_p (op:io_cmds) (arg:io_sig.args op) (res:io_sig.res op arg) =
  True

type acts_p (mon:monad) (mon_p:monad_p mon) (theActs:acts mon) = 
  op:io_cmds -> op_p : (io_cmds_p op) -> 
  arg:io_sig.args op -> arg_p : (io_sig_args_p op arg) ->
  Lemma (mon_p.m_p (io_sig.res op arg) (io_sig_res_p op arg) (theActs op arg))

(* TODO: check if we need parametricity for the interface **)
type ct_p (i:interface) (mon:monad) (mon_p:monad_p mon) (c:ct i mon) =
  squash (forall x. mon_p.m_p i.ctx_out (fun x -> True) (c x))

type ctx_p (i:interface) (mon:monad) (mon_p:monad_p mon) (theActs:acts mon) (theActs_p:acts_p mon mon_p theActs) (c:ctx i) =
  ct_p i mon mon_p (c mon theActs)

(* TODO: check with others **)
(* Parametricity Assumption about the Context **)
assume val ctx_param : 
  (i:interface) ->
  (mon:monad) -> (mon_p:monad_p mon) ->
  (theActs:acts mon) -> (theActs_p:acts_p mon mon_p theActs) ->
  (c:ctx i) -> 
  Lemma (ctx_p i mon mon_p theActs theActs_p c)

(** **** Parametricity - instances **)
let free_p (pi:monitorable_prop) : monad_p free = {
  m_p = (fun a a_p tree -> ILang.pi_hist #a pi `hist_ord` dm_iio_theta tree);
  ret_p = (fun a a_p tree tree_p -> ());
}

(** *** Backtranslate **)
unfold val check_get_trace : pi_type -> cmd:io_cmds -> io_sig.args cmd -> free.m bool
let check_get_trace pi cmd arg = 
  iio_bind (IO.Sig.Call.iio_call GetTrace ()) (fun h -> Return (pi cmd arg h))

val wrap : pi_type -> acts free -> acts free
let wrap pi theActs cmd arg =
  iio_bind
    (check_get_trace pi cmd arg)
    (fun b -> if b then theActs cmd arg else free.ret #(io_sig.res cmd arg) (Inr Common.Contract_failure))

let spec_free_acts (ca:acts free) =
  (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (ca cmd arg))

val wrap_p : (pi:monitorable_prop) -> (ca:(acts free){spec_free_acts ca}) -> acts_p free (free_p pi) (wrap pi ca)
let wrap_p pi ca (op:io_cmds) op_p (arg:io_sig.args op) arg_p : 
  Lemma ((free_p pi).m_p (io_sig.res op arg) (io_sig_res_p op arg) ((wrap pi ca) op arg)) = 
  assert (spec_free_acts ca);
  assert (iio_wps op arg `hist_ord` dm_iio_theta (ca op arg)) by (
    let lem = nth_binder 9 in
    let lem = instantiate lem (nth_binder 2) in
    let lem = instantiate lem (nth_binder 4) in
    assumption ()
  );
  introduce forall p h. ILang.pi_hist pi p h ==> dm_iio_theta ((wrap pi ca) op arg) p h with begin
    introduce ILang.pi_hist pi p h ==> dm_iio_theta ((wrap pi ca) op arg) p h with _. begin
 //     assume (pi op arg h ==> io_pre op arg h);
//      assert (iio_wps op arg p h ==> dm_iio_theta (ca op arg) p h);
//      assume (dm_iio_theta (ca op arg) p h);
//      assume (dm_iio_theta (ca op arg) (fun lt' r -> p lt' r) h);
      (** pi must imply iio_wps **)
      calc (==>) {
        if pi op arg h then
          (* TODO: I only have to prove this one *)
          dm_iio_theta (ca op arg) (fun lt' r -> p lt' r) h
        else 
          (* this branch is proved automatically *)
          dm_iio_theta (Return (Inr Common.Contract_failure)) (fun lt' r -> p lt' r) h;
        ==> { _ by (tadmit ()) (* should move theta in the if *) }
        dm_iio_theta (if pi op arg h then ca op arg
          else Return (Inr Common.Contract_failure))
        (fun lt' r -> p lt' r)
        h;
        == { _ by (
          norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift];zeta;iota];
          l_to_r [`List.Tot.Properties.append_nil_l]
        )}
        hist_bind
          (fun p h -> p [] (pi op arg h))
          (fun b -> dm_iio_theta (if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
          p h;
        == { _ by (compute ()) }
        hist_bind
          (dm_iio_theta (check_get_trace pi op arg))
          (fun b -> dm_iio_theta (if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
          p h;
        == { _ by (tadmit ()) (* monad morphism *) }
        dm_iio_theta (
  iio_bind
    (check_get_trace pi op arg)
    (fun b -> if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
         p h;
        == {}
        dm_iio_theta ((wrap pi ca) op arg) p h;
      };
      admit ()
    end
  end

(** **** Free Actions **)
val free_acts : acts free
(** CA: I can not reify here an IO computation because there is no way to prove the pre-condition **)
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg

let lemma_free_acts () : Lemma (spec_free_acts free_acts) = 
  assert (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (free_acts cmd arg));
  assert (spec_free_acts free_acts) by (assumption ())

val cast_to_dm_iio  : (i:interface) -> ipi:pi_type -> ctx i -> (x:i.ctx_in) -> dm_iio i.ctx_out (ILang.pi_hist ipi)
let cast_to_dm_iio i ipi c x : _ by (norm [delta_only [`%ctx_p;`%ct_p;`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  lemma_free_acts ();
  let c' : ct i free = c free (wrap ipi free_acts) in
  let tree : iio i.ctx_out = c' x in
  ctx_param i free (free_p ipi) (wrap ipi free_acts) (wrap_p ipi free_acts) c;
  assert (ILang.pi_hist ipi `hist_ord` dm_iio_theta tree);
  tree

val backtranslate : (i:interface) -> ipi:pi_type -> ctx i -> ictx i ipi
let backtranslate i ipi c (x:i.ictx_in) : ILang.IIOpi i.ictx_out ipi =
  let dm_tree : dm_iio i.ctx_out (ILang.pi_hist ipi) = cast_to_dm_iio i ipi c (compile' i x) in
  let r : i.ctx_out = IIOwp?.reflect dm_tree in
  backtranslate' i r

(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)

(** *** Compilation **)
assume val reify_IIOwp (#a:Type) (#wp:hist a) ($f:unit -> IIOwp a wp) : dm_iio a wp

[@@ "opaque_to_smt"]
let hack_compile  
  (#i:interface)
  (#vpi:pi_type)
  (ip:iprog i vpi)
  (ipi:pi_type)
  (#_: r_vpi_ipi vpi ipi) 
  (c:ctx i) :
  unit -> IIOwp i.iprog_out (ILang.pi_hist vpi) = 
  fun () -> ip (backtranslate i ipi c)

let compile
  (#i:interface)
  (#vpi:pi_type)
  (ip:iprog i vpi)
  (ipi:pi_type)
  (#_: r_vpi_ipi vpi ipi) :
  prog i = 
  fun (c:ctx i) -> 
    let f = hack_compile ip ipi c in
    let tree : dm_iio i.iprog_out (ILang.pi_hist vpi) = reify_IIOwp f in
    iio_bind tree (fun x -> free.ret (compile'' i x))

(** ** Theorems **)

(** *** Beh **)
let beh #a x (*:whole *) = dm_iio_theta #a (x ())

(* We verify specs of whole progrems, thus, instead of having
   properties forall histories, we can specialize it for the
   empty history *)
let included_in (wp:hist 'a) (pi:pi_type) =
  wp (fun lt r -> enforced_locally pi [] lt) []

(* TODO: not sure if this has the intended effect. It should be a 
   predicate that says that `t` is a possible trace of `wp` *)
let produces (wp:hist 'a) (t:trace) =
  forall p. wp p [] ==> (exists r. p t r)

let respects (t:trace) (pi:pi_type) =
  enforced_locally pi [] t

(** *** Soundness *)
let soundness (i:interface) (vpi:pi_type) (ip:iprog i vpi) (c:ctx i) : Type0 =
  lemma_free_acts ();
  beh (compile ip vpi `link i` c) `included_in` vpi
(* TODO: to prove this, one can add to compile a post-condition that guarantees this *)

let reveal_monotonicity (wp:hist 'a) : Lemma (hist_wp_monotonic wp) = ()
let reveal_wp (d:dm_iio 'a 'wp) : Lemma ('wp `hist_ord` dm_iio_theta d) = ()

let soundness_proof (i:interface) (vpi:pi_type) (ip:iprog i vpi) (c:ctx i) : Lemma (soundness i vpi ip c) = 
  let lhs : dm_iio i.iprog_out (ILang.pi_hist vpi) = reify_IIOwp (hack_compile ip vpi c) in
  let rhs = fun x -> Mkmonad?.ret free (compile'' i x) in
  let p1 : hist_post i.iprog_out = (fun lt _ -> enforced_locally vpi [] lt) in

  calc (==>) {
    dm_iio_theta lhs p1 [];
    ==> {  
      let p2 : hist_post i.iprog_out = 
      	(fun lt r ->
	   dm_iio_theta (Mkmonad?.ret free (compile'' i r))
	     (fun lt' (_:i.prog_out) -> enforced_locally vpi [] (lt @ lt'))
             (rev lt @ [])) in
      assert (forall h x. dm_iio_theta (rhs x) (fun lt _ -> lt == []) h);
      assert (forall h x. dm_iio_theta (rhs x) (fun lt _ -> enforced_locally vpi h lt) h);
      assert (p1 `hist_post_ord` p2);
      reveal_monotonicity (dm_iio_theta lhs)
    }
    dm_iio_theta 
       lhs
       (fun lt r ->
         dm_iio_theta (rhs r)
           (fun lt' _ -> enforced_locally vpi [] (lt @ lt'))
           (List.Tot.Base.rev lt @ []))
       [];
    == { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift]; iota]) }
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) (fun lt _ -> enforced_locally vpi [] lt) [];
    ==> { DMFree.lemma_theta_is_lax_morphism_bind iio_wps lhs rhs }
    dm_iio_theta 
       (iio_bind lhs rhs)
       (fun lt _ -> enforced_locally vpi [] lt)
       [];
    == {}
    dm_iio_theta 
       (iio_bind (reify_IIOwp (hack_compile ip vpi c))
                 (fun x -> Mkmonad?.ret free (compile'' i x)))
       (fun lt _ -> enforced_locally vpi [] lt)
       [];
    == { _ by (norm [delta_only [`%soundness;`%beh;`%link; `%included_in;`%compile]; iota]) }
    soundness i vpi ip c;
  }

(* Example:
   ct free.m = alpha -> free.m beta
   ictx for this = alpha -> IIO beta pi
*)

(** *** Transparency **)
(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)
(* we give an interface that has the true pi on the left, and our pi on the right *)
(* pi is part of the interface because the partial program uses it in its type in two places: input type and output type. *)
(* the pi in this theorem, has nothing to do with the pi we need *)

(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)
let true_pi : pi_type = fun _ _ _ -> true
      
let alles (ipi:pi_type) : (r_vpi_ipi true_pi ipi) =
  let rec alles_0 (ipi:pi_type) (h lt:trace) : 
    Lemma 
	(requires (enforced_locally ipi h lt))
	(ensures (enforced_locally true_pi h lt)) 
	(decreases lt) = begin
    match lt with
    | [] -> ()
    | hd::t -> alles_0 (ipi) (hd::h) t
  end in
  Classical.forall_intro_2 (Classical.move_requires_2 (alles_0 ipi))

let transparency (i:interface) (ip:iprog i true_pi) (c:ctx i) (t:trace) (ipi:pi_type) = squash (
  beh ((compile ip true_pi) `link i` c) `produces` t /\ t `respects` ipi ==>
    beh ((compile ip ipi #(alles ipi)) `link i` c) `produces` t)
(* ip:iprog i true_pi = the partial program has the trivial spec, thus, it produces any trace 
                        and accepts contexts that also produce any trace.
   compile ip true_pi = compilation gives to the context the free_acts wrapped with trivial checks
   compile ip ipi     = compilation gives to the context the free_acts wrapped with ipi 
   The trick of this statement is that we can instrument the context with any spec we want because the
   partial program accepts all of them. This is possible because a context must be instrumented with a pi
   stronger than the one used as spec for the partial program and all pis are stronger than the trivial pi. *)

(* we want to have two different pis. The one that the partial program expects, and the one that is enforced by instrumentation.
For transparency, the partial wants the true property, and then
we first instrument with true on the left and then instrument with psi. *)


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
