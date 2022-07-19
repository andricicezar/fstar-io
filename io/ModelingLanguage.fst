module ModelingLanguage

open FStar.Classical.Sugar

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

  
// #set-options "--print_universes --detail_errors"

noeq
type interface = {
  vpi  : pi_type; (* the statically verified monitorable property (part of partial program's spec) *)
  ipi : pi_type;  (* the instrumented monitorable property (part of context's spec) *)

  (* intermediate level *)
  ictx_in : Type u#a;
  ictx_out : Type u#a;
  iprog_out : Type u#a; 

  (* target level *)
  ctx_in : Type u#a;
  ctx_out : Type u#a;
  prog_out : Type u#a; 

  (* props *)
  r_vpi_ipi : squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt);
}

open FStar.Tactics
  
(** *** Intermediate Lang **)
type ictx (i:interface) = x:i.ictx_in -> ILang.IIOpi i.ictx_out i.ipi
type iprog (i:interface) = (x:i.ictx_in -> ILang.IIOpi i.ictx_out i.vpi) -> ILang.IIOpi i.iprog_out i.vpi
type iwhole (i:interface) = unit -> ILang.IIOpi i.iprog_out i.vpi
let ilink (i:interface) (ip:iprog i) (ic:ictx i) : iwhole i = 
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

open FStar.Tactics

let spec_free_acts (ca:acts free) =
  squash (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (ca cmd arg))

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

(* TODO: remove passing of ca **)
val cast_to_dm_iio  : (i:interface) -> ctx i -> (ca:(acts free){spec_free_acts ca}) -> (x:i.ctx_in) -> dm_iio i.ctx_out (ILang.pi_hist #i.ctx_out i.ipi)
let cast_to_dm_iio i c ca x : _ by (norm [delta_only [`%ctx_p;`%ct_p;`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  let c' : ct i free = c free (wrap i.ipi ca) in
  let tree : iio i.ctx_out = c' x in
  ctx_param i free (free_p i.ipi) (wrap i.ipi ca) (wrap_p i.ipi ca) c;
  assert (ILang.pi_hist i.ipi `hist_ord` dm_iio_theta tree);
  tree

(* TODO: the wrap does not have the intended effect *)
val backtranslate : (i:interface) -> ctx i -> (ca:(acts free){spec_free_acts ca}) -> ictx i
let backtranslate i c ca (x:i.ictx_in) : ILang.IIOpi i.ictx_out i.ipi =
  let dm_tree : dm_iio i.ctx_out (ILang.pi_hist i.ipi) = cast_to_dm_iio i c ca (compile' i x) in
  let r : i.ctx_out = IIOwp?.reflect dm_tree in
  backtranslate' i r

(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)

(** *** Compilation **)
let compile (i:interface) (ip:iprog i) (ca:(acts free){spec_free_acts ca}) : prog i = 
  fun (c:ctx i) -> 
    let tree : dm_iio i.iprog_out (ILang.pi_hist i.vpi) = 
      reify (ip (backtranslate i c ca)) in
    iio_bind tree (fun x -> free.ret (compile'' i x))

(** ** Theorems **)

(** **** Free Actions **)
val free_acts : acts free
(** CA: I can not reify here an IO computation because there is no way to prove the pre-condition **)
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg
  
let lemma_free_acts () : 
  Lemma (spec_free_acts free_acts) = admit ()

(** *** Beh **)
let beh #a x (*:whole *) = dm_iio_theta #a (x ())

let included_in (x:hist 'a) (pi:pi_type) =
  forall h. x (fun lt r -> enforced_locally pi h lt) h

(** *** Soundness *)
(* forall ip c pi. compile ip `link pi` c ~> t => t \in pi *)
#set-options "--print_implicits"

let soundness (i:interface) (ip:iprog i) (c:ctx i) =
  lemma_free_acts ();
  squash (beh (compile i ip free_acts `link i` c) `included_in` i.vpi)
(* TODO: to prove this, one can add to compile a post-condition that guarantees this *)

(* Example:
   ct free.m = alpha -> free.m beta
   ictx for this = alpha -> IIO beta pi
*)

(** *** Transparency **)
(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)
(* we give an interface that has the true pi on the left, and our pi on the right *)
(* pi is part of the interface because the partial program uses it in its type in two places: input type and output type. *)
(* the pi in this theorem, has nothing to do with the pi we need *)

let true_interface (i:interface) : interface = {
  vpi = (fun cmd arg h -> true);
  ipi = i.ipi;

  (* intermediate level *)
  ictx_in = i.ictx_in;
  ictx_out = i.ictx_out;
  iprog_out = i.iprog_out; 

  (* target level *)
  ctx_in = i.ctx_in;
  ctx_out = i.ctx_out;
  prog_out = i.prog_out; 

  r_vpi_ipi = admit ();
}

(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)
let transparency (i:interface) (ip:iprog (true_interface i)) (c:ctx (true_interface i)) =
  squash (forall (t:trace). 
    beh ((compile (true_interface i) ip free_acts) `link (true_interface i)` c) `produces` t /\ t `respects` i.ipi ==>
      beh ((compile (true_interface i) ip free_acts) *)

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
