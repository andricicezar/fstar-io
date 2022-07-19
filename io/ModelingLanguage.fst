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
  pi : pi_type;
  ictx_in : Type u#a;
  ictx_out : Type u#a;
  iprog_out : Type u#a; 

  ctx_in : Type u#a;
  ctx_out : Type u#a;
  prog_out : Type u#a; 
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
  m_p = (fun a a_p tree -> ILang.pi_hist a pi `hist_ord` dm_iio_theta tree);
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
  introduce forall p h. ILang.pi_hist _ pi p h ==> dm_iio_theta ((wrap pi ca) op arg) p h with begin
    introduce ILang.pi_hist _ pi p h ==> dm_iio_theta ((wrap pi ca) op arg) p h with _. begin
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

val cast_to_dm_iio  : (i:interface) -> ctx i -> (ca:(acts free){spec_free_acts ca}) -> (x:i.ctx_in) -> dm_iio i.ctx_out (ILang.pi_hist i.ctx_out i.pi)
let cast_to_dm_iio i c ca x : _ by (norm [delta_only [`%ctx_p;`%ct_p;`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  let c' : ct i free = c free (wrap i.pi ca) in
  let tree : iio i.ctx_out = c' x in
  ctx_param i free (free_p i.pi) (wrap i.pi ca) (wrap_p i.pi ca) c;
  assert (ILang.pi_hist i.ctx_out i.pi `hist_ord` dm_iio_theta tree);
  tree

(* TODO: the wrap does not have the intended effect *)
val backtranslate : (i:interface) -> ctx i -> (ca:(acts free){spec_free_acts ca}) -> ictx i
let backtranslate i c ca (x:i.ictx_in) : ILang.IIOpi i.ictx_out i.pi =
  let dm_tree : dm_iio i.ctx_out (ILang.pi_hist i.ctx_out i.pi) = cast_to_dm_iio i c ca (compile' i x) in
  let r : i.ctx_out = IIOwp?.reflect dm_tree in
  backtranslate' i r

(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)

(** *** Compilation **)
let compile (i:interface) (ip:iprog i) (ca:(acts free){spec_free_acts ca}) : prog i = 
  fun (c:ctx i) -> 
    let tree : dm_iio i.iprog_out (ILang.pi_hist _ i.pi) = 
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
  squash (beh (compile i ip free_acts `link i` c) `included_in` i.pi)
(* TODO: to prove this, one can add a post-condition that guarantees this to compile *)

(* Example:
   ct free.m = alpha -> free.m beta
   ictx for this = alpha -> IIO beta pi
*)

(** *** Transparency **)
(* forall ip c pi. link (compile ip free_acts) c ~> t /\ t \in pi => link (compile ip (wrapped_acts pi)) c ~> t *)

// let transparency (i:interface) (ip:iprog i) (c:ctx i) =
//  squash (beh (compile i ip free_acts) c) 


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
(* CA: ip has as a precondtion that it wants an instrumented `c` with pi, so, we can not do this without 
       relaxing type of `p`, thus, this has the same problem as the first attempt of transparency *)
