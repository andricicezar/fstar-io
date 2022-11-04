module RrHP

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot

open Free
open IO
open IO.Sig
open TC.Monitorable.Hist
open IIO

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

let pi_type = pi:monitorable_prop{forall h op arg. pi op arg h ==> io_pre op arg h}

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

  vpi : pi_type;
}


(** *** Intermediate Lang **)
type ictx (i:interface) (ipi:pi_type) =  x:i.ictx_in -> ILang.IIOpi i.ictx_out ipi
type iprog (i:interface)  = ictx i i.vpi -> ILang.IIOpi i.iprog_out i.vpi
type iwhole (i:interface) = unit -> ILang.IIOpi i.iprog_out i.vpi

//  vpi  : pi_type; (* the statically verified monitorable property (part of partial program's spec) *)
//  ipi : pi_type;  (* the instrumented monitorable property (part of context's spec) *)
type r_vpi_ipi (vpi ipi:pi_type) = squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt)

(* The interesting thing here is that the context can have a different (stronger) pi than the partial program. *)
let ilink 
  (#i:interface) 
  (#ipi:pi_type) 
  (#_ : r_vpi_ipi i.vpi ipi)
  (ip:iprog i) 
  (ic:ictx i ipi) : 
  iwhole i = 
  fun () -> ip ic

(** *** Target Lang **)
(* will eventually need a signature and what not;
   I think we need to pass the abstract monad inside is we want to support higher-order types.
   in this case I conflated alpha + beta = ct, and gamma + delta = pt *)
type ct (i:interface) (mon:monad) = i.ctx_in -> mon.m i.ctx_out
type pt (i:interface) (mon:monad) = mon.m i.prog_out 

type ctx (i:interface) = mon:monad -> acts mon -> ct i mon
type prog (i:interface) = ctx i -> pt i free

type whole (i:interface) = unit -> iio i.prog_out 
let link (#i:interface) (p:prog i) (c:ctx i) : whole i = fun () -> p c

(* TODO: these should be replaced by typeclasses *)
assume val backtranslate' : (i:interface) -> i.ctx_out -> i.ictx_out
assume val compile' : (i:interface) -> i.ictx_in -> i.ctx_in
assume val compile'' : (i:interface) -> i.iprog_out -> i.prog_out


(** *** Parametricity **)
type verified_marrow (t1:Type u#a) (t2:Type u#b) = t1 -> free.m t2
type unverified_marrow (t1:Type) (t2:Type) : Type = mon:monad -> acts mon -> t1 -> mon.m t2
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
type ct_p (a b:Type) (mon:monad) (mon_p:monad_p mon) (c:a -> mon.m b) =
  squash (forall x. mon_p.m_p b (fun x -> True) (c x))

type ctx_p (a b:Type) (mon:monad) (mon_p:monad_p mon) (theActs:acts mon) (theActs_p:acts_p mon mon_p theActs) (c:unverified_marrow a b) =
  ct_p a b mon mon_p (c mon theActs)

(* TODO: check with others **)
(* Parametricity Assumption about the Context **)
assume val ctx_param : 
  (a:Type) -> 
  (b:Type) ->
  (mon:monad) -> (mon_p:monad_p mon) ->
  (theActs:acts mon) -> (theActs_p:acts_p mon mon_p theActs) ->
  (c:unverified_marrow a b) -> 
  Lemma (ctx_p a b mon mon_p theActs theActs_p c)

(** **** Parametricity - instances **)
let free_p (pi:pi_type) : monad_p free = {
  m_p = (fun a a_p tree -> ILang.pi_hist #a pi `hist_ord` dm_iio_theta tree);
  ret_p = (fun a a_p tree tree_p -> ());
}

(** *** Backtranslate **)
unfold val check_get_trace : pi_type -> cmd:io_cmds -> io_sig.args cmd -> free.m bool
[@@ "opaque_to_smt"]
let check_get_trace pi cmd arg = 
  iio_bind (IO.Sig.Call.iio_call GetTrace ()) (fun h -> Return (pi cmd arg h))

val wrap : pi_type -> acts free -> acts free
[@@ "opaque_to_smt"]
let wrap pi theActs cmd arg =
  iio_bind
    (check_get_trace pi cmd arg)
    (fun b -> if b then theActs cmd arg else free.ret #(io_sig.res cmd arg) (Inr Common.Contract_failure))

let spec_free_acts (ca:acts free) =
  (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (ca cmd arg))

#set-options "--split_queries"
val wrap_p : (pi:pi_type) -> (ca:(acts free){spec_free_acts ca}) -> acts_p free (free_p pi) (wrap pi ca)
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
      calc (==>) {
        ILang.pi_hist pi p h;
        ==> {
          assert (pi op arg h ==> io_pre op arg h);
          assert (iio_wps op arg p h ==> dm_iio_theta (ca op arg) p h)
        }
        if pi op arg h then
          (* TODO: I only have to prove this one *)
          dm_iio_theta (ca op arg) p h
        else 
          (* this branch is proved automatically *)
          dm_iio_theta (Return (Inr Common.Contract_failure)) p h;
        ==> {}
        if pi op arg h then
          dm_iio_theta (ca op arg) (fun lt' r -> p lt' r) h
        else 
          dm_iio_theta (Return (Inr Common.Contract_failure)) (fun lt' r -> p lt' r) h;
        ==> {}
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
        ==> { 
          let m1 = (check_get_trace pi op arg) in
          let m2 = fun b -> (if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)) in 
          DMFree.lemma_theta_is_lax_morphism_bind iio_wps m1 m2;
          assert (hist_bind (dm_iio_theta m1) (fun b -> dm_iio_theta (m2 b)) p h ==>
            dm_iio_theta (iio_bind m1 m2) p h)
        }
        dm_iio_theta (
          iio_bind
            (check_get_trace pi op arg)
            (fun b -> if b then ca op arg else free.ret #(io_sig.res op arg) (Inr Common.Contract_failure)))
         p h;
        == { _ by (norm [delta_only [`%wrap]; zeta]) }
        dm_iio_theta ((wrap pi ca) op arg) p h;
      }
    end
  end
#reset-options

(** **** Free Actions **)
val free_acts : acts free
(** CA: I can not reify here an IO computation because there is no way to prove the pre-condition **)
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg

let lemma_free_acts () : Lemma (spec_free_acts free_acts) = 
  assert (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (free_acts cmd arg));
  assert (spec_free_acts free_acts) by (assumption ())

val cast_to_dm_iio  : (#a:Type) -> (#b:Type) -> ipi:pi_type -> unverified_marrow a b -> (x:a) -> dm_iio b (ILang.pi_hist ipi)
let cast_to_dm_iio #a #b ipi c x : _ by (norm [delta_only [`%ctx_p;`%ct_p;`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  lemma_free_acts ();
  let c' : a -> free.m b = c free (wrap ipi free_acts) in
  let tree : iio b = c' x in
  ctx_param a b free (free_p ipi) (wrap ipi free_acts) (wrap_p ipi free_acts) c;
  assert (ILang.pi_hist ipi `hist_ord` dm_iio_theta tree);
  tree

val backtranslate : (#i:interface) -> ipi:pi_type -> ctx i -> ictx i ipi
let backtranslate #i ipi c (x:i.ictx_in) : ILang.IIOpi i.ictx_out ipi =
  let dm_tree : dm_iio i.ctx_out (ILang.pi_hist ipi) = cast_to_dm_iio ipi c (compile' i x) in
  let r : i.ctx_out = IIOwp?.reflect dm_tree in
  backtranslate' i r

(* Possible issue: backtranslation may be difficult if we allow m at arbitrary places,
   while in F* effects are only allowed at the right or arrows;
   make such kleisli arrows the abstraction instead of m? *)

(** *** Compilation **)
assume val reify_IIOwp (#a:Type) (#wp:hist a) ($f:unit -> IIOwp a wp) : dm_iio a wp

[@@ "opaque_to_smt"]
let compile_body  
  (#i:interface)
  (ip:iprog i)
  (ipi:pi_type)
  (#_: r_vpi_ipi i.vpi ipi) 
  (c:ctx i) :
  dm_iio i.iprog_out (ILang.pi_hist i.vpi) = 
  let f : unit -> IIOwp i.iprog_out (ILang.pi_hist i.vpi) = fun () -> ip (backtranslate ipi c) in
  reify_IIOwp f

let compile
  (#i:interface)
  (ip:iprog i)
  (ipi:pi_type)
  (#_: r_vpi_ipi i.vpi ipi) :
  prog i = 
  fun (c:ctx i) -> 
    let tree = compile_body ip ipi c in
    iio_bind tree (fun x -> free.ret (compile'' i x))

let compile_prog
  (#vpi:pi_type)
  (#ia:Type) (#ib:Type) (#ic:Type)
  (#ma:Type) (#mb:Type) (#mc:Type)
  (ip:(ia -> ILang.IIOpi ib vpi) -> ILang.IIOpi ic vpi)
  (ipi:pi_type)
  (#r: r_vpi_ipi vpi ipi) :
  ((mon:monad -> acts mon -> ma -> mon.m mb) -> free.m mc) =
  let i : interface =({ ictx_in = ia; ictx_out = ib; iprog_out = ic; vpi = vpi; ctx_in = ma; ctx_out = mb; prog_out = mc }) in
  let p : prog i = compile #i ip ipi #r in
  p

(** ** Theorems **)
(** *** Behaviors **)
(* A trace property i:qs a set of pairs between a trace and a result. 
   The trace is a complete trace. *)

(* `hist_post a` is the type of post-condtions over the local trace and the final result.
   Since, it has the same type as our definition of a trace property, we use 
   hist_post a as the type for trace properties. *)
type trace_property (a:Type) = hist_post #event a

(* We define `beh` that returns the set of traces produced by a whole program.
   Since whole programs start with the empty trace, thus, the
   local trace that the post-condtion describes is the complete trace.

   `theta` is a weakest precondtion monad, and we need it to be
   a post-condition. Looking at Kenji's thesis, we can apply the
   'backward predicate transformer 2.3.4' and the 
   'pre-/postcondition transformer 2.3.2' to obtain
   the 'set' of traces produces by the whole program. *)
let _beh  #a (d:iio a) : trace_property a = 
  fun lt (r:a) -> 
   (* We verify specs of whole programs, thus, instead of having
      properties forall histories, we can specialize it for the
      empty history *)
    forall p. dm_iio_theta d p [] ==> p lt r

(* TODO: the two sets have the same type, which is a limitation since:
         1) our traces do not contain the result
         2) the type between target and source can be different *)
let subset_of (s1:trace_property 'a) (s2:trace_property 'a) =
  (* TODO: using hist_post_ord implies that the trace and the result are part of s2.
           maybe we can simply our life for now by having just the trace **)
  s1 `hist_post_ord` s2

let included_in (tr:trace * 'a) (s1:trace_property 'a) : Type0 =
  s1 (fst tr) (snd tr) 
  
let _produces (d:iio 'a) (tr:trace * 'a) : Type0 =
  tr `included_in` (_beh d)

let pi_to_set #a (pi:pi_type) : trace_property a = fun lt _ -> enforced_locally pi [] lt

(** **** Helpers **)
let ibeh (#i:interface) (d:iwhole i) : trace_property i.iprog_out = 
  _beh (reify_IIOwp d)

(* d has this type to accomodate both whole and iwhole programs. **)
let beh  #a (d:unit -> iio a) : trace_property a = 
  _beh (d ())

let produces (d:unit -> iio 'a) (tr:trace * 'a) =
  (d ()) `_produces` tr


let iproduces (#i:interface) (d:iwhole i) (tr:trace * i.prog_out) =
  exists r'. compile'' i r' == snd tr /\ (reify_IIOwp d) `_produces` (fst tr, r')

(** *** Soundness *)
let soundness (i:interface) (ip:iprog i) (c:ctx i) : Type0 =
  lemma_free_acts ();
  beh (compile ip i.vpi `link` c) `subset_of` (pi_to_set i.vpi)

let lemma_dm_iio_theta_is_lax_morphism_bind (#a:Type u#a) (#b:Type u#b) (m:iio a) (f:a -> iio b) :
  Lemma
    (hist_bind (dm_iio_theta m) (fun x -> dm_iio_theta (f x)) `hist_ord` dm_iio_theta (iio_bind m f)) = 
    DMFree.lemma_theta_is_lax_morphism_bind iio_wps m f

let soundness_proof (i:interface) (ip:iprog i) (c:ctx i) : Lemma (soundness i ip c) = 
  let lhs : dm_iio i.iprog_out (ILang.pi_hist i.vpi) = (compile_body ip i.vpi #_ c) in
  let rhs : x:i.iprog_out -> dm_iio i.prog_out (hist_return (compile'' i x))  = fun x -> Mkmonad?.ret free (compile'' i x) in
  let p1 : hist_post i.iprog_out = (fun lt _ -> enforced_locally i.vpi [] lt) in
  let p1' : hist_post i.prog_out = (fun lt _ -> enforced_locally i.vpi [] lt) in

  assert (dm_iio_theta lhs p1 []);
  calc (==>) {
    dm_iio_theta lhs p1 [];
    ==> {  
      let p2 : hist_post i.iprog_out = 
      	(fun lt r ->
	   dm_iio_theta (Mkmonad?.ret free (compile'' i r))
	     (fun lt' (_:i.prog_out) -> enforced_locally i.vpi [] (lt @ lt'))
             (rev lt @ [])) in
      assert (p1 `hist_post_ord` p2) (* using monotonicity **)
    }
    dm_iio_theta 
       lhs
       (fun lt r ->
         dm_iio_theta (rhs r)
           (fun lt' _ -> enforced_locally i.vpi [] (lt @ lt'))
           (rev lt @ []))
       [];
    == { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift]; iota]) }
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) (fun lt (_:i.prog_out) -> enforced_locally i.vpi [] lt) [];
    == {}
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) p1' [];
    ==> { lemma_dm_iio_theta_is_lax_morphism_bind lhs rhs }
    dm_iio_theta #i.prog_out (iio_bind lhs rhs) p1' [];
  };
  assert (dm_iio_theta (iio_bind lhs rhs) p1' []);
  introduce forall lt r. (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally i.vpi [] lt with begin
    introduce (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally i.vpi [] lt with q1. begin
      eliminate forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r with p1';
      assert (p1' lt r);
      assert (enforced_locally i.vpi [] lt)
    end
  end;
  assert (soundness i ip c) by (assumption ())


let lemma_beh_bind_of_tot (m:iio 'a) (f:'a -> Tot 'b) (tr:trace * 'b) :
  Lemma 
    (requires (iio_bind m (fun x -> Return (f x))) `_produces` tr)
    (ensures  (exists r'. f r' == snd tr /\ m `_produces` (fst tr, r'))) =
    admit ()

let lemma_beh_bind_of_tot_dual (m:iio 'a) (f:'a -> Tot 'b) (tr:trace * 'b) :
  Lemma 
    (requires  (exists r'. f r' == snd tr /\ m `_produces` (fst tr, r')))
    (ensures ((iio_bind m (fun x -> Return (f x))) `_produces` tr)) =
    admit ()

(** *** RTC **)
let rtc (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) =
  ((compile ip i.vpi) `link` c) `produces` tr ==> 
    (exists (ic:ictx i i.vpi). (ip `ilink` ic) `iproduces` tr)

let rtc_proof (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) : Lemma (rtc i ip c tr) =
  let ws = (compile ip i.vpi) `link` c in
  let wt = fun ic -> (ip `ilink` ic) in
  introduce ws `produces` tr ==> (exists (ic:ictx i i.vpi). wt ic `iproduces` tr) with s. begin
    let ic = (backtranslate i.vpi c) in
    introduce exists (ic:ictx i i.vpi). wt ic `iproduces` tr with ic and begin
      let m = compile_body ip i.vpi c in
      assert (ws `produces` tr);
      assert (iio_bind m (fun x -> Return (compile'' i x)) `_produces` tr) by (assumption ());
      lemma_beh_bind_of_tot m (compile'' i) tr;
      assert (wt ic `iproduces` tr) by (
        norm [delta_only [`%iproduces;`%produces;`%beh;`%link;`%ilink]; iota];
        binder_retype (nth_binder (-1));
          norm [delta_only [`%compile_body];iota];
        trefl ();
       assumption ()
      )
    end
  end

(** *** RrHC **)
let r_pi (pi:pi_type) : squash (r_vpi_ipi pi pi) by (compute ()) = ()

(* stronger criterion; for which our backtranslation should also work *)
let rrhc (i:interface) (c:ctx i) =
  (exists (ic:ictx i i.vpi).
    (forall (ip:iprog i) (tr:trace * i.prog_out).
      ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==>
         (ip `ilink` ic) `iproduces` tr))

let rrhc_proof (i:interface) (c:ctx i) : Lemma (rrhc i c) =
  let ic = backtranslate i.vpi c in
  introduce exists (ic:ictx i i.vpi).
    (forall (ip:iprog i) (tr:trace * i.prog_out).
      ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==> (ip `ilink #_ #_ #(r_pi i.vpi)` ic) `iproduces` tr)
  with ic and 
  begin
    introduce forall (ip:iprog i) (tr:trace * i.prog_out). 
      ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr ==> (ip `ilink #i #_ #(r_pi i.vpi)` ic) `iproduces` tr
    with 
    begin
      rtc_proof i ip c tr
    end;

    introduce forall (ip:iprog i) (tr:trace * i.prog_out). 
      (ip `ilink #i #_ #(r_pi i.vpi)` ic) `iproduces` tr ==> ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr
    with 
    begin
      introduce (ip `ilink #i #_ #(r_pi i.vpi)` ic) `iproduces` tr ==>
        ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr
      with _.
      begin
        let ws = (compile ip i.vpi) `link` c in
        let wt = fun ic -> (ip `ilink` ic) in
        let m = compile_body ip i.vpi c in
        assert (wt ic `iproduces` tr);
        assert (exists r'. compile'' i r' == snd tr /\ m `_produces` (fst tr, r')) by (assumption ());
        lemma_beh_bind_of_tot_dual m (compile'' i) tr;
        assert (ws `produces` tr) by (
            norm [delta_only [`%iproduces;`%produces;`%beh;`%link;`%ilink]; iota];
            binder_retype (nth_binder (-1));
            norm [delta_only [`%compile_body];iota];
            trefl ();
            assumption ()
        )
      end
    end
  end

assume val thePi : pi_type

(** *** RrHP **)
let i : interface = {
  ictx_in = int;
  ictx_out = int;
  iprog_out = int; 

  (* target level *)
  ctx_in = int;
  ctx_out = int;
  prog_out = int; 

  vpi = thePi;
}

(* To state RrHP we need relations between the results and I am not sure if it is worth 
   doing that since we proved RrHC *)
type hyperproperty = trace_property int -> Type0


let rrhp (h:hyperproperty) (ip:iprog i) =
  (forall (ic:ictx i i.vpi). (h (ibeh (ip `ilink` ic)))) ==> 
    (forall c. (h (beh ((compile ip i.vpi) `link` c))))

let rrhc_g = forall c. rrhc i c
let rrhp_g = forall h ip. rrhp h ip


let lemma_trace_to_prop (ws:iwhole i) (wt:whole i) :
  Lemma 
    (requires (forall tr. ws `iproduces` tr <==> wt `produces` tr))
    (ensures (ibeh ws `subset_of` beh wt /\ beh wt `subset_of` ibeh ws)) = 
    admit ()

let lemma_prop_to_trace (ws:iwhole i) (wt:whole i) :
  Lemma
    (requires (ibeh ws `subset_of` beh wt /\ beh wt `subset_of` ibeh ws))
    (ensures (forall tr. ws `iproduces` tr <==> wt `produces` tr)) =
    admit ()

let lemma_prop_eqs (s1:trace_property int) (s2:trace_property int) (h:hyperproperty) : 
    Lemma 
      (requires (s1 `subset_of` s2 /\ s2 `subset_of` s1 /\ h s1))
      (ensures (h s2)) = 
      assert (forall lt r. s1 lt r <==> s2 lt r);
      assume (h s2)
      
let lemma_rrhc_eq_rrhp () : Lemma (rrhc_g <==> rrhp_g) = 
  introduce rrhc_g ==> 
    rrhp_g 
  with imp1. begin
    assert (forall c. (exists (ic:ictx i i.vpi).
    (forall (ip:iprog i) (tr:trace * i.prog_out).
      ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==>
         (ip `ilink` ic) `iproduces` tr)));
    introduce forall h ip. 
      rrhp h ip 
    with begin
      introduce (forall (ic:ictx i i.vpi). (h (ibeh (ip `ilink` ic)))) ==> 
        (forall c. (h (beh ((compile ip i.vpi) `link` c)))) 
      with imp2. begin
        introduce forall c. 
          (h (beh ((compile ip i.vpi) `link` c)))
        with begin
          Classical.Sugar.forall_elim c imp1;
          eliminate exists (ic:ictx i i.vpi).
            (forall (ip:iprog i) (tr:trace * i.prog_out).
              ((ip `ilink` ic) `iproduces` tr) <==>
              (((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr))
          returns (h (beh ((compile ip i.vpi `link` c))))
          with imp3. begin
	     let wt = ((compile ip i.vpi #(r_pi i.vpi)) `link` c) in
	     let ws = (ip `ilink` ic) in
	     Classical.Sugar.forall_elim ic imp2;
	     assert (h (ibeh ws));
	     Classical.Sugar.forall_elim ip imp3;
	     assert (forall tr. ws `iproduces` tr <==> wt `produces` tr);
	     lemma_trace_to_prop ws wt;
	     lemma_prop_eqs (ibeh ws) (beh wt) h;
             assert (h (beh wt))
          end
        end
      end
    end
  end;
  introduce rrhp_g ==> 
    rrhc_g 
  with imp1. begin
    introduce forall c. 
      rrhc i c 
    with begin
      assert (forall h ip. rrhp h ip);
      let ic = backtranslate i.vpi c in
      
      introduce exists (ic:ictx i i.vpi).
         (forall (ip:iprog i) (tr:trace * i.prog_out).
           ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==>
             (ip `ilink` ic) `iproduces` tr)
      with ic and begin
         introduce forall (ip:iprog i).
	   (forall (tr:trace * i.prog_out). ((compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==>
             (ip `ilink` ic) `iproduces` tr) 
	 with begin
	   eliminate forall ip. (forall h. rrhp h ip) with ip;
	   let wt = fun c -> ((compile ip i.vpi #(r_pi i.vpi)) `link` c) in
	   let ws = fun ic -> (ip `ilink` ic) in
	   let h : hyperproperty = fun pi -> exists ic. ibeh (ws ic) `subset_of` pi in
	   eliminate forall h. rrhp h ip with h;
           eliminate (forall (ic':ictx i i.vpi). (exists ic. ibeh (ws ic) `subset_of` (ibeh (ws ic')))) ==> 
	   	  (forall c'. (exists ic. ibeh (ws ic) `subset_of` (beh (wt c'))))
           with ();
           eliminate forall c'. (exists ic. ibeh (ws ic) `subset_of` (beh (wt c'))) with c;
	   introduce exists ic. ibeh (ws ic) `subset_of` (beh (wt c)) with ic and ();
	   assert (ibeh (ws ic) `subset_of` (beh (wt c)));
	   assume (beh (wt c) `subset_of` ibeh (ws ic)); (* RTC? *)
           lemma_prop_to_trace (ws ic) (wt c);
	   assert (forall tr. (wt c) `produces` tr <==> (ws ic) `iproduces` tr)
	 end
      end
    end
  end

(** *** Transparency **)
let transparency (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) =
  ((compile ip i.vpi) `link` c) `produces` tr /\ tr `included_in` (pi_to_set #i.prog_out ipi) ==>
    ((compile ip ipi #r) `link` c) `produces` tr
(* ip:iprog i weakest_pi = the partial program has the weakest spec, thus, it produces any trace 
                           and accepts contexts that also produce any trace that respect the weakest_pi.
   compile ip weakest_pi = compilation gives to the context the free_acts wrapped with minimal checks
   compile ip ipi        = compilation gives to the context the free_acts wrapped with ipi 
   The trick of this statement is that we can instrument the context with any spec stronger than weakest_pi
   because the partial program accepts all of them. This is possible because a context must be instrumented with a pi
   stronger than the one used as spec for the partial program. *)

let lemma_transparency_without_reify (i:interface) (ip:ictx i i.vpi -> dm_iio i.iprog_out (ILang.pi_hist i.vpi)) (c:ctx i) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) (p:hist_post i.iprog_out) :
  Lemma
    (requires (dm_iio_theta (ip (backtranslate ipi c)) p []))
    (ensures (dm_iio_theta (ip (backtranslate i.vpi c)) p [])) =
  (* TODO: why is this easy? my first intuition was that it would be easy, but I can not figure out the proof *)
  () 

let lemma_transparency_without_tot (i:interface) (ip:iprog i) (c:ctx i) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) (p:hist_post i.iprog_out) :
  Lemma
    (requires (dm_iio_theta (compile_body ip ipi c) p []))
    (ensures (dm_iio_theta (compile_body ip i.vpi c) p [])) by (
    norm [delta_only [`%compile_body];iota];
    ExtraTactics.blowup ();
    bump_nth 4;
    ExtraTactics.rewrite_lemma (-4) (-2);
    assumption ();
    bump_nth 3;
    assumption ()
  )=
  (* TODO: unexpected that I could prove this using tactics. probably unsound since reify is opaque to the SMT *)
  lemma_transparency_without_reify i (fun x -> reify_IIOwp (fun () -> ip x)) c ipi r p

let lemma_iio_theta_bind_of_tot (m:iio 'a) (f:'a -> Tot 'b) (p:hist_post 'b) h :
  Lemma 
    (requires (dm_iio_theta (iio_bind m (fun x -> Return (f x))) p h))
    (ensures  (dm_iio_theta m (fun lt r -> exists r'. f r == r' /\ p lt r') h)) =
    admit ()

let lemma_iio_theta_bind_of_tot_dual (m:iio 'a) (f:'a -> Tot 'b) (p:hist_post 'b) h :
  Lemma 
    (requires  (dm_iio_theta m (fun lt r -> exists r'. f r == r' /\ p lt r') h))
    (ensures (dm_iio_theta (iio_bind m (fun x -> Return (f x))) p h)) =
    admit ()

let lemma_transparency_tot
  (i:interface)
  (ip:iprog i)
  (c:ctx i)
  (ipi:pi_type)
  (r:r_vpi_ipi i.vpi ipi)
  (p:hist_post i.prog_out)
  (f:i.iprog_out -> Tot i.prog_out) :
  Lemma
    (requires (dm_iio_theta (iio_bind (compile_body ip ipi c) (fun x -> Return (f x))) p []))
    (ensures (dm_iio_theta (iio_bind (compile_body ip i.vpi c)( fun x -> Return (f x))) p [])) =
  let p' : hist_post i.iprog_out = (fun lt r -> exists r'. f r == r' /\ p lt r') in
  lemma_iio_theta_bind_of_tot (compile_body ip ipi c) f p [];
  lemma_transparency_without_tot i ip c ipi r p';
  lemma_iio_theta_bind_of_tot_dual (compile_body ip i.vpi c) f p []
  
let lemma_transparency_unfolded 
  (i:interface)
  (ip:iprog i)
  (c:ctx i)
  (ipi:pi_type)
  (r:r_vpi_ipi i.vpi ipi)
  (p:hist_post i.prog_out) :
  Lemma
    (requires (dm_iio_theta (iio_bind (compile_body ip ipi c) (fun x -> Return (compile'' i x))) p []))
    (ensures (dm_iio_theta (iio_bind (compile_body ip i.vpi c)( fun x -> Return (compile'' i x))) p [])) =
  lemma_transparency_tot i ip c ipi r p (compile'' i)
  
let transparency_proof (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) : Lemma (transparency i ip c tr ipi r) =
  introduce ((compile ip i.vpi) `link` c) `produces` tr /\ tr `included_in` (pi_to_set #i.prog_out ipi) ==>
    ((compile ip ipi #r) `link` c) `produces` tr
  with q1. 
  begin
    introduce forall (p: hist_post i.prog_out).
      dm_iio_theta (link (compile ip ipi) c ()) p [] ==> p (fst tr) (snd tr)
    with
    begin
      introduce dm_iio_theta (link (compile ip ipi) c ()) p [] ==> 
        p (fst tr) (snd tr)
      with _. 
      begin
        eliminate dm_iio_theta (link (compile ip i.vpi) c ()) p [] ==> 
          p (fst tr) (snd tr)
        with
        begin
          assert (dm_iio_theta (iio_bind (compile_body ip ipi c) (fun x -> Return (compile'' i x))) p []) by (assumption ());
          lemma_transparency_unfolded i ip c ipi r p;
          assert (dm_iio_theta (link (compile ip i.vpi) c ()) p []) by (assumption ())
        end
      end
    end
  end

(**
(* this is the smallest pi that can be used to instrument. this pi must imply io_pre *)
let weakest_pi : pi_type = fun op arg h ->
  match op with
  | Openfile -> true
  | Read -> is_open arg h
  | Close -> is_open arg h
      
(* weakest_pi and ipi both imply io_pre. weakest_pi is the weakest possible pi
   that implies io_pre, thus, all the other pis that imply io_pre also imply the weakest_pi 
   since they are stronger *)
let ipi_implies_weakest_pi (ipi:pi_type) : (r_vpi_ipi weakest_pi ipi) =
  let rec aux (ipi:pi_type) (h lt:trace) : 
    Lemma 
	(requires (enforced_locally ipi h lt))
	(ensures (enforced_locally weakest_pi h lt)) 
	(decreases lt) = begin
    match lt with
    | [] -> ()
    | hd::t -> aux (ipi) (hd::h) t
  end in
  Classical.forall_intro_2 (Classical.move_requires_2 (aux ipi))
**)

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