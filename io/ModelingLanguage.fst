module ModelingLanguage

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
  (#vpi #ipi:pi_type) 
  (#_ : r_vpi_ipi vpi ipi)
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

type whole (i:interface) = unit -> iio i.prog_out 
let link (i:interface) (p:prog i) (c:ctx i) : whole i = fun () -> p c

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
  dm_iio i.iprog_out (ILang.pi_hist vpi) = 
  let f : unit -> IIOwp i.iprog_out (ILang.pi_hist vpi) = fun () -> ip (backtranslate i ipi c) in
  reify_IIOwp f

let compile
  (#i:interface)
  (#vpi:pi_type)
  (ip:iprog i vpi)
  (ipi:pi_type)
  (#_: r_vpi_ipi vpi ipi) :
  prog i = 
  fun (c:ctx i) -> 
    let tree = hack_compile ip ipi c in
    iio_bind tree (fun x -> free.ret (compile'' i x))

(** ** Theorems **)
(** *** Behaviors **)
(* `hist_post a` type is a set over traces, and my intuition
   is to use it directly instead of defining a new set of
   traces. *)
type set_of_traces (a:Type) = hist_post #event a

(* theta is a weakest precondtion monad, and we need it to be
   a post-condition. Looking at Kenji's thesis, we can apply the
   'backward predicate transformer monad 2.3.4' and the 
   'pre-/postcondition transformer monad 2.3.2' to obtain
   the definition of beh. *)

(* d has this type to accomodate both whole and iwhole programs. **)
let beh  #a (d:unit -> iio a) : set_of_traces a = 
  fun lt (r:a) -> 
   (* We verify specs of whole programs, thus, instead of having
      properties forall histories, we can specialize it for the
      empty history *)
    forall p. dm_iio_theta (d ()) p [] ==> p lt r

(* TODO: the two sets have the same type, which is a limitation since:
         1) our traces do not contain the result
         2) the type between target and source can be different *)
unfold let subset_of (s1:set_of_traces 'a) (s2:set_of_traces 'a) =
  s1 `hist_post_ord` s2

(* TODO: not sure if this has the intended effect. It should be a 
   predicate that says that `t` is a possible trace of `wp` *)
(* should this be flipped? *)
unfold let included_in (t:trace) (s1:set_of_traces 'a) =
  exists r. s1 t r 

let produces (d:unit -> iio 'a) (t:trace) =
  t `included_in` (beh d)
// exists r. (beh d) t r
// exists r. forall p. dm_iio_theta (d ()) p [] ==> p t r

let iproduces (#i:interface) (#vpi:pi_type) (d:iwhole i vpi) (t:trace) =
  (fun () -> reify_IIOwp d) `produces` t

let pi_to_set #a (pi:pi_type) : set_of_traces a = fun lt _ -> enforced_locally pi [] lt

(** *** Soundness *)
let soundness (i:interface) (vpi:pi_type) (ip:iprog i vpi) (c:ctx i) : Type0 =
  lemma_free_acts ();
  beh (compile ip vpi `link i` c) `subset_of` (pi_to_set vpi)

let lemma_dm_iio_theta_is_lax_morphism_bind (#a:Type u#a) (#b:Type u#b) (m:iio a) (f:a -> iio b) :
  Lemma
    (hist_bind (dm_iio_theta m) (fun x -> dm_iio_theta (f x)) `hist_ord` dm_iio_theta (iio_bind m f)) = 
    DMFree.lemma_theta_is_lax_morphism_bind iio_wps m f

let soundness_proof (i:interface) (vpi:pi_type) (ip:iprog i vpi) (c:ctx i) : Lemma (soundness i vpi ip c) = 
  let lhs : dm_iio i.iprog_out (ILang.pi_hist vpi) = (hack_compile #i #vpi ip vpi #_ c) in
  let rhs : x:i.iprog_out -> dm_iio i.prog_out (hist_return (compile'' i x))  = fun x -> Mkmonad?.ret free (compile'' i x) in
  let p1 : hist_post i.iprog_out = (fun lt _ -> enforced_locally vpi [] lt) in
  let p1' : hist_post i.prog_out = (fun lt _ -> enforced_locally vpi [] lt) in

  assert (dm_iio_theta lhs p1 []);
  calc (==>) {
    dm_iio_theta lhs p1 [];
    ==> {  
      let p2 : hist_post i.iprog_out = 
      	(fun lt r ->
	   dm_iio_theta (Mkmonad?.ret free (compile'' i r))
	     (fun lt' (_:i.prog_out) -> enforced_locally vpi [] (lt @ lt'))
             (rev lt @ [])) in
      assert (p1 `hist_post_ord` p2) (* using monotonicity **)
    }
    dm_iio_theta 
       lhs
       (fun lt r ->
         dm_iio_theta (rhs r)
           (fun lt' _ -> enforced_locally vpi [] (lt @ lt'))
           (rev lt @ []))
       [];
    == { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift]; iota]) }
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) (fun lt (_:i.prog_out) -> enforced_locally vpi [] lt) [];
    == {}
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) p1' [];
    ==> { lemma_dm_iio_theta_is_lax_morphism_bind lhs rhs }
    dm_iio_theta #i.prog_out (iio_bind lhs rhs) p1' [];
  };
  assert (dm_iio_theta (iio_bind lhs rhs) p1' []);
  introduce forall lt r. (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally vpi [] lt with begin
    introduce (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally vpi [] lt with q1. begin
      eliminate forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r with p1';
      assert (p1' lt r);
      assert (enforced_locally vpi [] lt)
    end
  end;
  assert (soundness i vpi ip c) by (assumption ())

let lemma_for_rtc (#i:interface) (m:iio i.iprog_out) (f:i.iprog_out -> i.prog_out) (t:trace) :
  Lemma 
    (requires ((fun () -> iio_bind m (fun x -> Return (f x))) `produces` t))
    (ensures  ((fun () -> m) `produces` t))  =
  introduce forall p'. dm_iio_theta m p' [] ==> (exists r'. p' t r') with begin
    introduce dm_iio_theta m p' [] ==> (exists r'. p' t r') with _. begin
      let p : hist_post i.prog_out = (fun lt (r:i.prog_out) -> exists (r':i.iprog_out). f r' == r /\ p' lt r') in
      eliminate forall p. dm_iio_theta (iio_bind m (fun x -> Return (f x))) p [] ==> (exists r. p t r) with p;
      calc (==>) {
        dm_iio_theta m p' [];
        ==> { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift]; iota]) }
        hist_bind (dm_iio_theta m) (fun x -> dm_iio_theta (Return (f x))) (fun lt (r:i.prog_out) -> exists (r':i.iprog_out). f r' == r /\ p' lt r') [];
        == {}
        hist_bind (dm_iio_theta m) (fun x -> dm_iio_theta (Return (f x))) p [];
        ==> { 
          let m1 : i.iprog_out -> iio i.prog_out = fun x -> Return (f x) in
          DMFree.lemma_theta_is_lax_morphism_bind iio_wps m m1;
          admit () (* not sure how to simplify the VC, but this should be trivial *)
        }
        dm_iio_theta (iio_bind m (fun x -> Return (f x))) p [];
        ==> {}
        exists (r:i.prog_out). p t r;
        == {}
        exists (r:i.prog_out). (fun lt (r:i.prog_out) -> exists (r':i.iprog_out). f r' == r /\ p' lt r') t r;
        == {}
        exists (r:i.prog_out). (exists (r':i.iprog_out). f r' == r /\ p' t r');
        ==> {}
        exists (r':i.iprog_out). (exists (r:i.prog_out). f r' == r /\ p' t r');
        ==> {}
        exists (r':i.iprog_out). p' t r';
      }
    end
  end

(** *** RTC **)
let rtc (i:interface) (vpi:pi_type) (ip:iprog i vpi) (c:ctx i) (t:trace) =
  ((compile ip vpi) `link i` c) `produces` t ==> 
    (exists (ic:ictx i vpi). (ip `ilink i` ic) `iproduces` t)

let rtc_proof (i:interface) (vpi:pi_type) (ip:iprog i vpi) (c:ctx i) (t:trace) : Lemma (rtc i vpi ip c t) =
  let ws = (compile ip vpi) `link i` c in
  let wt = fun ic -> (ip `ilink i` ic) in
  introduce ws `produces` t ==> (exists (ic:ictx i vpi). wt ic `iproduces` t) with s. begin
    let ic = (backtranslate i vpi c) in
    introduce exists (ic:ictx i vpi). wt ic `iproduces` t with ic and begin
      let m = hack_compile ip vpi c in
      assert (ws `produces` t);
      assert (forall (p:hist_post i.prog_out). dm_iio_theta (iio_bind m (fun x -> Return (compile'' i x))) p [] ==>
               (exists (r:i.prog_out). p t r)) by (assumption ());
      lemma_for_rtc m (compile'' i) t;
      assert (wt ic `iproduces` t) by (
        norm [delta_only [`%iproduces;`%produces;`%beh;`%link;`%ilink]; iota];
        binder_retype (nth_binder (-1));
          norm [delta_only [`%hack_compile];iota];
        trefl ();
        assumption ()
      )
    end
  end

(** *** Transparency **)
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

let transparency (i:interface) (ip:iprog i weakest_pi) (c:ctx i) (t:trace) (ipi:pi_type) =
  ((compile ip weakest_pi) `link i` c) `produces` t /\ t `respects` ipi ==>
    ((compile ip ipi #(ipi_implies_weakest_pi ipi)) `link i` c) `produces` t
(* ip:iprog i weakest_pi = the partial program has the weakest spec, thus, it produces any trace 
                           and accepts contexts that also produce any trace that respect the weakest_pi.
   compile ip weakest_pi = compilation gives to the context the free_acts wrapped with minimal checks
   compile ip ipi        = compilation gives to the context the free_acts wrapped with ipi 
   The trick of this statement is that we can instrument the context with any spec stronger than weakest_pi
   because the partial program accepts all of them. This is possible because a context must be instrumented with a pi
   stronger than the one used as spec for the partial program. *)

let transparency_cast_to_dm_iio (i:interface) (c:ctx i) (t:trace) (ipi:pi_type) (x:i.ctx_in) : 
  Lemma ((fun _ -> cast_to_dm_iio i weakest_pi c x) `produces` t /\ t `respects` ipi ==>
            (fun _ -> cast_to_dm_iio i ipi c x) `produces` t)  =
  assert (ILang.pi_hist ipi `hist_ord` dm_iio_theta (cast_to_dm_iio i ipi c x));
  assert (ILang.pi_hist weakest_pi `hist_ord` dm_iio_theta (cast_to_dm_iio i weakest_pi c x));
  ipi_implies_weakest_pi ipi;
  (* this is an extension of ipi_implies_weakest_pi *)
  assume (ILang.pi_hist #i.ctx_in ipi `hist_ord` ILang.pi_hist weakest_pi);
  (* transitivity of hist_ord *)
  assume (ILang.pi_hist ipi `hist_ord` dm_iio_theta (cast_to_dm_iio i weakest_pi c x));
  (* Goal: *)
  assume (forall p. dm_iio_theta (cast_to_dm_iio i ipi c x) p [] ==>
               dm_iio_theta (cast_to_dm_iio i weakest_pi c x) p [])


let transparency_proof (i:interface) (ip:iprog i weakest_pi) (c:ctx i) (t:trace) (ipi:pi_type) : Lemma (transparency i ip c t ipi) =
  assume (forall p. dm_iio_theta (hack_compile ip ipi #(ipi_implies_weakest_pi ipi) c) p [] ==>
    dm_iio_theta (hack_compile ip weakest_pi c) p []);
  (* the previous is an unfolding of the following *)
  assert (produces (fun _ -> hack_compile ip weakest_pi c) t /\ respects t ipi ==>
    produces (fun _ -> hack_compile ip ipi #(ipi_implies_weakest_pi ipi) c) t);
  (* the following is the unfolded goal and an extension to the previous assertion *)
  assume (produces (fun _ ->
          iio_bind (hack_compile ip weakest_pi c) (fun x -> Mkmonad?.ret free (compile'' i x)))
      t /\ respects t ipi ==>
    produces (fun _ -> iio_bind (hack_compile ip ipi c) (fun x -> Mkmonad?.ret free (compile'' i x))
      ) t)

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
