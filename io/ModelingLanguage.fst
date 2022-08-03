module ModelingLanguage

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses

open Common
open Free
open IO
open IO.Sig
open TC.Monitorable.Hist
open IIO

(* TODO : think about higher-order **)
(* TODO: define type class for MLang **)
(* TODO: refactor compile and backtranslate into instances of the TC **)
(* TODO: replace in the interface the target types with constraints on the 
         intermediate types **)


#set-options "--print_universes"

(* TODO: our monad also needs a way to represent failure,
         or is it enough to have it in actions? *)
noeq type monad = {
  m    : Type u#a -> Type u#(max 1 a);
  ret  : #a:Type -> a -> m a;
}

(* TODO: things should be indexed by this too. the context needs it to bind
         computations. unfortunately, we can not make it a part of the monad record. *)
//type mon_bind (mon:monad) = #a:Type u#a -> #b:Type u#b -> mon.m u#a a -> (a -> mon.m u#b b) -> mon.m u#b b

type acts (mon:monad) = op:io_cmds -> arg:io_sig.args op -> mon.m (io_sig.res op arg)

val free : monad
let free = { m = iio; ret = iio_return; }

(** **** Free Actions **)
val free_acts : acts free
let free_acts cmd arg = IO.Sig.Call.iio_call cmd arg

let spec_free_acts (ca:acts free) =
  (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (ca cmd arg))

let lemma_free_acts () : Lemma (spec_free_acts free_acts) = 
  assert (forall (cmd:io_cmds) (arg:io_sig.args cmd). iio_wps cmd arg `hist_ord` dm_iio_theta (free_acts cmd arg));
  assert (spec_free_acts free_acts) by (assumption ())

let pi_type = pi:monitorable_prop{forall h op arg. pi op arg h ==> io_pre op arg h}

(** * MLang **)
class mlang (t:Type) = { mldummy : unit }

(** *** FO instances **)
instance mlang_unit : mlang unit = { mldummy = () }

instance mlang_bool : mlang bool = { mldummy = () }
instance mlang_int : mlang int = { mldummy = () }

instance mlang_pair t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (t1 * t2) = 
  { mldummy = () }
instance mlang_either t1 t2 {| d1:mlang t1 |} {| d2:mlang t2 |} : mlang (either t1 t2) =
  { mldummy = () }

instance mlang_resexn t1 {| d1:mlang t1 |} : mlang (resexn t1) =
  { mldummy = () }

(** TODO: is this one neeeded? *)
instance mlang_tree #t1 (d1:mlang t1) : mlang (free.m t1) =
  { mldummy = () }

instance mlang_ver_arrow #t1 #t2 (d1:mlang t1) (d2:mlang t2) : mlang (t1 -> free.m t2) =
  { mldummy = () }

instance mlang_unv_arrow 
  (#ct:(Type u#a -> Type u#(max 1 a)) -> Type) 
  (d1:mlang (ct free.m)) :
  mlang (mon:monad -> acts mon -> ct mon.m) =
  { mldummy = () }

// (int -> int) -> (int -> int)
type ct (m:Type -> Type) = m int
let d1 : mlang (ct free.m) = mlang_tree mlang_int
type myctx = mon:monad -> acts mon -> ct mon.m
let _ : mlang myctx = mlang_unv_arrow d1 

type ct' (m:Type -> Type) = int -> m int
let d1' : mlang (ct' free.m) = mlang_ver_arrow mlang_int mlang_int
type myctx' = mon:monad -> acts mon -> ct' mon.m
let _ : mlang myctx' = mlang_unv_arrow d1'

type ct'' (m:Type -> Type) = (int -> m int) -> m int
let d1'' : mlang (ct'' free.m)= 
  mlang_ver_arrow (mlang_ver_arrow mlang_int mlang_int) mlang_int
type myctx'' = mon:monad -> acts mon -> ct'' mon.m
let _ : mlang myctx'' = mlang_unv_arrow d1''

type ct''' (m:Type u#0 -> Type u#1) = int -> m (int -> m int)

let d1''' : mlang (ct''' free)= 
  mlang_ver_arrow mlang_int (mlang_ver_arrow mlang_int mlang_int)
type myctx''' = mon:monad -> acts mon -> ct''' mon.m
let _ : mlang myctx''' = mlang_unv_arrow d1'''

(** * Type Classes **)
class compilable (comp_in:Type u#a) (pi:pi_type) = {
  comp_out : Type u#b;
  compile: comp_in -> comp_out;

  [@@@no_method]
  ilang_comp_in : ILang.ilang comp_in pi;
//  [@@@no_method]
//  mlang_comp_out : mlang comp_out;
}

class backtranslateable (btrans_out:Type u#a) (pi:pi_type) = {
  btrans_in : Type u#b;
  backtranslate: btrans_in -> btrans_out;

  [@@@no_method]
  ilang_btrans_out : ILang.ilang btrans_out pi;
//  [@@@no_method]
//  mlang_btrans_in : mlang btrans_in;
}

type verified_arrow (t1 t2:Type) pi = t1 -> ILang.IIOpi (resexn t2) pi
type unverified_arrow (ct:(Type -> Type) -> Type) = mon:monad -> acts mon -> ct mon.m

class instrumentable (inst_in_in inst_in_out:Type) (pi:pi_type) = {
  [@@@no_method]
  ct:(Type -> Type) -> Type;

  instrument: unverified_arrow ct -> Tot (verified_arrow inst_in_in inst_in_out pi); 

//  [@@@no_method]
//  mlang_inst_in : mlang (unverified_arrow inst_out_in inst_out_out pi);
  [@@@no_method]
  ilang_inst_out : ILang.ilang (verified_arrow inst_in_in inst_in_out pi) pi;
}

instance instrumentable_is_backtranslateable #t1 #t2 #ipi (d1: instrumentable t1 t2 ipi) : backtranslateable (verified_arrow t1 t2 ipi) ipi = {
  btrans_in = unverified_arrow d1.ct;
  //mlang_btrans_in = d1.mlang_inst_in;
  backtranslate = d1.instrument;
  ilang_btrans_out = d1.ilang_inst_out;
}

(** * Model of Secure Interop *)

noeq
type interface = {
  (* intermediate level *)
  ictx_in : Type u#a;
  ictx_out : Type u#b;
  iprog_out : Type u#c; 

  (* target level *)
  ctx_in : Type u#d;
  ctx_out : Type u#e;
  prog_out : Type u#f; 

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
let link (#i:interface) (p:prog i) (c:ctx i) : whole i = 
  fun () -> p c

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

(* TODO: check with others -- since this is assumed, it represents a risk **)
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

val cast_to_dm_iio  : (i:interface) -> ipi:pi_type -> ctx i -> (x:i.ctx_in) -> dm_iio i.ctx_out (ILang.pi_hist ipi)
let cast_to_dm_iio i ipi c x : _ by (norm [delta_only [`%ctx_p;`%ct_p;`%Mkmonad_p?.m_p;`%free_p]]; norm [iota]; explode ()) =
  lemma_free_acts ();
  let c' : ct i free = c free (wrap ipi free_acts) in
  let tree : iio i.ctx_out = c' x in
  ctx_param i free (free_p ipi) (wrap ipi free_acts) (wrap_p ipi free_acts) c;
  assert (ILang.pi_hist ipi `hist_ord` dm_iio_theta tree);
  tree



val backtranslate : (#i:interface) -> ipi:pi_type -> ctx i -> ictx i ipi
let backtranslate #i ipi c (x:i.ictx_in) : ILang.IIOpi i.ictx_out ipi =
  let dm_tree : dm_iio i.ctx_out (ILang.pi_hist ipi) = cast_to_dm_iio i ipi c (compile' i x) in
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


(** *** Case Studies **)

let test_i (pi:pi_type) : interface = {
  (* intermediate level *)
  ictx_in = int -> ILang.IIOpi int pi;
  ictx_out = int -> ILang.IIOpi int pi;
  iprog_out = int; 

  (* target level *)
  ctx_in = (mon:monad) -> int -> mon.m int;
  ctx_out = (mon:monad) -> int -> mon.m int;
  prog_out = int; 

  vpi = pi;
}






(** ** Criterias **)
(** *** Behaviors **)
(* A trace property is a set of pairs between a trace and a result. 
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

let included_in (tr:trace * 'a) (s1:trace_property 'a) =
  s1 (fst tr) (snd tr) 
  
let _produces (d:iio 'a) (tr:trace * 'a) =
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

(** *** RrHP **)
(* To state RrHP we need relations between the results and I am not sure if it is worth 
   doing that since we proved RrHC *)
type hyperproperty (a:Type) = trace_property a -> Type0

let rel (#i:interface) (p:trace_property i.iprog_out) : trace_property i.prog_out =
  fun t (r:i.prog_out) -> exists r'. compile'' i r' == r /\ p t r'
  
let rrhp (i:interface) (h:hyperproperty i.prog_out) (ip:iprog i) =
  (forall (ic:ictx i i.vpi). (h (rel (ibeh (ip `ilink` ic))))) ==> 
    (forall c. (h (beh ((compile ip i.vpi) `link` c))))

let rrhc_g (i:interface) = forall c. rrhc i c
let rrhp_g (i:interface) = forall h ip. rrhp i h ip

let lemma_rrhc_eq_rrhp (i:interface) : Lemma (rrhc_g i <==> rrhp_g i) = 
  introduce rrhc_g i ==> rrhp_g i with _. begin
    admit ()
  end;
  introduce rrhp_g i ==> rrhc_g i with _. begin
    admit ()
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
