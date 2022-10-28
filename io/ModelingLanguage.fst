module ModelingLanguage

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses

open Common
open Free
open IO
open TC.Monitorable.Hist
open IIO

#set-options "--print_universes --print_implicits"


open Compile.RILang.To.MLang

noeq
type interface = {
  vpi : monitorable_prop;

  ct:(Type->Type)->Type;
  rilang_ct  : rilang (ct (dm_mon vpi).m) vpi;
  mlang_ct   : mlang (ct free.m);

  //pt:(Type->Type)->Type0;
  //compilable_pt : compilable (pt (dm_mon vpi).m) vpi;
}


(** *** Intermediate Lang **)
type ictx (i:interface) (ipi:monitorable_prop) = i.ct (dm_mon ipi).m
type iprog (i:interface)  = ictx i i.vpi -> rilang_dm i.vpi int
type iwhole (i:interface) = unit -> rilang_dm i.vpi int 
//type iprog (i:interface)  = ictx i i.vpi -> rilang_dm i.vpi (i.pt (dm_mon i.vpi).m)
//type iwhole (i:interface) = unit -> rilang_dm i.vpi (i.pt (dm_mon i.vpi).m)

//  vpi  : pi_type; (* the statically verified monitorable property (part of partial program's spec) *)
//  ipi : pi_type;  (* the instrumented monitorable property (part of context's spec) *)

type r_vpi_ipi (vpi ipi:monitorable_prop) = squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt)

(* The interesting thing here is that the context can have a different (stronger) pi than the partial program. *)
let ilink 
  (#i:interface) 
 // (#ipi:monitorable_prop) 
//  (#_ : r_vpi_ipi i.vpi ipi)
  (ip:iprog i) 
  (ic:ictx i i.vpi) : 
  iwhole i = 
  fun () -> ip ic

(** *** Target Lang **)
(* will eventually need a signature and what not;
   I think we need to pass the abstract monad inside is we want to support higher-order types.
   in this case I conflated alpha + beta = ct, and gamma + delta = pt *)
type ctx (i:interface) = mon:monad -> acts mon -> i.ct mon.m
type prog (i:interface) = ctx i -> free.m int 

type whole (i:interface) = unit -> free.m int 
  
let link (#i:interface) (p:prog i) (c:ctx i) : whole i = 
  fun () -> p c

#reset-options

let prog_compilable (i:interface) : compilable (iprog i) i.vpi =
  compilable_arrow
    i.vpi
    i.ct #i.rilang_ct #i.mlang_ct
    int #(compilable_int i.vpi)

let model_compile
  (#i:interface)
  (ip:iprog i) :
  prog i = 
  let p : (prog_compilable i).comp_out = (prog_compilable i).compile ip in
  p

(** *** Case Studies **)

assume val thePi : monitorable_prop

let test1 : interface = {
  vpi = thePi;

  ct = (fun m -> (int -> m int));

  rilang_ct = rilang_arrow thePi (rilang_int thePi) (rilang_int thePi);
  mlang_ct = mlang_free_arrow mlang_int mlang_int;
}

let iprog1 : iprog test1 = fun c -> (dm_mon thePi).bind (c 5) (fun r -> (dm_mon thePi).ret (r + 1))
let mprog1 : prog test1 = model_compile iprog1 //thePi
val mctx1 : ctx test1  
let mctx1 (mon:monad) (acts:acts mon) (x:int) : mon.m int =
  mon.ret (x+2)

let mwhole1 = mprog1 `link` mctx1

(** new test where ctx accepts an f from prog **)

let test2 : interface = {
  vpi = thePi;

  (* intermediate level *)
  ct = (fun m -> (int -> m int) -> m int);
  rilang_ct = rilang_arrow thePi (rilang_arrow thePi (rilang_int thePi) (rilang_int thePi)) (rilang_int thePi);
  mlang_ct = mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int;
}

let iprog2 : iprog test2 = fun c -> (dm_mon thePi).bind (c (fun x -> (dm_mon thePi).ret (x + 5))) (fun r -> (dm_mon thePi).ret (r + 1))
let mprog2 : prog test2 = model_compile iprog2 //thePi
val mctx2 : ctx test2  
let mctx2 (mon:monad) (acts:acts mon) (f:int -> mon.m int) : mon.m int =
  mon.bind (f 5) (fun x -> mon.ret (x+2))
let mwhole2 = mprog2 `link` mctx2


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

let iproduces (#i:interface) (d:iwhole i) (tr:trace * (i.prog_out.mcomp free free_acts)) =
  exists r'. compile #_ #_ #i.prog_out r' == snd tr /\ (reify_IIOwp d) `_produces` (fst tr, r')

(** *** Soundness *)
let soundness (i:interface) (ip:iprog i) (c:ctx i) : Type0 =
  lemma_free_acts ();
  beh (model_compile ip i.vpi `link` c) `subset_of` (pi_to_set i.vpi)

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
    (forall (ip:iprog i) (tr:trace * i.prog_out.mcomp).
      ((model_compile ip i.vpi #(r_pi i.vpi)) `link` c) `produces` tr <==>
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
let transparency (i:interface) (ip:iprog i) (c:ctx i) (tr:trace * i.prog_out.mcomp) (ipi:pi_type) (r:r_vpi_ipi i.vpi ipi) =
  ((model_compile ip i.vpi) `link` c) `produces` tr /\ tr `included_in` (pi_to_set #i.prog_out.mcomp ipi) ==>
    ((model_compile ip ipi #r) `link` c) `produces` tr
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
