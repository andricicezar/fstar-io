module Criteria.RILang.To.MLang

open FStar.List.Tot
open FStar.Tactics

open Hist
open IO.Sig
open IIO

open TC.Monitorable.Hist
open Compile.RILang.To.MLang

noeq
type interface = {
  vpi : monitorable_prop;

  ct:(Type->Type)->Type;
  rilang_ct  : ipi:monitorable_prop -> rilang (ct (dm_mon ipi).m) ipi;
  mlang_ct   : mlang (ct free.m);

  // pt:int;
  //compilable_pt : compilable pt vpi;
}


type ictx (i:interface) (ipi:monitorable_prop) = i.ct (dm_mon ipi).m
type iprog (i:interface)  = ictx i i.vpi -> rilang_dm i.vpi int
type iwhole (i:interface) = unit -> rilang_dm i.vpi int

let ilink 
  (#i:interface) 
  (ip:iprog i) 
  (ic:ictx i i.vpi) : 
  iwhole i = 
  fun () -> ip ic

(** *** Target Lang **)
type ctx (i:interface) = mon:monad -> acts mon -> i.ct mon.m
type prog (i:interface) = ctx i -> free.m int
type whole (i:interface) = unit -> free.m int
let link (#i:interface) (p:prog i) (c:ctx i) : whole i = fun () -> p c

#reset-options

let prog_compilable (i:interface) : compilable (iprog i) i.vpi =
  compilable_arrow
    i.vpi i.vpi i.vpi
    i.ct #(i.rilang_ct i.vpi) #i.mlang_ct
    int #(compilable_int i.vpi)
    
let model_compile
  (#i:interface)
  (ip:iprog i) :
  prog i = 
  (prog_compilable i).compile ip

(** ** Criterias **)
(** *** Behaviors **)
(* A trace property is a set of pairs between a trace and a result. 
   The trace is a complete trace. *)

(* `hist_post a` is the type of post-condtions over the local trace and the final result.
   Since, it has the same type as our definition of a trace property, we use 
   hist_post a as the type for trace properties. *)
type finite_trace = IO.Sig.trace

type finite_trace_property (a:Type) = Hist.hist_post #IO.Sig.event a

(* We define `beh` that returns the set of traces produced by a whole program.
   Since whole programs start with the empty trace, thus, the
   local trace that the post-condtion describes is the complete trace.

   `theta` is a weakest precondtion monad, and we need it to be
   a post-condition. Looking at Kenji's thesis, we can apply the
   'backward predicate transformer 2.3.4' and the 
   'pre-/postcondition transformer 2.3.2' to obtain
   the 'set' of traces produces by the whole program. *)
let _beh  #a (d:free.m a) : finite_trace_property a = 
  fun lt (r:a) -> 
   (* We verify specs of whole programs, thus, instead of having
      properties forall histories, we can specialize it for the
      empty history *)
    forall p. IIO.dm_iio_theta d p [] ==> p lt r

(* TODO: the two sets have the same type, which is a limitation since:
         1) our traces do not contain the result
         2) the type between target and source can be different *)
let subset_of (s1:finite_trace_property 'a) (s2:finite_trace_property 'a) =
  (* TODO: using hist_post_ord implies that the trace and the result are part of s2.
           maybe we can simply our life for now by having just the trace **)
  s1 `Hist.hist_post_ord` s2

let included_in (tr:finite_trace * 'a) (s1:finite_trace_property 'a) =
  s1 (fst tr) (snd tr) 
  
let _produces (d:free.m 'a) (tr:finite_trace * 'a) =
  tr `included_in` (_beh d)

let pi_to_set #a (pi:monitorable_prop) : finite_trace_property a = fun lt _ -> enforced_locally pi [] lt

(** **** Helpers **)
(* d has this type to accomodate both whole and iwhole programs. **)
let beh  #a (d:unit -> free.m a) : finite_trace_property a = 
  _beh (d ())

let produces (d:unit -> free.m 'a) (tr:finite_trace * 'a) =
  (d ()) `_produces` tr

let soundness (i:interface) (ip:iprog i) (c:ctx i) : Type0 =
  beh (model_compile ip `link` c) `subset_of` (pi_to_set i.vpi)

let rrhc (i:interface) (c:ctx i) =
  (exists (ic:ictx i i.vpi).
    (forall (ip:iprog i) (tr:finite_trace * int).
      ((model_compile ip) `link` c) `produces` tr <==>
         (ip `ilink` ic) `produces` tr))

let transparency (i:interface) (ip:iprog i) (c:ctx i) (tr:finite_trace * int) (ipi:monitorable_prop) =
  ((model_compile ip) `link` c) `produces` tr /\ tr `included_in` (pi_to_set #int ipi) ==>
    ((model_compile ip) `link` c) `produces` tr


let lemma_dm_iio_theta_is_lax_morphism_bind (#a:Type u#a) (#b:Type u#b) (m:free.m a) (f:a -> free.m b) :
  Lemma
    (Hist.hist_bind (IIO.dm_iio_theta m) (fun x -> IIO.dm_iio_theta (f x)) `Hist.hist_ord` IIO.dm_iio_theta (IO.Sig.iio_bind m f)) = 
    DMFree.lemma_theta_is_lax_morphism_bind iio_wps m f

let soundness_proof (i:interface) (ip:iprog i) (c:ctx i) : Lemma (soundness i ip c) = 
  let lhs : dm_iio int (pi_as_hist i.vpi) = (compile_body #i.vpi #i.vpi #i.ct #int ip c) in
  let rhs : x:int -> dm_iio int (hist_return x)  = fun x -> Mkmonad?.ret free ((compilable_int i.vpi).compile x) in
  let p1 : hist_post int = (fun lt _ -> enforced_locally i.vpi [] lt) in
  let p1' : hist_post int = (fun lt _ -> enforced_locally i.vpi [] lt) in

  assert (dm_iio_theta lhs p1 []);
  calc (==>) {
    dm_iio_theta lhs p1 [];
    ==> {  
      let p2 : hist_post int = 
      	(fun lt r ->
	   dm_iio_theta (Mkmonad?.ret free ((compilable_int i.vpi).compile r))
	     (fun lt' (_:int) -> enforced_locally i.vpi [] (lt @ lt'))
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
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) (fun lt (_:int) -> enforced_locally i.vpi [] lt) [];
    == {}
    hist_bind (dm_iio_theta lhs) (fun x -> dm_iio_theta (rhs x)) p1' [];
    ==> { lemma_dm_iio_theta_is_lax_morphism_bind lhs rhs; admit () }
    dm_iio_theta #int (iio_bind lhs rhs) p1' [];
  };
  assert (dm_iio_theta (iio_bind lhs rhs) p1' []);
  introduce forall lt r. (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally i.vpi [] lt with begin
    introduce (forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r) ==> enforced_locally i.vpi [] lt with q1. begin
      eliminate forall p. dm_iio_theta (iio_bind lhs rhs) p [] ==> p lt r with p1';
      assert (p1' lt r);
      assert (enforced_locally i.vpi [] lt)
    end
  end;
  (* TODO: this may fail because model_compile contains now a typeclass that
           may need manual unfolding *)
  admit ();
  assert (soundness i ip c) by (assumption ())
