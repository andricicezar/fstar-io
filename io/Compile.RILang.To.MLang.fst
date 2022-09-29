module Compile.RILang.To.MLang

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open TC.Monitorable.Hist

include Compile.RILang
include Compile.MLang

let dm_mon (pi:monitorable_prop) : monad = {
  m = rilang_dm pi;
  ret = (fun (x:'a) -> IIO.dm_iio_return 'a x);
  bind = (fun (m:rilang_dm pi 'a) (k:'a -> rilang_dm pi 'b) -> 
    let wp : Hist.hist 'b = Hist.hist_bind (pi_as_hist #'a pi) (fun _ -> pi_as_hist pi) in 
    let tr : IIO.dm_iio 'b wp = IIO.dm_iio_bind _ _ _ _ (as_iio_dm m) (fun x -> as_iio_dm (k x)) in
    lemma_bind_pi_implies_pi #'a #'b pi;
    let w = IIO.dm_iio_subcomp 'b wp (pi_as_hist pi) tr in
    as_rilang_dm w)
}

assume val dm_acts (pi:monitorable_prop) : acts (dm_mon pi)

(** *** Notes **)
(** In our transparency criteria, we did a trick that may not work anymore.

    The trick was:
    To a partial program that expects a context that respects the trivial pi,
    we were passing a context that respects a stronger pi.

    However, now because the ctx is effect polymorphic, when we instantiate it with
    a `dm pi` it also changes the spec of the callbacks from the partial program.

    Conclusion: The ctx must have the pi the pprog expects it to have. We need a new way
                to write transparency.
**)

(** Proof of concept: **)
type r_vpi_ipi (vpi ipi:monitorable_prop) = squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt)

noeq
type experiment_interface = {
  (* Partial Program respects vpi *)
  vpi : monitorable_prop;

  (* Type of the context *)
  ct:(Type->Type)->Type;

  (* Primitive that should cast the context to the weaker pi (vpi) *)
  subcomp_ct : (#ipi:monitorable_prop) -> (#_ : r_vpi_ipi vpi ipi) -> (ct (dm_mon ipi).m) -> (ct (dm_mon vpi).m);
}

[@@expect_failure]
let counter_example (vpi:monitorable_prop) : experiment_interface = {
  vpi = vpi;
  ct = (fun m -> f:(int -> m int) -> m int);
  subcomp_ct = (fun #ipi (c:(int -> (dm_mon ipi).m int) -> (dm_mon ipi).m int) (f:int -> (dm_mon vpi).m int) -> 
    (** `c` is expecting a `f` that respects ipi, but f respects vpi that 
        is weaker than ipi, so we can not cast to it
	TODO: 
	- was this working before? 
	- why was this working before? 
	Answer: 
	  * it is hard to answer since there were so many changes lately
	    and the complexity before was quite hard to crompehend.
	  * in the latest version, this was admitted.
	  * previous version to that, we did not address HO.
	  * The intuition before was that we only instrument the context, thus
	    the specification of the partial programs' callbacks should not change. 
            However, since the type of the partial programs' callbacks are part of the 
            type of the context and the type of the context is effect polymorphic at all 
            positions (including specs), we have to weaken/strengthen specs in the same time. 
	TODO: maybe we don't need to weaken at all positions? 
        CA: I don't see how this can be done without losing the nice abstractions. For now 
            it may be better to look at how to state Transparency differently. **)
    c f);
}
(** End notes *)

class compilable (comp_in:Type u#a) (pi:monitorable_prop) = {
  [@@@no_method]
  comp_out : Type u#b;
  compile: comp_in -> comp_out;

  [@@@no_method]
  rilang_comp_in : rilang comp_in pi;
  [@@@no_method]
  mlang_comp_out : mlang comp_out;
}

instance compilable_int pi : compilable int pi = {
  comp_out = int;
  rilang_comp_in = rilang_int pi;
  mlang_comp_out = mlang_int;
  compile = (fun x -> x);
}

instance compilable_int_arrow
  pi
  (t2:Type) {| d2:compilable t2 pi |} :
  Tot (compilable (int -> rilang_dm pi t2) pi) = {
  rilang_comp_in = rilang_arrow pi (rilang_int pi) d2.rilang_comp_in;

  comp_out = int -> free.m d2.comp_out;
  mlang_comp_out = mlang_free_arrow mlang_int d2.mlang_comp_out;

  compile = (fun (f:(int -> rilang_dm pi t2)) (x:int) ->
    let r : rilang_dm pi t2 = f x in
    let r = as_iio_dm r in 
    IIO.dm_iio_bind _ _ _ (fun _ -> (pi_as_hist pi)) r (fun x -> IIO.dm_iio_return _ (d2.compile x))
  );
}

(** *** Compilable arrows **)
(* The pis don't have to be the same when compiling *)
instance compilable_arrow
  ct_pi pi pt_pi
  (ct:((Type->Type)->Type)) {| d1:rilang (ct (dm_mon ct_pi).m) ct_pi |} {| d1':mlang (ct free.m) |}
  (pt:Type) {| d2:compilable pt pt_pi |} :
  Tot (compilable ((ct (dm_mon ct_pi).m) -> rilang_dm pi pt) pi) = {
  rilang_comp_in = rilang_arrow pi d1 d2.rilang_comp_in;

  comp_out = (mon:monad -> acts mon -> ct mon.m) -> free.m d2.comp_out;
  mlang_comp_out = mlang_free_arrow (mlang_effectpoly d1') d2.mlang_comp_out;

  compile = (fun (f:((ct (dm_mon ct_pi).m) -> rilang_dm pi pt)) (tgt_x:(mon:monad -> acts mon -> ct mon.m)) ->
    let src_x : ct (dm_mon ct_pi).m = tgt_x (dm_mon ct_pi) (dm_acts ct_pi) in
    let r : rilang_dm pi pt = f src_x in
    let r = as_iio_dm r in 
    IIO.dm_iio_bind _ _ _ (fun _ -> (pi_as_hist pi)) r (fun x -> IIO.dm_iio_return _ (d2.compile x))
  );
}


(** ** Manual testing *)
(* TODO:
  - [v] support HO on the return type
  - [ ] support different pi for the ctx
*)
noeq
type interface = {
  vpi : monitorable_prop;

  ct:(Type->Type)->Type;
  rilang_ct  : ipi:monitorable_prop -> rilang (ct (dm_mon ipi).m) ipi;
  mlang_ct   : mlang (ct free.m);

  pt:(Type->Type)->Type;
  compilable_pt : compilable (pt (dm_mon vpi).m) vpi;
}


type ictx (i:interface) (ipi:monitorable_prop) = i.ct (dm_mon ipi).m
type iprog (i:interface)  = ictx i i.vpi -> rilang_dm i.vpi (i.pt (dm_mon i.vpi).m)
type iwhole (i:interface) = unit -> rilang_dm i.vpi (i.pt (dm_mon i.vpi).m) 

let ilink 
  (#i:interface) 
  (ip:iprog i) 
  (ic:ictx i i.vpi) : 
  iwhole i = 
  fun () -> ip ic

(** *** Target Lang **)
type ctx (i:interface) = mon:monad -> acts mon -> i.ct mon.m
type prog (i:interface) = ctx i -> free.m i.compilable_pt.comp_out
type whole (i:interface) = unit -> free.m i.compilable_pt.comp_out 
let link (#i:interface) (p:prog i) (c:ctx i) : whole i = fun () -> p c

#reset-options

let prog_compilable (i:interface) : compilable (iprog i) i.vpi =
  compilable_arrow
    i.vpi i.vpi i.vpi
    i.ct #(i.rilang_ct i.vpi) #i.mlang_ct
    (i.pt (dm_mon i.vpi).m) #i.compilable_pt

let model_compile
  (#i:interface)
  (ip:iprog i) :
  prog i = 
  (prog_compilable i).compile ip

(** *** Case Studies **)

assume val thePi : monitorable_prop

let test1 : interface = {
  vpi = thePi;

  ct = (fun m -> (int -> m int));
  rilang_ct = (fun ipi -> rilang_arrow ipi (rilang_int ipi) (rilang_int ipi));
  mlang_ct = mlang_free_arrow mlang_int mlang_int;

  pt = (fun m -> int);
  compilable_pt = compilable_int thePi;
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

  ct = (fun m -> (int -> m int) -> m int);
  rilang_ct = (fun ipi -> rilang_arrow ipi (rilang_arrow ipi (rilang_int ipi) (rilang_int ipi)) (rilang_int ipi));
  mlang_ct = mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int;

  pt = (fun m -> int);
  compilable_pt = compilable_int thePi;
}

let iprog2 : iprog test2 = fun c -> (dm_mon thePi).bind (c (fun x -> (dm_mon thePi).ret (x + 5))) (fun r -> (dm_mon thePi).ret (r + 1))
let mprog2 : prog test2 = model_compile iprog2 //thePi
val mctx2 : ctx test2  
let mctx2 (mon:monad) (acts:acts mon) (f:int -> mon.m int) : mon.m int =
  mon.bind (f 5) (fun x -> mon.ret (x+2))
let mwhole2 = mprog2 `link` mctx2

let test3 : interface = {
  vpi = thePi;

  ct = (fun m -> (int -> m int) -> m int);
  rilang_ct = (fun ipi -> rilang_arrow ipi (rilang_arrow ipi (rilang_int ipi) (rilang_int ipi)) (rilang_int ipi));
  mlang_ct = mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int;

  pt = (fun m -> int -> m int);
  compilable_pt = compilable_int_arrow thePi int #(compilable_int thePi);
}

let test4 : interface = {
  vpi = thePi;

  ct = (fun m -> (int -> m int) -> m int);
  rilang_ct = (fun ipi -> rilang_arrow ipi (rilang_arrow ipi (rilang_int ipi) (rilang_int ipi)) (rilang_int ipi));
  mlang_ct = mlang_free_arrow (mlang_free_arrow mlang_int mlang_int) mlang_int;

  pt = (fun m -> (int -> m int) -> m int);
  compilable_pt = compilable_arrow thePi thePi thePi (fun m -> int -> m int) #(rilang_arrow thePi (rilang_int thePi) (rilang_int thePi)) #(mlang_free_arrow mlang_int mlang_int) int #(compilable_int thePi);
}


val iprog4 : iprog test4
let iprog4 ctx = (dm_mon thePi).ret (fun cb -> cb 5)
let mprog4 : prog test4 = model_compile iprog4 //thePi
val mctx4 : ctx test4  
let mctx4 (mon:monad) (acts:acts mon) (f:int -> mon.m int) : mon.m int =
  mon.bind (f 5) (fun x -> mon.ret (x+2))

let mwhole4 = mprog4 `link` mctx4

let _ = assert (has_type mwhole4 (unit -> free.m (test4.compilable_pt.comp_out))) by (norm [delta_only [`%Mkcompilable?.comp_out;`%Mkinterface?.compilable_pt;`%Mkmonad?.m;`%Mkinterface?.pt]; iota;zeta]; dump "H")

let _ = assert (test4.compilable_pt.comp_out == ((mon:monad -> acts mon -> (int -> mon.m int)) -> free.m int)) by (compute ())

let mwhole4' : (unit -> free.m ((mon:monad -> acts mon -> (int -> mon.m int)) -> free.m int)) =
  assert (has_type mwhole4 (unit -> free.m ((mon:monad -> acts mon -> (int -> mon.m int)) -> free.m int))) by (compute ());
  admit (); (* not sure why this does not work since the previous assert works *)
  mwhole4
  
(* TODO: probably can not bind because the types are not in the same universe *)
let _ = 
  let whole4 : free.m ((mon:monad -> acts mon -> (int -> mon.m int)) -> free.m int) = mwhole4' () in
  free.bind whole4 #((mon:monad -> acts mon -> (int -> mon.m int)) -> free.m int) #int (fun (p:((mon:monad -> acts mon -> (int -> mon.m int)) -> free.m int)) ->
    let r : free.m int = p mctx1 in
    r)
