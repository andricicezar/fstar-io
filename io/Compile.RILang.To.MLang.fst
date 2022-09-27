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

(** *** Compilable arrows **)
instance compilable_arrow
  pi
  (ct:((Type->Type)->Type)) {| d1:rilang (ct (dm_mon pi).m) pi |} {| d1':mlang (ct free.m) |}
  (t2:Type) {| d2:compilable t2 pi |} :
  Tot (compilable ((ct (dm_mon pi).m) -> rilang_dm pi t2) pi) = {
  rilang_comp_in = rilang_arrow pi d1 d2.rilang_comp_in;

  comp_out = (mon:monad -> acts mon -> ct mon.m) -> free.m d2.comp_out;
  mlang_comp_out = mlang_free_arrow (mlang_effectpoly d1') d2.mlang_comp_out;

  compile = (fun (f:((ct (dm_mon pi).m) -> rilang_dm pi t2)) (tgt_x:(mon:monad -> acts mon -> ct mon.m)) ->
    let src_x : ct (dm_mon pi).m = tgt_x (dm_mon pi) (dm_acts pi) in
    let r : rilang_dm pi t2 = f src_x in
    let r = as_iio_dm r in 
    let w = IIO.dm_iio_bind _ _ _ (fun _ -> (pi_as_hist pi)) r (fun x -> IIO.dm_iio_return _ (d2.compile x)) in
    w
  );
}


(** ** Manual testing *)
(* TODO:
  - [ ] support HO on the return type
  - [ ] support different pi for the ctx
*)
noeq
type interface = {
  vpi : monitorable_prop;

  ct:(Type->Type)->Type;
  rilang_ct  : rilang (ct (dm_mon vpi).m) vpi;
  mlang_ct   : mlang (ct free.m);

  //pt:(Type->Type)->Type0;
  //compilable_pt : compilable (pt (dm_mon vpi).m) vpi;
}


type ictx (i:interface) (ipi:monitorable_prop) = i.ct (dm_mon ipi).m
type iprog (i:interface)  = ictx i i.vpi -> rilang_dm i.vpi int
type iwhole (i:interface) = unit -> rilang_dm i.vpi int 

type r_vpi_ipi (vpi ipi:monitorable_prop) = squash (forall h lt. enforced_locally ipi h lt ==> enforced_locally vpi h lt)

let ilink 
  (#i:interface) 
 // (#ipi:monitorable_prop) 
//  (#_ : r_vpi_ipi i.vpi ipi)
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
