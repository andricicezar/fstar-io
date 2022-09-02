module BeyondCriteria.ILangToMLang

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

open BeyondCriteria
open RrHP

type trace_property = (a:Type u#a & (Hist.hist_post #(IO.Sig.event) a))

(**
val _beh : (#a:Type u#a) -> (d:free a) ^-> trace_property u#a
let _beh #a = 
  on (free a) (fun d ->
    (| a, (fun lt (r:a) -> forall p. IIO.dm_iio_theta d p [] ==> p lt r) |) <: trace_property)
**)

val _beh : (#a:Type u#a) -> (d:free.m a) -> trace_property u#a
let _beh #a d = 
    (| a, (fun lt (r:a) -> forall p. IIO.dm_iio_theta d p [] ==> p lt r) |)

noeq type ilang_int = {
  ctx_in : Type u#a; 
  ctx_out : Type u#b; 
  prog_out : Type u#c; 
  vpi : pi_type; 
}

type ictx   (i:ilang_int) = x:i.ctx_in -> ILang.IIOpi i.ctx_out i.vpi
type iprog  (i:ilang_int) = ictx i -> ILang.IIOpi i.prog_out i.vpi
type iwhole = i:ilang_int & (unit -> ILang.IIOpi i.prog_out i.vpi)

let ilink 
  (#i:ilang_int) 
  (ip:iprog i) 
  (ic:ictx i) : 
  iwhole = 
  (| i, (fun () -> ip ic <: ILang.IIOpi i.prog_out i.vpi) |)

val ibeh : iwhole u#a u#b u#c ^-> trace_property u#c
let ibeh =
  on (iwhole) (fun (| _, iw |) -> _beh (reify_IIOwp iw))

let ilang : language trace_property = {
  interface = ilang_int;
  ctx   = ictx;
  pprog = iprog;
  whole = iwhole;
  link  = ilink;
  beh   = ibeh;
}

noeq type mlang_int = {
  ctx_in : Type u#a; 
  ctx_out : Type u#b; 
  prog_out : Type u#c; 
}

type mctx   (i:mlang_int) = mon:monad -> acts mon -> i.ctx_in -> mon.m i.ctx_out
type mprog  (i:mlang_int) = mctx i -> free.m i.prog_out
type mwhole = i:mlang_int & (unit   -> free.m i.prog_out)

let mlink 
  (#i:mlang_int) 
  (mp:mprog i) 
  (mc:mctx i) : 
  mwhole = 
  (| i, (fun () -> mp mc) |)

val mbeh : mwhole u#a u#b u#c ^-> trace_property u#c
let mbeh =
  on (mwhole) (fun (| _, mw |) -> _beh (mw ()))

let mlang : language trace_property = {
  interface = mlang_int;
  ctx       = mctx;
  pprog     = mprog;
  whole     = mwhole;
  link      = mlink;
  beh       = mbeh;
}

let cint (i:ilang_int) : mlang_int = {
  ctx_in = i.ctx_in;
  ctx_out = i.ctx_out;
  prog_out = i.prog_out;
}

let ilang_to_mlang : compiler trace_property = {
  source = ilang;
  target = mlang;
  cint = cint;
  compile_pprog = (fun #i sp -> 
    compile_prog #i.vpi sp i.vpi #(r_pi i.vpi))
}

let bc_rrhc = BeyondCriteria.rrhc trace_property ilang_to_mlang
let my_rrhc = forall i c. RrHP.rrhc i c

let equivalence () : Lemma (bc_rrhc <==> my_rrhc) by (
  explode ();
  ExtraTactics.rewrite_lemma 2 3;
  norm [delta_only [`%bc_rrhc; `%my_rrhc;`%BeyondCriteria.rrhc;`%RrHP.rrhc];iota];
  explode ();
  dump "H"
)= ()
