module BeyondCriteria

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

(** ** Trace Model *)
(* Inspired from
   * https://github.com/secure-compilation/exploring-robust-property-preservation/blob/master/TraceModel.v
   * https://github.com/secure-compilation/exploring-robust-property-preservation/blob/master/Properties.v *)

(* F* does not have co-induction *)
let stream a = nat ^-> a

noeq
type trace (#event_typ:Type) =
| Finite_trace : tr:(list event_typ) * result:int -> trace #event_typ
| Infinite_trace : stream (option event_typ) -> trace #event_typ

type trace_property (#event_typ:Type) = trace #event_typ -> Type0

type hyper_trace_property (#event_typ:Type) = trace_property #event_typ -> Type0

(** ** Language Record *)
(*
Record language :=
  {
    int  : Set;
    par  : int -> Set;  (* partial programs *)
    ctx  : int -> Set;  (* context *)
    prg  : Set;  (* whole programs *)
    plug : forall {i:int}, par i -> ctx i -> prg;
    sem  : prg -> prop;
    non_empty_sem : forall W, exists t, sem W t
  }.

Axiom src : language.
Axiom tgt : language.

Axiom cint : int src -> int tgt.

Axiom compile_par : forall {i}, (par src i) -> (par tgt (cint i)).
*)

noeq
type language = {
  interface : Type u#a;
  pprog : interface -> Type u#b;
  ctx   : interface -> Type u#c;
  whole : Type u#d;
  link  : #i:interface -> pprog i -> ctx i -> whole;

  event_typ : Type u#e;
  beh   : whole ^-> trace_property #event_typ;
}

noeq
type compiler = {
  source : language u#a u#b u#c u#d u#e;
  target : language u#f u#g u#h u#i u#j;

  comp_int   : source.interface -> target.interface;

  rel_traces : trace_property #source.event_typ -> trace_property #target.event_typ -> Type0;

  compile_pprog : #i:source.interface -> source.pprog i -> target.pprog (comp_int i);
}

let chain_compilers (c1:compiler) (c2:compiler{c1.target == c2.source}) : r:compiler{c1.source == r.source /\ c2.target == r.target } = {
  source = c1.source;
  target = c2.target;
  comp_int = (fun (i:c1.source.interface) -> c2.comp_int (c1.comp_int i));

  rel_traces = (fun ts tt -> forall ti. c1.rel_traces ts ti <==> c2.rel_traces ti tt);

  compile_pprog = (fun #i ps -> c2.compile_pprog (c1.compile_pprog ps));
}

(**
Definition RrHC : Prop :=
  forall (Ct:ctx tgt (cint i)),
  exists (Cs:ctx src i),
  forall (P:par src i), sem src (Cs [P]) = sem tgt (Ct [P ↓]).
**)

let rrhc (comp:compiler) : Type0 =
  forall (i:comp.source.interface).
    forall (ct:comp.target.ctx (comp.comp_int i)).
      exists (cs:comp.source.ctx i).
        forall (ps:comp.source.pprog i).
          comp.source.beh (ps `comp.source.link` cs) `comp.rel_traces` comp.target.beh (comp.compile_pprog ps `comp.target.link` ct)
