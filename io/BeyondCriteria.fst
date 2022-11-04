module BeyondCriteria

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

#set-options "--print_universes"

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
  interface : Type u#b;
  pprog : interface -> Type u#c;
  ctx   : interface -> Type u#d;
  whole : Type u#e;
  link  : #i:interface -> pprog i -> ctx i -> whole;

  event_typ : Type u#f;
  beh   : whole ^-> trace_property #event_typ;
}

noeq
type compiler = {
  source : language u#a u#b u#c u#d u#e;
  target : language u#a u#f u#g u#h u#i;

  comp_int   : source.interface -> target.interface;

  rel_traces : trace_property #source.event_typ -> trace_property #target.event_typ -> Type0;

  compile_pprog : #i:source.interface -> source.pprog i -> target.pprog (comp_int i);
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