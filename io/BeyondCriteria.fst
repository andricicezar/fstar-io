module BeyondCriteria

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

#set-options "--print_universes"

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
type language (semantics:Type u#a) = {
  interface : Type u#b;
  pprog : interface -> Type u#c;
  ctx   : interface -> Type u#d;
  whole : Type u#e;
  link  : #i:interface -> pprog i -> ctx i -> whole;
  beh   : whole ^-> semantics;
}

noeq
type compiler (semantics:Type u#a) = {
  source : language u#a u#b u#c u#d u#e semantics;
  target : language u#a u#f u#g u#h u#i semantics;
  cint   : source.interface -> target.interface;
  
  compile_pprog : #i:source.interface -> source.pprog i -> target.pprog (cint i);
}

(**
Definition RrHC : Prop :=
  forall (Ct:ctx tgt (cint i)),
  exists (Cs:ctx src i),
  forall (P:par src i), sem src (Cs [P]) = sem tgt (Ct [P ↓]).
**)

let rrhc (semantics:Type) (comp:compiler semantics) : Type0 =
  forall (i:comp.source.interface).
    forall (ct:comp.target.ctx (comp.cint i)).
      exists (cs:comp.source.ctx i).
        forall (ps:comp.source.pprog i).
          comp.source.beh (ps `comp.source.link` cs) == comp.target.beh (comp.compile_pprog ps `comp.target.link` ct)
