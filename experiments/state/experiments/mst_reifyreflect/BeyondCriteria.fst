module BeyondCriteria

open FStar.Classical.Sugar
open FStar.Tactics
open FStar.List.Tot
open FStar.Tactics.Typeclasses
open FStar.FunctionalExtensionality

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
type language (sem:Type u#e) = {
  interface : Type u#a;
  pprog : interface -> Type u#b;
  ctx   : interface -> Type u#c;
  whole : Type u#d;
  link  : #i:interface -> pprog i -> ctx i -> whole;

  beh   : whole ^-> sem;
}

noeq
type compiler = {
  src_sem : Type u#e;
  tgt_sem : Type u#j;
  source : language u#e u#a u#b u#c u#d src_sem;
  target : language u#j u#f u#g u#h u#i tgt_sem;

  comp_int   : source.interface -> target.interface;

  rel_sem : src_sem -> tgt_sem -> Type0;

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
          comp.source.beh (ps `comp.source.link #i` cs) `comp.rel_sem` comp.target.beh (comp.compile_pprog #i ps `comp.target.link #(comp.comp_int i)` ct)

let scc (comp:compiler) (compile_ctx:(#i:_ -> comp.source.ctx i -> comp.target.ctx (comp.comp_int i))) ((⊆):comp.tgt_sem -> comp.src_sem -> Type0): Type0 =
  forall (i:comp.source.interface).
    forall (cs:comp.source.ctx i).
      forall (ps:comp.source.pprog i).
        comp.target.beh (comp.compile_pprog #i ps `comp.target.link #(comp.comp_int i)` compile_ctx #i cs) ⊆ comp.source.beh (ps `comp.source.link #i` cs)
  
