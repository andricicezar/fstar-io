(** Proof of concept: does the universe problem we hit in F*
    (experiments/state_on_io) exist in Rocq?

    In F*, CGetHeap could not be a constructor of the Type0-indexed command
    GADT [mst_cmds], because (erased) heap lives in universe 1 and F*'s
    universes are NOT cumulative: an index forces the index universe to
    match it exactly, so the Type0 results (CRead's [b], unit, ...) pin the
    index universe to 0 and [heap] cannot appear. We had to:
      - give CGetHeap its own command type  heap_cmds : Type u#1 -> Type u#2;
      - lift mst_cmds and guard_cmd to index universe 1 with a wrapper
        (cmd_downgrade + FStar.Universe.raise_t/downgrade_val);
      - recover the GADT index equality (r == erased heap) inside the WP
        functions through SMT inversion + coerce_eq.

    This file replays the same architecture in Rocq. Summary of findings:
      1. Rocq universes are cumulative: constructors only impose LOWER
         bounds on the index universe, so a single index universe
         accommodates results in Type0 (CRead) and results one level up
         (CGetHeap). No downgrade/raise wrapper is needed: cmd_sum applies
         directly to guard_cmd, mst_cmds and heap_cmds. Guards, the MST
         commands and CGetHeap can even live together in one single
         inductive ([mst_cmds_direct] below).
      2. Dependent match with an [in .. return] clause makes the index
         equality definitional in each branch — no coerce_eq analogue.
      3. The F* failure is reproducible only by artificially pinning the
         index universe to the bottom (Set) — see the [Fail] command in
         Section 5.

    To compile:  rocq compile UniversesPoC.v   (Rocq >= 9)
            or:  coqc UniversesPoC.v           (Coq 8.x)
*)

Set Printing Universes.

(* Without this, Rocq auto-lowers heap_cmds into Prop (it is a syntactic
   singleton: one argument-less constructor), despite the declared Type
   arity. Not-lowering will become the default in a future version; on
   Coq 8.x this line only emits an unknown-option warning and can be
   removed. *)
Unset Automatic Proposition Inductives.

(** * Section 0: a heap that must live above Type0.
    Like FStar.Monotonic.Heap, cells store values of arbitrary (small)
    types, which forces the heap one universe up. *)

Definition cell : Type := { A : Type & A }.
Definition heap : Type := list cell.

(* heap : Type@{u+1} — strictly above the universe of the stored types *)
Check heap.

(* References: an address with a phantom type. Enough for the universe
   question; no actual heap semantics needed. *)
Definition mref (b : Type) : Type := nat.

(** * Section 1: free monad + command sum (mirrors Free.fst) *)

Inductive caller : Set := Prog | Ctx.

Inductive cmd_sum (cmd1 cmd2 : Type -> Type) : Type -> Type :=
| CmdL : forall r : Type, cmd1 r -> cmd_sum cmd1 cmd2 r
| CmdR : forall r : Type, cmd2 r -> cmd_sum cmd1 cmd2 r.
Arguments CmdL {cmd1 cmd2 r} _.
Arguments CmdR {cmd1 cmd2 r} _.

Inductive free (cmd : Type -> Type) (a : Type) : Type :=
| Call : forall r : Type, caller -> cmd r -> (r -> free cmd a) -> free cmd a
| Ret  : a -> free cmd a.
Arguments Call {cmd a r} _ _ _.
Arguments Ret {cmd a} _.

(** * Section 2: the commands (mirrors GuardedDMFree.fst / MST.Repr.fst) *)

Inductive guard_cmd : Type -> Type :=
| GCmd : forall pre : Prop, guard_cmd pre.

Inductive mst_cmds : Type -> Type :=
| CRead    : forall b : Type, mref b -> mst_cmds b
| CWrite   : forall b : Type, mref b -> b -> mst_cmds unit
| CAlloc   : forall b : Type, b -> mst_cmds (mref b)
| CWitness : (heap -> Prop) -> mst_cmds unit
| CRecall  : (heap -> Prop) -> mst_cmds unit.

(* The get_heap command in its own command type, as in the F* development
   after the refactoring ... *)
Inductive heap_cmds : Type -> Type :=
| CGetHeap : heap_cmds heap.

(* ... but note that in Rocq it could also live directly next to the
   Type0-resulting commands — and the guards — in one single inductive:
   cumulativity lifts the small indices (pre : Prop, b, unit) into the
   index universe required by heap. This is exactly the declaration that
   F* rejects: there, the Type0 indices pin the index universe to 0 and
   erased heap : Type u#1 cannot appear. *)
Inductive mst_cmds_direct : Type -> Type :=
| DGuard   : forall pre : Prop, mst_cmds_direct pre
| DRead    : forall b : Type, mref b -> mst_cmds_direct b
| DGetHeap : mst_cmds_direct heap.

(* A program using all three kinds of operations from the single GADT,
   without any cmd_sum or universe-lifting wrapper. *)
Example prog_direct : free mst_cmds_direct nat :=
  Call Prog (DRead nat 0) (fun n =>
  Call Prog (DGuard True) (fun _ =>
  Call Prog DGetHeap (fun h =>
  Ret (length h)))).

(* The combined commands. In F* this needed
     cmd_sum (cmd_downgrade guard_cmd) (cmd_sum (cmd_downgrade mst_cmds) heap_cmds)
   with raise_t/downgrade_val plumbing; in Rocq the sum applies as-is. *)
Definition mst_all_cmds : Type -> Type := cmd_sum mst_cmds heap_cmds.
Definition gmst_cmds    : Type -> Type := cmd_sum guard_cmd mst_all_cmds.

(* Programs freely mixing guards, Type0 commands and get_heap. *)
Example prog_get_heap : free gmst_cmds heap :=
  Call Prog (CmdR (CmdR CGetHeap)) (fun h => Ret h).

Example prog_mixed : free gmst_cmds nat :=
  Call Prog (CmdR (CmdL (CRead nat 0))) (fun n =>
  Call Prog (CmdL (GCmd True)) (fun _ =>
  Call Prog (CmdR (CmdR CGetHeap)) (fun h =>
  Ret (length h)))).

(** * Section 3: WP functions — the GADT index equality is definitional.
    (hist over a stand-in event type; semantics irrelevant here) *)

Definition event : Set := nat.

Definition hist_post (a : Type) : Type := list event -> a -> Prop.
Definition hist (a : Type) : Type := hist_post a -> list event -> Prop.

Definition current_heap (h : list event) : heap := nil. (* stand-in *)

Definition cmd_wp (cmd : Type -> Type) : Type :=
  forall r : Type, caller -> cmd r -> hist r.

(* In F*, this match needed SMT inversion + coerce_eq to transport the
   result along r == erased heap. In Rocq the [in .. return] clause gives
   the branch the precise index type, definitionally. *)
Definition heap_cwp : cmd_wp heap_cmds :=
  fun r c op =>
    match op in heap_cmds r' return hist r' with
    | CGetHeap => fun p h => p nil (current_heap h)
    end.

Definition guard_cwp : cmd_wp guard_cmd :=
  fun r c op =>
    match op in guard_cmd r' return hist r' with
    | GCmd pre => fun p h => pre /\ (forall prf : pre, p nil prf)
    end.

Definition mst_cwp : cmd_wp mst_cmds :=
  fun r c op =>
    match op in mst_cmds r' return hist r' with
    | CRead b rf    => fun p h => forall v : b, p nil v
    | CWrite b rf v => fun p h => p nil tt
    | CAlloc b v    => fun p h => forall rf : mref b, p nil rf
    | CWitness prd  => fun p h => p nil tt
    | CRecall prd   => fun p h => p nil tt
    end.

Definition cmd_wp_sum {cmd1 cmd2 : Type -> Type}
  (cwp1 : cmd_wp cmd1) (cwp2 : cmd_wp cmd2) : cmd_wp (cmd_sum cmd1 cmd2) :=
  fun r c op =>
    match op in cmd_sum _ _ r' return hist r' with
    | CmdL op1 => cwp1 _ c op1
    | CmdR op2 => cwp2 _ c op2
    end.

(** * Section 4: theta, to check everything composes at these universes *)

Definition hist_return {a : Type} (x : a) : hist a :=
  fun p _ => p nil x.

Fixpoint rev' {A : Type} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => app (rev' xs) (cons x nil)
  end.

Definition hist_bind {a b : Type} (w : hist a) (k : a -> hist b) : hist b :=
  fun p h =>
    w (fun lt r => k r (fun lt' r' => p (app lt lt') r') (app (rev' lt) h)) h.

Fixpoint theta {cmd : Type -> Type} {a : Type}
  (cwp : cmd_wp cmd) (m : free cmd a) {struct m} : hist a :=
  match m with
  | Ret x => hist_return x
  | Call c op k => hist_bind (cwp _ c op) (fun x => theta cwp (k x))
  end.

Definition gmst_cwp : cmd_wp gmst_cmds :=
  cmd_wp_sum guard_cwp (cmd_wp_sum mst_cwp heap_cwp).

(* Sanity: the WPs compute on the mixed programs. *)
Goal theta gmst_cwp prog_get_heap (fun _ _ => True) nil.
Proof. cbn. exact I. Qed.

Goal theta gmst_cwp prog_mixed (fun _ _ => True) nil.
Proof. cbn. intros v. tauto. Qed.

(** * Section 5: reproducing the F* failure.
    The problem reappears only if the index universe is pinned to the
    bottom (Set) — which is what F*'s non-cumulative Type0-indexed
    [mst_cmds] amounts to. [Fail] succeeds iff the declaration is
    rejected; the printed message should be a universe inconsistency. *)

Fail Inductive bad_cmds : Set -> Type :=
| BadGetHeap : bad_cmds heap.

(* Inspect the inferred universes/constraints of the direct declaration. *)
Print mst_cmds_direct.
