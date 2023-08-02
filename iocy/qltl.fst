module QLTL

open FStar.Tactics
open FStar.List.Tot.Base

/// Quantified Linear Temporal logic on sets of finite traces [trs: list (list s)]
/// 
/// We define the quantifier [quant] and ltl syntax [ltl_syntax].
type quant =
| Forall
| Exists

noeq
type ltl_syntax (s:Type0) =
| Eventually : ltl_syntax s -> ltl_syntax s
| Always: ltl_syntax s -> ltl_syntax s
| And: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Or: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Impl: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Now: (s -> Type0) -> ltl_syntax s

let rec suffixes_of (l:list 'a) : list (list 'a) =
  match l with
  | [] -> []
  | h::tl -> l :: suffixes_of tl

/// Does a finite trace [tr: list s] satisfy an ltl formula [form]
let rec ltl_denote (#s: Type0)(form: ltl_syntax s)(tr: list s): Type0 =
  match form with
  | Now p -> ~(tr == []) /\ p (hd tr)
  | Eventually p -> exists (tl:list s). tl `memP` suffixes_of tr /\ ltl_denote p tl
  | Always p -> forall (tl:list s). tl `memP` suffixes_of tr ==> ltl_denote p tl
  | And p q -> ltl_denote p tr /\ ltl_denote q tr
  | Or p q -> ltl_denote p tr /\ ltl_denote q tr
  | Impl p q -> ltl_denote p tr ==> ltl_denote q tr

/// Quantified LTL formula
type qltl_formula s = quant * ltl_syntax s

/// Satisfiability of a QLTL formula over sets of finite traces [trs] (non-empty)
let qltl_denote (form: qltl_formula 'a) (trs: list (list 'a) {Cons? trs}) : Type0 =
  match form with
  | (Forall, p) -> forall t. t `memP` trs ==> ltl_denote p t
  | (Exists, p) -> exists (t:list 'a). t `memP` trs /\ ltl_denote p t

// Some assertions
let _ = assert(qltl_denote (Forall, Eventually (Now (fun n -> n % 2 == 1))) [[0; 1]; [3]])
let _ = assert(qltl_denote (Forall, Always (Now (fun n -> n % 2 == 1))) [[1]; [3]]) 

let _ = assert(qltl_denote (Exists, Always (Now (fun n -> n % 2 == 1))) [[4]; [6]; [2]; [1]; [2]]) 
 // by (norm [delta_only [`%qltl_denote;`%ltl_denote;`%suffixes_of];zeta;iota]; dump "H")
 by (witness (`([1])); dump "H")

// Should fail
[@expect_failure]
let _ = assert(qltl_denote (Forall, Eventually (Now (fun n -> n % 2 == 0))) [[1;3]; [1]])

// Test if 1 is followed by 2
// CA: is this how one writes it?
let _ = assert (
  qltl_denote (Forall, Always (Impl (Now (fun n -> n == 1)) (Eventually (Now (fun n -> n == 2))))) [
        [0; 1; 2; 5; 6];
        [0; 1; 5; 2; 6];
        [0; 5; 1; 2; 6];
        [5; 0; 1; 2; 6]
      ])

// TODO: why is this working?
[@expect_failure]
let _ = assert (
  qltl_denote (Forall, Always (Impl (Now (fun n -> n == 0)) (Eventually (Now (fun n -> n == 5))))) [
        [0; 1; 2; 5; 6];
        [0; 1; 5; 2; 6];
        [0; 5; 1; 2; 6];
        [5; 0; 1; 2; 6]
      ])
