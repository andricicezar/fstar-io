module MLInterop

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Exn
open FStar.All

open Common
open IO.ML
open IOStHist


(** ** `ml` class *)
(* Intuition, this are morally ML types written in F* syntax *)

class ml (t:Type) = { mldummy : unit }

// Basic ML types
instance ml_unit : ml unit = { mldummy = () }
instance ml_bool : ml bool = { mldummy = () }
instance ml_int : ml int = { mldummy = () }
instance ml_string : ml string = { mldummy = () }

instance ml_pair t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 * t2) = { mldummy = () }

instance ml_mlarrow t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 -> ML t2) = { mldummy = () }
instance ml_mlarrow2 t1 t2 t3 [| ml t1 |] [| ml t2 |] [| ml t3 |] : ml (t1 -> t2 -> ML t3) = { mldummy = () } (* not good! *)

(* Could also define this as an inductive: *)

type is_ml : Type -> Type0 =
| ML_unit : is_ml unit
| ML_bool : is_ml bool
| ML_int : is_ml int
| ML_string : is_ml string
(* | ML_pair : a:Type -> b:Type -> is_ml a -> is_ml b -> is_ml (a*b) *)
(* | ML_arrow : a:Type -> b:Type -> is_ml a -> is_ml b -> is_ml (a -> ML b) *)

type mlish : Type = t:Type{is_ml t}

(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
- the types of values we can safely `import` from malicious ML code
- the types of values we can safely `export` to malicious ML code
This interoperability model includes extraction as well as
adding extra checking and wrapping.
*)

exception Contract_failure

class exportable (t : Type) = { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) = { itype : Type; import : itype -> Ex t; ml_itype : ml itype }

let mk_exportable (#t1 t2 : Type) [|ml t2|] (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }
let mk_importable (t1 #t2 : Type) [|ml t1|] (imp : t1 -> Ex t2) : importable t2 =
  { itype = t1; import = imp;  ml_itype = solve }

instance ml_exportable (#t : Type) (d : exportable t) : ml (d.etype) = d.ml_etype
instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance exportable_ml t [| ml t|] : exportable t = mk_exportable t (fun x -> x)
instance importable_ml t [| ml t|] : importable t = mk_importable t (fun x -> x)

instance exportable_refinement t [| d:exportable t |] (p : t -> Type0)  : exportable (x:t{p x})
= mk_exportable (d.etype) export // TODO: Eta expanding causes type error

class decidable (#t:Type) (p : t -> Type0) = { dec : (x:t -> b:bool{b <==> p x}) }
class checkable (#t:Type) (p : t -> Type0) = { check : (x:t -> b:bool{b ==> p x}) }
instance general_is_checkeable t (p : t -> bool) : checkable (fun x -> p x) = { check = fun x -> p x }

instance checkable_decidable (#t:Type) (p : (t -> Type0)) [| decidable p|] : checkable p =
  { check = fun (x:t) -> dec #t #p x }

class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) = { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkeable2 t1 t2 (p : t1 -> t2 -> bool) : checkable2 (fun x y -> p x y) = { check2 = fun x y -> p x y}

instance importable_refinement t [| d:importable t |] (p : t -> Type0) [| checkable p |] : importable (x:t{p x}) 
= mk_importable (d.itype)
    (fun (x:d.itype) -> let x : t = import x in
                        if check #t #p x then x <: Ex (x:t{p x}) else raise Contract_failure)
    (* TODO: quite a few type annotations needed above *)

instance exportable_pair t1 t2 [| d1:exportable t1 |] [| d2:exportable t2 |] : exportable (t1 * t2) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

instance importable_pair t1 t2 [| d1:importable t1 |] [| d2:importable t2 |] : importable (t1 * t2) =
  mk_importable (d1.itype * d2.itype) (fun (x,y) -> (import x, import y) <: Ex (t1 * t2))

instance importable_dpair_refined t1 t2 (p:t1 -> t2 -> Type0)
  [| d1:importable t1 |] [| d2:importable t2 |] [| d3:checkable2 p |] : importable (x:t1 & y:t2{p x y}) =
  mk_importable (d1.itype & d2.itype) #(x:t1 & y:t2{p x y})
    (fun ((x', y')) ->
        let (x : t1) = import x' in
        let (y : t2) = import y' in
        (if check2 #t1 #t2 #p x y then (| x, y |) 
        else raise Contract_failure) <: (x:t1 & y:t2{p x y}))

// A typed term in an untyped context
instance exportable_arrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))
  
instance exportable_exarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> Ex t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->Ex t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))

instance exportable_mlarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> ML t2)  =
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(t1->ML t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: ML d2.etype))

// An untyped term in a typed context
instance importable_mlarrow t1 t2 [| d1:exportable t1 |] [| d2:importable t2 |] : importable (t1 -> ML t2)  =
  mk_importable (d1.etype -> ML d2.itype)
    (fun (f:(d1.etype -> ML d2.itype)) -> (fun (x:t1) -> import (f (export x)) <: ML t2))
  
// Example trueish
let trueish (x:int{x >= 0}) : bool = true
let trueish' (x:int) : ML bool = (trueish (import x))
let trueish'' : int -> ML bool = export trueish

instance importable_darrow_refined t1 t2 (p:t1->t2->Type0)
  [| d1:exportable t1 |] [| d2:importable t2 |] [| d3:checkable2 p |] : importable (x:t1 -> ML (y:t2{p x y})) =
  mk_importable (d1.etype -> ML d2.itype) #(x:t1 -> ML (y:t2{p x y}))
    (fun (f:(d1.etype -> ML d2.itype)) -> 
      (fun (x:t1) -> 
        let y : t2 = import (f (export x)) in
          (if check2 #t1 #t2 #p x y then y 
           else raise Contract_failure) <: ML (y:t2{p x y})))

// Example incr

let incr (x:int) : int = x + 1

val incr' : (x:int) -> ML (y:int{y = x + 1})
let incr' = import incr

let incr'' (x:int) : ML (y:int{y = x + 1}) = import (incr x)


instance exportable_purearrow_spec t1 t2 (pre : t1 -> Type0) (post : t1 -> t2 -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d3:checkable pre |] : exportable ((x:t1) -> Pure t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(x:t1 -> Pure t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = import x in
        (if check #t1 #pre x then (
          export (f x)
        ) else raise Contract_failure) <: ML d2.etype))

// Example incrs
let postcond (x:int) (y:int) : Type0 = y = x + 1
let incrs1 : (x:int) -> Pure int (x > 0) (postcond x) = fun x -> x + 1
let incrs1' : int -> ML int = export incrs1

let incrs2  : (x:int) -> Pure int (x > 0) (fun (y:int) -> y = x + 1) = fun x -> x + 1
let incrs2' : int -> ML int = export incrs2

// this does not work for some reason (see github issue FStarLang/FStar #2006):
// let incrs3  : (x:int) -> Pure int (x > 0) (fun y -> y = x + 1) = fun x -> x + 1
// let incrs3' : int -> ML int = export incrs3'

// even if it checks, I don't think it makes sense
// let heap = FStar.Heap.heap
// instance exportable_starrow_spec t1 t2 (pre : t1 -> heap -> Type0) (post : t1 -> heap -> t2 -> heap -> Type0)
//   [| d1:importable t1 |] [| d2:exportable t2 |] [| d3:checkable2 pre |] : exportable ((x:t1) -> ST t2 (pre x) (post x)) = 
//   mk_exportable (d1.itype -> ML d2.etype)
//     (fun (f:(x:t1 -> ST t2 (pre x) (post x))) ->
//       (fun (x:d1.itype) ->
//         let x : t1 = import x in
//         // ST.get is not implemented
//         let h0 : heap = ST.get () in
//         (if check2 #t1 #heap #pre x h0 then (
//           assume (ST.get () == h0);
//           export (f x)
//         ) else raise Contract_failure) <: ML d2.etype))

// Example stiy
// let stiy_pre (x:ℤ) (h0:heap) : Type0 = True
// let stiy_post (x:ℤ) (h0:heap) (r:ℤ) (h1:heap) : Type0 = True
// let stiy (x:ℤ) : ST ℤ (stiy_pre x) (stiy_post x) = x

// Does not work
// let stiy' : int -> ML int = export stiy

let rec exportableSys t1 [| d1:exportable t1 |] (x: sys io_cmds io_cmd_sig t1) : ML d1.etype = match x with
      | Return r -> export r
      | Throw r -> raise r 
      | Cont (Call cmd argz fnc) ->
          let rez = ml_io_execute cmd argz in
          IOStHist.update_history (convert_call_to_event cmd argz rez);
          let z' : sys io_cmds io_cmd_sig t1 = fnc rez in
          exportableSys _ z'


instance exportable_sys t1 [| d1:exportable t1 |] : exportable (sys io_cmds io_cmd_sig t1) =
  mk_exportable (unit -> ML d1.etype) 
    (fun (x:sys io_cmds io_cmd_sig t1) -> 
      fun _ -> exportableSys _ x)

// IOStHist is IO with materialized history 

let reify2 (a:Type) 
  (pre:(events_trace->Type0)) 
  (post:(events_trace->(maybe (events_trace*a))->events_trace->Type0))
  (f:(unit -> IOStHist a pre post)) 
  (s0:events_trace)
  : 
    Pure (io (events_trace * a)) 
      (pre s0) 
      (fun x -> iohist_interpretation x s0 (fun r le -> post s0 r le)) 
 = admit (); reify (f ()) s0 

instance ml_file_descr : ml file_descr = { mldummy = () }

instance exportable_IOStHist_arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d4:checkable2 pre |] : exportable ((x:t1) -> IOStHist t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(x:t1 -> IOStHist t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = import x in
        let s0 : events_trace = IOStHist.get_history () in
        (if check2 #t1 #events_trace #pre x s0 then (
          let z = reify2 t2 (pre x) (post x) (fun () -> f x) in
          let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
          z' ()
        ) else raise Contract_failure) <: ML d2.etype))

instance ml_check_type : ml check_type = { mldummy = () }

instance exportable_IOStHist_2arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d4:checkable2 pre |] : exportable ((pi:check_type) ->(x:t1) ->  IOStHist t2 (pre x) (post x)) = 
  mk_exportable (check_type -> d1.itype -> ML d2.etype)
    (fun (f:(check_type -> x:t1 -> IOStHist t2 (pre x) (post x))) ->
      (fun pi (x:d1.itype) ->
        let x : t1 = import x in
        let s0 : events_trace = IOStHist.get_history () in
        (if check2 #t1 #events_trace #pre x s0 then (
          let z = reify2 t2 (pre x) (post x) (fun () -> f pi x) in
          let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
          z' ()
        ) else raise Contract_failure) <: ML d2.etype))

instance exportable_IOStHist_3arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> check_type -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d4:checkable2 pre |] : exportable ((pi:check_type) ->(x:t1) ->  IOStHist t2 (pre x) (post x pi)) = 
  mk_exportable (check_type -> d1.itype -> ML d2.etype)
    (fun (f:((pi:check_type) -> x:t1 -> IOStHist t2 (pre x) (post x pi))) ->
      (fun pi (x:d1.itype) ->
        let x : t1 = import x in
        let s0 : events_trace = IOStHist.get_history () in
        (if check2 #t1 #events_trace #pre x s0 then (
          let z = reify2 t2 (pre x) (post x pi) (fun () -> f pi x) in
          let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
          z' ()
        ) else raise Contract_failure) <: ML d2.etype))

// let general_cmd
//   (pi_check : check_type)
//   (t:string) :
//   IOStHistInv unit pi_check
//     (requires (fun s0 -> True))
//     (ensures (fun _ _ _ -> True)) = admit() 

// let ladf = export general_cmd 

// should be able to export with is_default_check_dynamic to false?
// therefore meaning that the precondition is not respected...
// instance exportable_GIOPrePost_arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
//   [| d1:importable t1 |] [| d2:exportable t2 |] [| d4:checkable2 pre |] : exportable ((pi:check_type) -> (is_default_check_dynamic:bool) -> (x:t1) -> GIOPrePost t2 is_default_check_dynamic pi (pre x) (post x)) by (explode (); dump "h")  = 
//   mk_exportable (check_type -> d1.itype -> ML d2.etype)
//     (fun (f:((pi:check_type) -> (is_default_check_dynamic:bool) -> (x:t1) -> GIOPrePost t2 is_default_check_dynamic pi (pre x) (post x))) ->
//       (fun pi (x:d1.itype) ->
//         let x : t1 = import x in
//         let s0 : events_trace = IOStHist.get_history () in
//         (if fold_left (default_check) s0 && 
//             fold_left (pi) s0 &&
//             check2 #t1 #events_trace #pre x s0 then (
//             let z = reify2 t2 (fun s0 -> (fold_left (default_check) s0) /\ 
//             (fold_left (pi) s0) /\ (pre x s0)) (post x) (fun () -> f pi true x) in
//             let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
//             z' ()
//         ) else raise Contract_failure) <: ML d2.etype))


instance exportable_GIO_arrow_spec t2
   [| d2:exportable t2 |] : exportable ((pi_check:check_type) -> GIO t2 pi_check) = 
  mk_exportable (check_type ->  ML d2.etype)
    (fun (f:(pi_check:check_type ->  GIO t2 pi_check)) ->
      (fun (pi_check:check_type) ->
        let s0 : events_trace = IOStHist.get_history () in
        (if fold_left (default_check) s0 && fold_left (pi_check) s0 then (
            let z = reify2 t2 (fun s0 -> (fold_left (default_check) s0 /\ fold_left (pi_check) s0)) (fun _ _ _ -> True) (fun () -> f pi_check) in
            let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
            z' ()
        ) else raise Contract_failure) <: ML d2.etype))

instance exportable_GIO_2arrow_spec t1 t2
  [| d1:importable t1 |] [| d2:exportable t2 |] : exportable ((pi_check:check_type) -> (x:t1) -> GIO t2 pi_check) = 
  mk_exportable (check_type -> d1.itype -> ML d2.etype)
    (fun (f:(pi_check:check_type -> x:t1 -> GIO t2 pi_check)) ->
      (fun (pi_check:check_type) (x:d1.itype) ->
        let x : t1 = import x in
        let s0 : events_trace = IOStHist.get_history () in
        (if fold_left (default_check) s0 && fold_left (pi_check) s0 then (
            let z = reify2 t2 (fun s0 -> (fold_left (default_check) s0 /\ fold_left (pi_check) s0)) (fun _ _ _ -> True) (fun () -> f pi_check x) in
            let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
            z' ()
        ) else raise Contract_failure) <: ML d2.etype))


// instance exportable_GIO_3arrow_spec (cmd:io_cmds) [| d1:importable (args cmd) |] [| d2:exportable (res cmd) |]  : exportable (cmd':io_cmds{cmd'=cmd} -> (pi:check_type) -> (x:args cmd) -> GIO (res cmd) pi) = 
//   mk_exportable (cmd':io_cmds{cmd'=cmd} -> check_type -> d1.itype -> ML d2.etype)
//     (fun (f:((cmd':io_cmds{cmd'=cmd}) -> pi:check_type -> x:(args cmd) -> GIO (res cmd) pi)) ->
//       (fun cmd' (pi:check_type) (x:d1.itype) ->
//         let x : args cmd' = import x in
//         let s0 : events_trace = IOStHist.get_history () in
//         (if fold_left (default_check) s0 then (
//             let z = reify2 (res cmd') (fun s0 -> (fold_left (default_check) s0)) (fun _ _ _ -> True) (fun () -> f cmd pi x) in
//             let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
//             z' ()
//         ) else raise Contract_failure) <: ML d2.etype))
