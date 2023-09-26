module MLInterop

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Exn
open FStar.All

open Common
open IO.ML
open IOStHist


(** ** `public` and `tainted` classes *)
(* Intuition, without extra checking and wrapping:
- the types we can safely import from malicious ML code have to be `tainted`
- the types we can safely export to malicious ML code have to be `public`
This interoperability model is all *up to extraction*,
but again without adding extra checking and wrapping.
*)

class public (t:Type) = { pdummy : unit }
class tainted (t:Type) = { tdummy : unit }


// TODO: How to properly declare empty type classes?
// GM: I should add that.

// TODO: Any way to declare "sealed type classes"? Or more generally,
//       restricting who can add new instances, since it's a dangerous operation
// GM: Not in any very robust way. We don't have "real" typeclasses as in
//     Haskell. Instead we have 1) custom implicit argument resolution and
//     2) a bunch of sugar. I think there's a way by making the class private
//     and using a proxy, but not sure it's bulletproof. In any case I'd be wary
//     of using typeclasses to enforce any kind of invariant.

let is_public t [| public t |] = ()
let is_tainted t [| tainted t |] = ()

// Basic ML types are all public and tainted
instance public_unit : public unit = { pdummy = () }
instance tainted_unit : tainted unit = { tdummy = () }
instance public_bool : public bool = { pdummy = () }
instance tainted_bool : tainted bool = { tdummy = () }
instance public_int : public int = { pdummy = () }
instance tainted_int : tainted int = { tdummy = () }
instance public_string : public string = { pdummy = () }
instance tainted_string : tainted string = { tdummy = () }

// Refinement types are public, but only trivial refinements are tainted
instance public_refined t p [| public t |] : public (x:t{p x}) = { pdummy = () }
instance tainted_refined t [| tainted t |] : tainted (x:t{True}) = { tdummy = () }

let untainted = x:int{x = 42}

let _ = is_public (x:int{x = 42}); is_tainted (x:int{True})

(* let _ = is_public untainted -- TODO: this should work, why are things not unfolded *)
(* GM: This is the unifier failing to unify `x:int{x = 42}` with `x:?t{?p x}`. Will look into it.
       Also reminds me of #1486 *)

(* [@(expect_failure)] -- TODO: the code below does fail, but this expect_failure blows up
let _ = is_tainted untainted *)

// Non-dependent pairs work pointwise
instance public_pair t1 t2 [| public t1 |] [| public t2 |] : public (t1 * t2) = { pdummy = () }
instance tainted_pair t1 t2 [| tainted t1 |] [| tainted t2 |] : tainted (t1 * t2) = { tdummy = () }
let _ = is_public (int*bool); is_tainted (int*bool)
(* let _ = is_tainted (int*untainted) -- fails as it should *)

// Dependent pairs are not tainted
(* let _ = is_tainted (x:int & (y:int{x = y} -> int)) -- fails as it should *)

// Dependent pairs could be public if we can make it work technically
instance public_dpair t1 t2 (_ : public t1) (f : (x:t1 -> public (t2 x))) : public (x:t1 & (t2 x))
  = { pdummy = () }
  

(* //let _ = is_public (x:int & (y:int{True})) *)
(* // GM: Again the unifier failing to apply public_dpair *)
(* let _ = is_public (x:int & (y:int{True})) #(public_dpair int (fun _ -> int) solve (fun _ -> solve)) *)
(* // GM: ^ that works by giving the types manually *)

// Simple inductives like lists are also co-variant
instance public_list t [| public t |] : public (list t) = { pdummy = () }
instance tainted_list t [| tainted t |] : tainted (list t) = { tdummy = () }
let _ = is_public (list int); is_tainted (list bool)
(* let _ = is_tainted (list untainted) -- fails as it should *)


// TODO: any kind of "deriving" mechanism that could give us instances for all ML-like inductives?
// GM: we've coded up similar things, as in `examples/tactics/Printers.fst`

// Non-dependent arrows are contravariant in arguments and covariant in results, as usual,
// but only ML arrows can be tainted!
instance public_arrow t1 t2 [| tainted t1 |] [| public t2 |] : public (t1 -> t2) = { pdummy = () }
instance public_exarrow t1 t2 [| tainted t1 |] [| public t2 |] : public (t1 -> Ex t2) = { pdummy = () }
instance public_mlarrow t1 t2 [| tainted t1 |] [| public t2 |] : public (t1 -> ML t2) = { pdummy = () }
instance tainted_mlarrow t1 t2 [| public t1 |] [| tainted t2 |] : tainted (t1 -> ML t2) = { tdummy = () }

let _ = is_public (int -> bool); is_public (int -> Ex bool);
        is_public (int -> ML bool); is_tainted (bool -> ML int)
let _ = is_public (bool -> x:int{x = 42}); is_public (bool -> Ex (x:int{x = 42}));
        is_public (bool -> ML (x:int{x = 42})); is_tainted (x:int{x = 42} -> ML int)
(* let _ = is_public ((x:int{x = 42}) -> bool) -- fails as it should *)
(* let _ = is_tainted (int -> x:int{x = 42}) -- fails as it should *)
(* let _ = is_tainted (bool -> int) -- fails as it should *)
(* let _ = is_tainted (x:int{x = 42} -> int) -- fails as it should *)

// Dependent arrows are neither public not tainted ? TODO: think a bit more
(* let _ = is_public (x:int -> y:int{x=42}) -- fails as it should? *)
(* let _ = is_tainted (x:int -> y:int{x=42}) -- fails as it should? *)

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

(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
- the types of values we can safely `import` from malicious ML code
- the types of values we can safely `export` to malicious ML code
This interoperability model includes extraction as well as
adding extra checking and wrapping.
*)

open FStar.Tactics.Typeclasses

exception Contract_failure

(* Foundations of Dependent Interop (Above):
   - internalizes everything (e.g. not relying on extraction, but can't internalize Obj.magic)
   - bundle export and import
   - the have laws, and nice theory
   - compositional: e.g. type_equiv t1 t2 with partial_connection t2 t3 to get partial_connection t1 t3
   - no formalization of things that extracts well (they still try to end with something that extracts well)
   - one t can be connected to many us
*)

(* t is equivalent to u *)
class type_equiv (t u : Type) = {
  fexport : t -> u;
  fimport : u -> t;
  fexport_fimport : x:u -> Lemma (fexport (fimport x) == x);
  fimport_fexport : x:t -> Lemma (fimport (fexport x) == x);
}

(* t is more precise type than u; e.g. t = x:int{x>=0} and u = int *)
class partial_connection (t u : Type) = {
  pexport : t -> u; // erasure, should always succeed
  pimport : u -> option t; // for base types requires cast
  (* pexport_pimport : x:u -> Lemma (bind_option (pimport x) (fun x => Some (pexport x)) == Some x \/ *)
  (*                               bind_option (pimport x) (fun x => Some (pexport x)) == None); *)
  pexport_pimport : x:u -> Lemma (match pimport x with | Some y -> pexport y == x | None -> True);
  pimport_pexport : x:t -> Lemma (pimport (pexport x) == Some x)
}

(* Below:
   - internalizes everything that can be internalized (but could also build on public/private)
   - separate export and import
     + there can be ts for which one can write one but not the other (sealing?)
     + might export to a different type than importing
       (can always export to unit and import from empty)
   - no laws or nice theory
   - less compositional:
     + could compose but only at one end:
       coercible t1 t2 and exportable t2 => exportable t1
       pcoercible t1 t2 and importable t1 => importable t2
   - one t mapped to a single u (but sealing might give us an instance for any type)

Note:
   ml u and partial_connection t u => exportable t and importable t

Different factoring:
class coercible (t u: Type) = { coerce : t -> u }
class pcoercible (t u: Type) = { pcoerce : t -> Ex u }

class exportable (t : Type) = { etype : Type; t_to_etype : coercible t etype; ml_etype : ml etype }
class importable (t : Type) = { itype : Type; itype_to_t : pcoercible itype t; ml_itype : ml itype }
*)

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

let heap = FStar.Heap.heap
instance exportable_starrow_spec t1 t2 (pre : t1 -> heap -> Type0) (post : t1 -> heap -> t2 -> heap -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d3:checkable2 pre |] : exportable ((x:t1) -> ST t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(x:t1 -> ST t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = import x in
        // ST.get is not implemented
        let h0 : heap = ST.get () in
        (if check2 #t1 #heap #pre x h0 then (
          assume (ST.get () == h0);
          export (f x)
        ) else raise Contract_failure) <: ML d2.etype))

// Example stiy
let stiy_pre (x:ℤ) (h0:heap) : Type0 = True
let stiy_post (x:ℤ) (h0:heap) (r:ℤ) (h1:heap) : Type0 = True
let stiy (x:ℤ) : ST ℤ (stiy_pre x) (stiy_post x) = x

// Does not work
// let stiy' : int -> ML int = export stiy

// unfold
// let lift_gio_all (a : Type) (wp : gio_wpty a) (p : all_post a) (h : heap) = wp (fun s0 r le -> p r h)
// sub_effect EXN ~> ALL { lift_wp = lift_exn_all }


unfold
let lift_exn_iosthist (a : Type) (wp : ex_wp a) (s0 : events_trace) (p : iosthist_post a) = wp (fun r ->
  match r with
  | V r' -> p (Inl (s0, r')) []
  | E e -> p (Inr 0) []
  | Err msg -> p (Inr 0) [])
sub_effect EXN ~> IOStHistwp { lift_wp = lift_exn_iosthist }

let rec exportableSys t1 [| d1:exportable t1 |] (x: sys io_cmds io_cmd_sig t1) (hh : ref events_trace) : ML d1.etype = match x with
      | Return r -> export r
      | Throw r -> raise Contract_failure
      | Cont (Call cmd argz fnc) ->
          let rez = io_execute cmd argz in
          hh := (convert_call_to_event cmd argz rez) :: !hh;
          let z' : sys io_cmds io_cmd_sig t1 = fnc rez in
          exportableSys _ z' hh

val hh : ref events_trace
let hh = ST.alloc []

instance exportable_sys t1 [| d1:exportable t1 |] : exportable (sys io_cmds io_cmd_sig t1) =
  mk_exportable (unit -> ML d1.etype) 
    (fun (x:sys io_cmds io_cmd_sig t1) -> 
      fun _ -> exportableSys _ x hh)

instance exportable_IOStHist_arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d4:checkable2 pre |] : exportable ((x:t1) -> IOStHist t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> ML d2.etype)
    (fun (f:(x:t1 -> IOStHist t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = import x in
        let s0 : events_trace = !hh in
        (if check2 #t1 #events_trace #pre x s0 then (
          let z = reify (f x) in
          let z' : unit -> ML d2.etype = export (sys_map _ _ _ _ (z s0) (fun (_, r) -> r)) in
          z' ()
        ) else raise Contract_failure) <: ML d2.etype))

let static_openfile (msg:string) :
  IOStHist file_descr 
    (requires (fun (s0:events_trace) -> 
      default_check s0 (| Openfile, msg |)))
    (ensures (fun _ _ _ -> True))  =
  IOStHist?.reflect (lift_io_iost (IO.Free.io_all Openfile msg))

let static_read (fd:file_descr) :
  IOStHist string 
    (requires (fun (s0:events_trace) -> 
      default_check s0 (| Read, fd |)))
    (ensures (fun _ res local_events -> True))  =
  IOStHist?.reflect (lift_io_iost (IO.Free.io_all Read fd))
  
let static_close (fd:file_descr) :
  IOStHist unit 
    (requires (fun (s0:events_trace) -> 
      default_check s0 (| Close, fd |)))
    (ensures (fun _ res local_events -> True))  =
  IOStHist?.reflect (lift_io_iost (IO.Free.io_all Close fd))


val dynamic_openfile : string -> ML file_descr
let dynamic_openfile = export static_openfile

val dynamic_read : file_descr -> ML string 
let dynamic_read = export static_read

val dynamic_close : file_descr -> ML unit 
let dynamic_close = export static_close

let testStat1 () : ML unit =
  let fd = dynamic_openfile "../Makefile" in
  let msg = dynamic_read fd in
  dynamic_close fd;
  ()

(* Dependent pairs are neither importable not exportable?
   For the exportable part things are quite funny.
   It seems We can't implement this in F*: *)
(* instance exportable_dpair t1 t2 [| d1:exportable t1 |] (d2:(x:t1 -> exportable (t2 x))) : exportable (x:t1 & t2 x) = *)
(*   mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y)) *)
// - intuitively I still think it should be public/exportable
//   + the problem seems technical, not being able to internalize F* erasure
//   + which might be justification for building exportable/importable on top of
//     public/tainted (which doesn't require to internalize extraction)
//     instead of ml (which does)

(* TODO: This seems related to Eric's early work on Coq-ML interop
         https://arxiv.org/abs/1506.04205
         http://www.mlworkshop.org/lost-in-extraction-recovered.pdf
         https://github.com/tabareau/Cocasse
   - interesting idea on type dependencies: "To recover type dependencies, we
     propose to exploit type isomorphisms between dependently-typed structures
     and plain structures with subset types, and then exploit the cast framework
     presented in the previous section to safely eliminate the subset types."
   - they don't properly deal with ML effects (ignored) and cast failures
     (unsound axiom), but we can do much better here *)

(* TODO: Is this related in any way to the F*-ML interop of Zoe / native tactics?
   - similar instances for arrows and pairs
     https://arxiv.org/pdf/1803.06547.pdf#page=42 *)

(* TODO: What would be a good soundness criterion for all this?
         And can it be internalized within F*? Maybe for importable/exportable?
  - Do Michael Sammler et al prove any generic property?
      No, they couldn't find any, especially for (affine) sealing!
  - Can we take inspiration from the dynamic contracts / gradual typing world?
  - Is etype always a supertype? Is itype always a subtype?
  - Roundtripping of imports and exports (as long as we don't do affine sealing)
  - Secure compilation to ML (need to formalize extraction, see MetaCoq work)
 *)

(* Next steps:
   - deal with pre-post conditions / WPs for effects (refined computation types)
   - stateful coercions (dynamic sealing)
   - connect this with our IO work
     + export and import instances for IO functions with pre/post conditions
     + Michael: the untrusted part is really just C (the context in our
       diagram), and the interaction with anything happen via wrappers
     + Michael: if one tracks capabilities like file handlers one is able
       to reduce the amount of global state.
*)
