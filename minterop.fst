module Minterop

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open IO.Free
open IOHist
open IOStHist
open M4


(** ** `ml` class *)
(* Intuition, this are morally M4 types written in F* syntax *)

class ml (t:Type) = { mldummy : unit }

// Basic M4 types
instance ml_unit : ml unit = { mldummy = () }
instance ml_bool : ml bool = { mldummy = () }
instance ml_int : ml int = { mldummy = () }
instance ml_string : ml string = { mldummy = () }

instance ml_pair t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 * t2) = { mldummy = () }

instance ml_mlarrow t1 t2 [| ml t1 |] [| ml t2 |] : ml (t1 -> M4 t2) = { mldummy = () }

(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
// - the types of values we can safely `import` from malicious M4 code
// - the types of values we can safely `export` to malicious M4 code
// This interoperability model includes extraction as well as
// adding extra checking and wrapping.
// *)

exception Contract_failure

class exportable (t : Type) = { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) = { itype : Type; import : itype -> M4 t; ml_itype : ml itype }

let mk_exportable (#t1 t2 : Type) [|ml t2|] (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }
let mk_importable (t1 #t2 : Type) [|ml t1|] (imp : t1 -> M4 t2) : importable t2 =
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
  
class checkable4 (#t1 #t2:Type) (p : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0) = { check4 : (x1:t1 -> s0:events_trace -> r:maybe (events_trace * t2) -> le:events_trace -> b:bool{b ==> p x1 s0 r le}) }
instance general_is_checkeable4 t1 t2 (p : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> bool) : checkable4 (fun x1 x2 x3 x4 -> p x1 x2 x3 x4) = { check4 = fun x1 x2 x3 x4 -> p x1 x2 x3 x4}

instance importable_refinement t [| d:importable t |] (p : t -> Type0) [| checkable p |] : importable (x:t{p x}) 
= mk_importable (d.itype)
    (fun (x:d.itype) -> let x : t = import x in
       if check #t #p x then x <: M4 (x:t{p x}) else M4.raise Contract_failure)
    (* TODO: quite a few type annotations needed above *)

instance exportable_pair t1 t2 [| d1:exportable t1 |] [| d2:exportable t2 |] : exportable (t1 * t2) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

instance importable_pair t1 t2 [| d1:importable t1 |] [| d2:importable t2 |] : importable (t1 * t2) =
  mk_importable (d1.itype * d2.itype) (fun (x,y) -> (import x, import y) <: M4 (t1 * t2))

instance importable_dpair_refined t1 t2 (p:t1 -> t2 -> Type0)
  [| d1:importable t1 |] [| d2:importable t2 |] [| d3:checkable2 p |] : importable (x:t1 & y:t2{p x y}) =
  mk_importable (d1.itype & d2.itype) #(x:t1 & y:t2{p x y})
    (fun ((x', y')) ->
        let (x : t1) = import x' in
        let (y : t2) = import y' in
        (if check2 #t1 #t2 #p x y then (| x, y |) 
        else M4.raise Contract_failure) <: (x:t1 & y:t2{p x y}))

// A typed term in an untyped context
instance exportable_arrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> Tot t2)  =
  mk_exportable (d1.itype -> M4 d2.etype)
    (fun (f:(t1 -> t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: M4 d2.etype))
  
// instance exportable_exarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> Ex t2)  =
//   mk_exportable (d1.itype -> M4 d2.etype)
//     (fun (f:(t1 -> Ex t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: M4 d2.etype))

instance exportable_mlarrow t1 t2 [| d1:importable t1 |] [| d2:exportable t2 |] : exportable (t1 -> M4 t2)  =
  mk_exportable (d1.itype -> M4 d2.etype)
    (fun (f:(t1 -> M4 t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: M4 d2.etype))

// An untyped term in a typed context
instance importable_mlarrow t1 t2 [| d1:exportable t1 |] [| d2:importable t2 |] : importable (t1 -> M4 t2)  =
  mk_importable (d1.etype -> M4 d2.itype)
    (fun (f:(d1.etype -> M4 d2.itype)) -> (fun (x:t1) -> import (f (export x)) <: M4 t2))
  
// Example trueish
let trueish (x:int{x >= 0}) : bool = true
let trueish' (x:int) : M4 bool = (trueish (import x))
let trueish'' : int -> M4 bool = export trueish

instance importable_darrow_refined t1 t2 (p:t1->t2->Type0)
  [| d1:exportable t1 |] [| d2:importable t2 |] [| d3:checkable2 p |] : importable (x:t1 -> M4 (y:t2{p x y})) =
  mk_importable (d1.etype -> M4 d2.itype) #(x:t1 -> M4 (y:t2{p x y}))
    (fun (f:(d1.etype -> M4 d2.itype)) -> 
      (fun (x:t1) -> 
        let y : t2 = import (f (export x)) in
          (if check2 #t1 #t2 #p x y then y 
           else M4.raise Contract_failure) <: M4 (y:t2{p x y})))

// Example incr

let incr (x:int) : int = x + 1

val incr' : (x:int) -> M4 (y:int{y = x + 1})
let incr' = import incr

let incr'' (x:int) : M4 (y:int{y = x + 1}) = import (incr x)


instance exportable_purearrow_spec t1 t2 (pre : t1 -> Type0) (post : t1 -> t2 -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d3:checkable pre |] : exportable ((x:t1) -> Pure t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> M4 d2.etype)
    (fun (f:(x:t1 -> Pure t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = import x in
        (if check #t1 #pre x then (
          export (f x)
        ) else raise Contract_failure) <: M4 d2.etype))

// Example incrs
let postcond (x:int) (y:int) : Type0 = y = x + 1
let incrs1 : (x:int) -> Pure int (x > 0) (postcond x) = fun x -> x + 1
let incrs1' : int -> M4 int = export incrs1

let incrs2  : (x:int) -> Pure int (x > 0) (fun (y:int) -> y = x + 1) = fun x -> x + 1
let incrs2' : int -> M4 int = export incrs2


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


// prove that behavior of tree is the same as behavior of result.
let rec drop_trace #t2 (tree : io (events_trace * t2)) : Tot (res:(io t2){IOHist.behavior res `IOHist.include_in` IOHist.behavior tree}) =
  match tree with
  | Return (s1, r) -> Return r
  | Throw r -> Throw r
  | Cont (Call cmd argz fnc) ->
     assume (IOHist.behavior (Cont (Call cmd argz (fun res -> 
       WellFounded.axiom1 fnc res;
       drop_trace (fnc res)))) `IOHist.include_in` IOHist.behavior (Cont (Call cmd argz fnc))
        );

     Cont (Call cmd argz (fun res -> 
       WellFounded.axiom1 fnc res;
       drop_trace (fnc res)))

let myexport #t1 #t2 
  (pre : t1 -> events_trace -> Type0)
  [| checkable2 pre |]
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x))) : (res:(t1 -> M4 t2){
    forall x.
     let f' = reify (f x) in
     let res' = reify (res x) in
     
     (behavior (res') `IOHist.include_in` (behavior (f' [])))}) 
   by (explode (); 
   ExtraTactics.bump_nth 10;
   dump "h") =
  (fun x -> 
    let s0 : events_trace = [] in
    (if check2 #t1 #events_trace #pre x s0 then (
        let tree = reify2 t2 (pre x) (post x) (fun () -> f x) in
        let tree' = drop_trace (tree s0) in
        assume (tree == reify (f x));
        assert (behavior tree' `IOHist.include_in` behavior (tree s0));
        assert (tree' == reify (M4?.reflect tree'));
        M4?.reflect (tree')
    ) else M4.raise Contract_failure) <: M4 t2)

instance exportable_IOStHist_arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  [| d1:importable t1 |] [| d2:exportable t2 |] [| d4:checkable2 pre |] : exportable ((x:t1) -> IOStHist t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> M4 d2.etype) (myexport #t1 #t2 pre post)
    // (fun (f:(x:t1 -> IOStHist t2 (pre x) (post x))) ->
    //   (fun (x:d1.itype) ->
    //     let x : t1 = import x in
    //     let s0 : events_trace = M4.get_history () in
    //     (if check2 #t1 #events_trace #pre x s0 then (
    //       let tree = reify2 t2 (pre x) (post x) (fun () -> f x) in
    //       M4?.reflect (drop_trace (tree s0))
    //     ) else M4.raise Contract_failure) <: M4 d2.etype))

instance ml_check_type : ml check_type = { mldummy = () }
instance ml_events_trace : ml events_trace = { mldummy = () }





let openfile (argz : args Openfile) :
  IOStHist (res Openfile)
    (requires (fun s0 -> default_check s0 (| Openfile, argz |)))
    (ensures (fun s0 (result:maybe (events_trace * (res Openfile))) local_trace -> True)) =
  IOStHist?.reflect(lift_io_iost #(res Openfile) (io_openfile argz))

val m4_openfile : args Openfile -> M4 (res Openfile)
let m4_openfile = export openfile
  
let x = reify (openfile "asd") []
let y = reify (m4_openfile "asd")

// let _ = assert (x == y) by (
//   unfold_def(`(y));
//   dump "h")

let openfile10 (argz : string) :
  IOStHist file_descr 
    (requires (fun s0 -> default_check s0 (| Openfile, argz |)))
    (ensures (fun s0 (result:maybe (events_trace * file_descr)) local_trace -> True)) =
  IOStHist?.reflect(lift_io_iost #file_descr (io_openfile argz))

val m4_openfile10 : string -> M4 file_descr 
let m4_openfile10 = export openfile10

let _ = assert (args Openfile == string)
let _ = assert (res Openfile == file_descr)

let x' = reify (openfile10 "asd") []
let y' = reify (m4_openfile10 "asd")

let _ = assert (x' == (lift_io_iost y' [])) by (
  unfold_def(`(y'));
  dump "h")
  

let mylemma () : Lemma (
  let (f' : args Openfile -> M4 (res Openfile)) = export openfile in
  (IOHist.behavior (reify (openfile "asd") []) `IOHist.include_in` (IOHist.behavior (reify (f' "asd"))))) by (
    unfold_def (`export);
    unfold_def (`reify);
    explode (); 
    ExtraTactics.bump_nth 5;
    dump "h"
) = ()


let rev_append_rev_append () : Lemma (
  forall (s0 le1 le2:events_trace). ((List.rev le2) @ (List.rev le1) @ s0) ==
     ((List.rev (le1@le2)) @ s0)) =
  let aux (s0 le1 le2:events_trace) : Lemma (
    ((List.rev le2) @ (List.rev le1) @ s0) ==
       ((List.rev (le1@le2)) @ s0)) = begin
    List.rev_append le1 le2;
    List.append_assoc (List.rev le2) (List.rev le1) s0
  end in Classical.forall_intro_3 aux

let rec _import_M4_to_IOStHist #t2 (tree : io (t2)) : 
    IOStHist (t2) (fun _ -> True) (fun s0 result le ->
    match result with
    | Inl v -> 
        let (s1, _) = v in s1 == (apply_changes s0 le)
    | Inr err -> True) = begin
  match tree with
  | Return r -> r
  | Throw r -> IOStHist.raise r
  | Cont (Call cmd argz fnc) ->
      let s0 = IOStHist.get () in
      if default_check s0 (| cmd, argz |) then (
        let rez = static_cmd cmd argz in 
        FStar.WellFounded.axiom1 fnc (Inl rez);
        let z' : sys io_cmds io_cmd_sig t2 = fnc (Inl rez) in
        rev_append_rev_append ();
        _import_M4_to_IOStHist z'
      ) else IOStHist.raise Contract_failure
end

// this can not have a precondition because you can not dynamically
// check it and still return in IOStHist pre if it fails. also it does
// not make sense to have a precondition for a computation

// the post has to accept as a result any errors, espicially 
// Contract_failure

let extract_local_events (s0 s1:events_trace) :
  Pure events_trace
    (requires (exists le. s1 == apply_changes s0 le))
    (ensures (fun le -> s1 == apply_changes s0 le)) = 
  admit ();
  assert (List.length s1 >= List.length s0);
  let n : nat = (List.length s1) - (List.length s0) in
  let (le, _) = List.Tot.Base.splitAt n s1 in
  List.rev le

// instance importable_M4_to_IOStHist t1 t2 (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
//   [| d1:exportable t1 |] [| d2:ml t2 |] [| checkable4 post |]:
//   importable(x:t1 -> IOStHistwp t2 (fun s0 p -> forall res le. post x s0 res le ==>  p res le)) by (explode (); 
//   ExtraTactics.bump_nth 13;
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   // tadmit ();
//   ExtraTactics.branch_on_match ();
//  explode ();
//   dump "h")=
//   mk_importable (d1.etype -> M4 t2) #(x:t1 -> IOStHistwp t2 (fun s0 p -> forall restl le. post x s0 restl le ==>  p restl le)) 
//     (fun (f:(d1.etype -> M4 t2)) ->
//       (fun (x:t1) ->
//         let s0 : events_trace = IOStHist.get () in
//         rev_append_rev_append ();
//         let x' : d1.etype = export x in
//         assume (forall x err s0 le. post x s0 (Inr err) le == true);
//         let tree = reify (f x') in
//         let result = _import_M4_to_IOStHist #t2 tree in
//         let s1 : events_trace = IOStHist.get () in
//         let le = extract_local_events s0 s1 in


//         // the casting is done wrongly because you don't have an extra le...
//         // in a way this is not correct because it uses the materialized le ^ and the ghost le
//         // without realizing that are the same thing.
//         (if check4 #t1 #t2 #post x s0 (Inl (s1, result)) le then (admit (); result)
//         else (IOStHist.raise Contract_failure)) ))
//           //<: IOStHistwp t2 (fun s0 p -> forall resxy le. post x s0 resxy le ==>  p resxy le)))
      

// why is this failing right now?
let rec _import_M4_to_GIO #t2 (tree : io (t2)) (pi:check_type) : GIO t2 pi = admit (); begin
  match tree with
  | Return r -> r 
  | Throw r -> IOStHist.raise r
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = dynamic_cmd cmd pi argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : sys io_cmds io_cmd_sig t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      _import_M4_to_GIO z' pi
end

instance importable_M4_arrow_spec t1 t2 [| d1:exportable t1 |] [| d2:ml t2 |] :
  importable(pi:check_type -> t1 -> GIO t2 pi) =
  mk_importable (d1.etype -> M4 t2) #(pi:check_type -> t1 -> GIO t2 pi)
    (fun (f:(d1.etype -> M4 t2)) ->
      (fun (pi:check_type) (x:t1) ->
        let x : d1.etype = export x in
        let tree = reify (f x) in
        _import_M4_to_GIO #t2 tree pi <: GIO t2 pi))

val allowed_file : string -> bool
let allowed_file fnm = match fnm with
  | "../Makefile" -> false
  | "Demos.fst" -> true
  | _ -> false

val allowed_fd : file_descr -> events_trace -> bool
let rec allowed_fd fd s0 =
  match s0 with
  | [] -> false
  | EOpenfile fnm (Inl fd') :: t -> if fd = fd' then allowed_file(fnm)
                                  else allowed_fd fd t
  | EClose fd' _  :: t -> if fd = fd' then false else allowed_fd fd t
  | _ :: t -> allowed_fd fd t

let pi : check_type = (fun s0 action -> 
  match action with
  | (| Openfile, fnm |) -> allowed_file(fnm)
  | (| Read, fd |) -> allowed_fd fd s0
  | (| Close, fd |) -> allowed_fd fd s0)

// the plugin will be written in GIO (should be ML?)
let plugin_type = (pi:check_type) -> file_descr -> GIO unit pi

// import plugin_type 
let webserver (plugin:plugin_type) : GIO unit pi =
  rev_append_rev_append ();
  let fd = pi_static_cmd Openfile pi "Demos.fst" in
  plugin pi fd

let m4_cmd (cmd:io_cmds) (argz: args cmd) : M4 (res cmd) = M4?.reflect (io_all cmd argz)

let plugin1 : file_descr -> M4 unit = fun fd ->
  m4_cmd Close fd

val plugin1_g : (pi:check_type) -> file_descr -> GIO unit pi 
let plugin1_g = import plugin1

let sdx () : GIO unit pi = 
  webserver (plugin1_g)

let plugin2 : file_descr -> M4 unit = fun fd ->
  let fd = m4_cmd Openfile "../Makefile" in
  m4_cmd Close fd;
  let msg = m4_cmd Read fd in ()


val plugin2_g : (pi:check_type) -> file_descr -> GIO unit pi 
let plugin2_g = import plugin2


let sdz () : GIO unit pi = 
  webserver (plugin2_g)
