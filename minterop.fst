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
instance ml_pair t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 * t2) = { mldummy = () }
instance ml_mlarrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> M4 t2) = { mldummy = () }

instance ml_file_descr : ml file_descr = { mldummy = () }
instance ml_check_type : ml check_type = { mldummy = () }



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

let mk_exportable (#t1 t2 : Type) {|ml t2|} (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }
let mk_importable (t1 #t2 : Type) {|ml t1|} (imp : t1 -> M4 t2) : importable t2 =
  { itype = t1; import = imp;  ml_itype = solve }

instance ml_exportable (#t : Type) (d : exportable t) : ml (d.etype) = d.ml_etype
instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) = d.ml_itype

instance exportable_ml t {| ml t|} : exportable t = mk_exportable t (fun x -> x)
instance importable_ml t {| ml t|} : importable t = mk_importable t (fun x -> x)

instance exportable_refinement t {| d:exportable t |} (p : t -> Type0)  : exportable (x:t{p x})
= mk_exportable (d.etype) export // TODO: Eta expanding causes type error

class checkable (#t:Type) (p : t -> Type0) = { check : (x:t -> b:bool{b ==> p x}) }
instance general_is_checkeable t (p : t -> bool) : checkable (fun x -> p x) = { check = fun x -> p x }
class checkable2 (#t1 #t2:Type) (p : t1 -> t2 -> Type0) = { check2 : (x1:t1 -> x2:t2 -> b:bool{b ==> p x1 x2}) }
instance general_is_checkeable2 t1 t2 (p : t1 -> t2 -> bool) : checkable2 (fun x y -> p x y) = { check2 = fun x y -> p x y}
  
class checkable4 (#t1 #t2:Type) (p : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0) = { check4 : (x1:t1 -> s0:events_trace -> r:maybe (events_trace * t2) -> le:events_trace -> b:bool{b ==> p x1 s0 r le}) }
instance general_is_checkeable4 t1 t2 (p : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> bool) : checkable4 (fun x1 x2 x3 x4 -> p x1 x2 x3 x4) = { check4 = fun x1 x2 x3 x4 -> p x1 x2 x3 x4}

instance importable_refinement 
  t {| d:importable t |} 
  (rp : t -> Type0) {| checkable rp |} : 
    importable (x:t{rp x}) = 
  mk_importable (d.itype)
    (fun (x:d.itype) ->
      let x : t = import x in
      (if check #t #rp x then x
       else M4.raise Contract_failure) <: M4 (x:t{rp x}))

let test_refinement () : M4 (y:int{y = 5}) = import 5

(* TODO: quite a few type annotations needed above *)

instance exportable_pair t1 t2 {| d1:exportable t1 |} {| d2:exportable t2 |} : exportable (t1 * t2) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

instance importable_pair t1 t2 {| d1:importable t1 |} {| d2:importable t2 |} : importable (t1 * t2) =
  mk_importable (d1.itype * d2.itype) (fun (x,y) -> (import x, import y) <: M4 (t1 * t2))

instance importable_dpair_refined t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 |} {| d2:importable t2 |} {| d3:checkable2 p |} : importable (x:t1 & y:t2{p x y}) =
  mk_importable (d1.itype & d2.itype) #(x:t1 & y:t2{p x y})
    (fun ((x', y')) ->
        let (x : t1) = import x' in
        let (y : t2) = import y' in
        (if check2 #t1 #t2 #p x y then (| x, y |) 
        else M4.raise Contract_failure) <: (x:t1 & y:t2{p x y}))

let test_dpair_refined () : M4 (a:int & b:int{b = a + 1}) = import (10, 11)

// A typed term in an untyped context
instance exportable_arrow t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} : exportable (t1 -> Tot t2)  =
  mk_exportable (d1.itype -> M4 d2.etype)
    (fun (f:(t1 -> t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: M4 d2.etype))
  
// instance exportable_exarrow t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} : exportable (t1 -> Ex t2)  =
//   mk_exportable (d1.itype -> M4 d2.etype)
//     (fun (f:(t1 -> Ex t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: M4 d2.etype))

instance exportable_mlarrow t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} : exportable (t1 -> M4 t2)  =
  mk_exportable (d1.itype -> M4 d2.etype)
    (fun (f:(t1 -> M4 t2)) -> (fun (x:d1.itype) -> export (f (import x)) <: M4 d2.etype))

// An untyped term in a typed context
instance importable_mlarrow t1 t2 {| d1:exportable t1 |} {| d2:importable t2 |} : importable (t1 -> M4 t2)  =
  mk_importable (d1.etype -> M4 d2.itype)
    (fun (f:(d1.etype -> M4 d2.itype)) -> (fun (x:t1) -> import (f (export x)) <: M4 t2))
  
// Example trueish
let trueish (x:int{x >= 0}) : bool = true
let trueish' (x:int) : M4 bool = (trueish (import x))
let trueish'' : int -> M4 bool = export trueish

instance importable_darrow_refined t1 t2 (p:t1->t2->Type0)
  {| d1:ml t1 |} {| d2:ml t2 |} {| d3:checkable2 p |} : importable (x:t1 -> M4 (y:t2{p x y})) =
  mk_importable (t1 -> M4 t2) #(x:t1 -> M4 (y:t2{p x y}))
    (fun (f:(t1 -> M4 t2)) -> 
      (fun (x:t1) -> 
        let y : t2 = f x in
        (if check2 #t1 #t2 #p x y then y 
         else M4.raise Contract_failure) <: M4 (y:t2{p x y})))

// Example incr

let incr (x:int) : int = x + 1

let incr2 : int -> M4 int = incr

let p x y : bool = (y = x + 1)
let incr'' (x:int) : M4 (y:int{p x y}) = import (incr x)

// val incr' : unit -> M4 ((x:int) -> M4 (y:int{p x y}))
// let incr' () = 
//   let (z:(x:int) -> M4 (y:int{p x y})) = import incr2 in
//   z

instance exportable_purearrow_spec t1 t2 (pre : t1 -> Type0) (post : t1 -> t2 -> Type0)
  {| d1:importable t1 |} {| d2:exportable t2 |} {| d3:checkable pre |} : exportable ((x:t1) -> Pure t2 (pre x) (post x)) = 
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

let _export_IOStHist_arrow_spec #t1 #t2 
  {| d1:ml t1 |} {| d2:exportable t2 |}
  (pre : t1 -> events_trace -> Type0)
  {| checkable2 pre |}
  (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  (f:(x:t1 -> IOStHist t2 (pre x) (post x))) : 
  Tot (t1 -> M4 d2.etype) =
    (fun (x:t1) ->
        if (check2 #t1 #events_trace #pre x []) then (
            let tree = reify (f x) (fun r le -> post x [] r le) in
            export (M4wp?.reflect (fun _ -> iost_to_io (tree [])) <: M4wp t2 (fun p -> forall res. p res))
        ) else M4.raise Contract_failure)

instance exportable_IOStHist_arrow_spec t1 t2 (pre : t1 -> events_trace -> Type0) (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
  {| d1:importable t1 |} {| d2:exportable t2 |} {| d4:checkable2 pre |} : exportable ((x:t1) -> IOStHist t2 (pre x) (post x)) = 
  mk_exportable (d1.itype -> M4 d2.etype)
    (fun (f:(x:t1 -> IOStHist t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        let x : t1 = import x in
        let s0 : events_trace = M4.get_history () in
        (if check2 #t1 #events_trace #pre x s0 then (
          let tree = reify (f x) (fun r le -> post x s0 r le) in
          let m4repr : M4.irepr t2 (fun p -> forall res. p res) = fun _ -> iost_to_io (tree s0) in 
          export (M4?.reflect (m4repr))
        ) else M4.raise Contract_failure) <: M4 d2.etype))

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
    IOStHist t2 (fun _ -> True) (fun s0 result le ->
    match result with
    | Inl v -> 
        let (s1, _) = v in s1 == (apply_changes s0 le)
    | Inr err -> True) by (explode ())= begin
  match tree with
  | Return r -> r
  | Throw r -> IOStHist.throw r
  | Cont (Call cmd argz fnc) ->
      let s0 = IOStHist.get () in
      if default_check s0 (| cmd, argz |) then (
        let rez = IOStHist.static_cmd cmd argz in 
        FStar.WellFounded.axiom1 fnc (Inl rez);
        let z' : sys io_cmds io_cmd_sig t2 = fnc (Inl rez) in
        rev_append_rev_append ();
        _import_M4_to_IOStHist z'
      ) else IOStHist.throw Contract_failure
end

      

let rec _import_M4_to_GIO #t2 (tree : io (t2)) (pi:check_type) : GIO t2 pi = begin
  match tree with
  | Return r -> r 
  | Throw r -> IOStHist.throw r
  | Cont (Call cmd argz fnc) ->
      let rez : res cmd = IOStHist.dynamic_cmd cmd pi argz in
      FStar.WellFounded.axiom1 fnc (Inl rez);
      let z' : sys io_cmds io_cmd_sig t2 = fnc (Inl rez) in
      rev_append_rev_append ();
      _import_M4_to_GIO z' pi
end

instance importable_M4_arrow_spec t1 t2 {| d1:exportable t1 |} {| d2:ml t2 |} :
  importable(pi:check_type -> t1 -> GIO t2 pi) =
  mk_importable (d1.etype -> M4 t2) #(pi:check_type -> t1 -> GIO t2 pi)
    (fun (f:(d1.etype -> M4 t2)) ->
      (fun (pi:check_type) (x:t1) ->
        let x : d1.etype = export x in
        let tree = reify (f x) (fun r -> True) in
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

let m4_cmd (cmd:io_cmds) (argz: args cmd) : M4 (res cmd) = 
  M4?.reflect (fun p -> io_all cmd argz)

let plugin1 : file_descr -> M4 unit = fun fd ->
  m4_cmd Close fd

// val plugin1_g : (pi:check_type) -> file_descr -> GIO unit pi 
// let plugin1_g = import plugin1

// let sdx () : GIO unit pi = 
//   webserver (plugin1_g)

// let plugin2 : file_descr -> M4 unit = fun fd ->
//   let fd = m4_cmd Openfile "../Makefile" in
//   m4_cmd Close fd;
//   let msg = m4_cmd Read fd in ()


// val plugin2_g : (pi:check_type) -> file_descr -> GIO unit pi 
// let plugin2_g = import plugin2
  
// let sdz () : GIO unit pi = 
//   webserver (plugin2_g)

// TODO : try to import from M4 to IOStHist and dynamically enforce the
// post condition

// this can not have a precondition because you can not dynamically
// check it and still return in IOStHist pre if it fails. also it does
// not make sense to have a precondition for a computation

// the post has to accept as a result any errors, espicially 
// Contract_failure

// let extract_local_events (s0 s1:events_trace) :
//   Pure events_trace
//     (requires (exists le. s1 == apply_changes s0 le))
//     (ensures (fun le -> s1 == apply_changes s0 le)) = 
//   admit ();
//   assert (List.length s1 >= List.length s0);
//   let n : nat = (List.length s1) - (List.length s0) in
//   let (le, _) = List.Tot.Base.splitAt n s1 in
//   List.rev le

// instance importable_M4_to_IOStHist t1 t2 (post : t1 -> events_trace -> maybe (events_trace * t2) -> events_trace -> Type0)
//   {| d1:exportable t1 |} {| d2:ml t2 |} {| checkable4 post |}:
//   importable(x:t1 -> IOStHistwp t2 (fun s0 p -> forall res le. post x s0 res le ==>  p res le)) =
//   mk_importable (d1.etype -> M4 t2) #(x:t1 -> IOStHistwp t2 (fun s0 p -> forall restl le. post x s0 restl le ==>  p restl le)) 
//     (fun (f:(d1.etype -> M4 t2)) ->
//       (fun (x:t1) ->
//         let s0 : events_trace = IOStHist.get () in
//         rev_append_rev_append ();
//         let x' : d1.etype = export x in
//         assume (forall x err s0 le. post x s0 (Inr err) le == true);
//         let tree = reify (f x') (fun r -> True) in
//         let result = _import_M4_to_IOStHist #t2 tree in
//         let s1 : events_trace = IOStHist.get () in
//         let le = extract_local_events s0 s1 in


//         // the casting is done wrongly because you don't have an extra le...
//         // in a way this is not correct because it uses the materialized le ^ and the ghost le
//         // without realizing that are the same thing.
//         (if check4 #t1 #t2 #post x s0 (Inl (s1, result)) le then (admit (); result)
//         else (IOStHist.throw Contract_failure)) ))
//           //<: IOStHistwp t2 (fun s0 p -> forall resxy le. post x s0 resxy le ==>  p resxy le)))
