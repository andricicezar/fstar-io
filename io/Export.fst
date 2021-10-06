module Export

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open DM
open Checkable

(**
lift: IO -> IIO (Done - in IIO.Effect.fst)
lift: MIO -> MIIO (the lift from IO to IIO should work automatically)

export: IIO -> MIIO (Done: exportable_IIO)
export: IO -> MIIO (Done: exportable_IO - lift automatically to IIO,
                          and then use export: IIO -> MIIO)

import: MIIO -> IIO (Done: importable_MIIO_IIO)
import: MIO -> IIO (Done: importable_MIO_IIO) lift from MIO to MIIO,
                          and then import to IIO)

Not possible cases:
IIO -> IO
IIO -> MIO (the runtime checks can not be
           enforced statically because GetTrace is missing in IO)

IO -> MIO (the preconditions can not be enforced
           dynamically because GetTrace is missing in IO)

MIO -> IO (we can not enforce preconditions
           statically)

MIIO -> IO
MIIO -> MIO (Not possible because we can not get rid of GetTrace)
**)

(** ** `ml` class *)
(* Intuition, this are morally MIO types written in F* syntax *)

class ml (t:Type) = { mldummy : unit }

// Basic MIO types
instance ml_unit : ml unit = { mldummy = () }
instance ml_bool : ml bool = { mldummy = () }
instance ml_int : ml int = { mldummy = () }
instance ml_string : ml string = { mldummy = () }
instance ml_pair t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 * t2) = { mldummy = () }
instance ml_option t1 {| ml t1 |} : ml (option t1) = { mldummy = () }
instance ml_totarrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> Tot t2) =
  { mldummy = () }
instance ml_purearrow t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 -> Pure t2 True (fun _ -> True)) =
  { mldummy = () }

instance ml_miioarrow (t1:Type u#a) (t2:Type u#b)
  {| ml t1 |} {| ml t2 |} : ml (t1 -> MIIO t2) =
  { mldummy = () }

// instance ml_mlarrow2 t1 t2 t3 {| ml t1 |} {| ml t2 |} {| ml t3 |} : ml (t1 -> t2 -> ML t3) =
//   { mldummy = () }

instance ml_file_descr : ml file_descr = { mldummy = () }
(** CA: Is this required? **)
// instance ml_monitorable_prop : ml monitorable_prop = { mldummy = () }



(** ** `exportable` and `importable` classes *)
(* Intuition, **with** extra checking, wrapping, and type erasure (extraction):
// - the types of values we can safely `import` from malicious MIO code
// - the types of values we can safely `export` to malicious MIO code
// This interoperability model includes extraction as well as
// adding extra checking and wrapping.
// *)

(** TODO:
we have 3 importable classes and I don't think they are named very well.

Context:
One thing we learned is that our import function should not throw
errors because we need to use it in writing specifications, therefore
we want an import function of type t1 -> option t2. In the same time,
it is much easier to write code using exceptions, therefore there is
the exn_import, which is just a lift from option to exceptions.

There is a special case for functions. Functions always can be imported, because
the cast from the strong type to the weak type is done inside the function (?).
Also, ml types can be always imported safely. Therefore, I added
safe_import of type t1 -> t2. I am not that happy with the safe_ part
in the name. To me import and safe_import are both 'safe'.
**)

class exportable (t : Type) =
  { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) =
  { itype : Type; import : itype -> option t; ml_itype : ml itype }

// class exn_importable (t : Type) =
//   { eitype : Type; exn_import : eitype -> ML t; ml_eitype : ml eitype }
class safe_importable (t : Type) =
  { sitype : Type; safe_import : sitype -> t; ml_sitype : ml sitype }

let mk_exportable (#t1 t2 : Type) {| ml t2 |} (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }

let mk_importable
  (t1 #t2 : Type) {| ml t1 |}
  (imp : t1 -> option t2) :
  Tot (importable t2) =
  { itype = t1; import = imp; ml_itype = solve }

// let mk_exn_importable
//   (t1 #t2 : Type) {| ml t1 |}
//   (imp : t1 -> ML t2) :
//   Tot (exn_importable t2) =
//   { eitype = t1; exn_import = imp; ml_eitype = solve }

let mk_safe_importable
  (t1 #t2 : Type) {| ml t1 |}
  (imp : t1 -> t2) :
  Tot (safe_importable t2) =
  { sitype = t1; safe_import = imp; ml_sitype = solve }

(** Are this two needed? **)
instance ml_exportable (#t : Type) (d : exportable t) : ml (d.etype) =
  d.ml_etype
instance ml_importable (#t : Type) (d : importable t) : ml (d.itype) =
  d.ml_itype

instance exportable_ml t {| ml t |} : exportable t =
  mk_exportable t (fun x -> x)
instance safe_importable_ml t {| ml t |} : safe_importable t =
  mk_safe_importable t (fun x -> x)

instance importable_safe_importable t {| d:safe_importable t |} : importable t =
  mk_importable d.sitype #t #d.ml_sitype
    (fun (x:d.sitype) -> (Some (safe_import x)) <: option t)

instance exportable_refinement
  t {| d:exportable t |}
  (p : t -> Type0) :
  Tot (exportable (x:t{p x})) =
  mk_exportable (d.etype) export

instance importable_refinement
  t {| d:importable t |}
  (rp : t -> Type0) {| checkable rp |} :
  Tot (importable (x:t{rp x})) =
  mk_importable (d.itype)
    (fun (x:d.itype) ->
      (match import x with
      | Some x -> if check #t #rp x then Some x else None
      | None -> None) <: option (x:t{rp x}))

instance exportable_pair
  t1 t2 {| d1:exportable t1 |} {| d2:exportable t2 |} :
  Tot (exportable (t1 * t2)) =
  mk_exportable (d1.etype * d2.etype) (fun (x,y) -> (export x, export y))

instance importable_pair
  t1 t2 {| d1:importable t1 |} {| d2:importable t2 |} :
  Tot (importable (t1 * t2)) =
  mk_importable (d1.itype * d2.itype) (fun (x,y) ->
    (match (import x, import y) with
    | (Some x, Some y) -> Some (x, y)
    | _ -> None) <: option (t1 * t2))

instance importable_dpair_refined
  t1 t2 (p:t1 -> t2 -> Type0)
  {| d1:importable t1 |} {| d2:importable t2 |} {| d3:checkable2 p |} :
  Tot (importable (x:t1 & y:t2{p x y})) =
  mk_importable (d1.itype & d2.itype) #(x:t1 & y:t2{p x y})
    (fun ((x', y')) ->
      (match (import x', import y') with
       | (Some x, Some y) ->
               if check2 #t1 #t2 #p x y then Some (| x, y |) else None
       | _ -> None) <: option (x:t1 & y:t2{p x y}))

instance exportable_option
  t1 {| d1:exportable t1 |} :
  Tot (exportable (option t1)) =
  mk_exportable (option d1.etype)
    (fun x -> match x with | Some x' -> Some (export x') | None -> None)

// A typed term in an untyped context
instance exportable_arrow
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |} :
  Tot (exportable (t1 -> Tot t2))  =
  mk_exportable (d1.itype -> Tot (option d2.etype))
    (fun (f:(t1 -> t2)) ->
      (fun (x:d1.itype) ->
        match import x with
        | Some x' -> Some (export (f x')) <: Tot (option d2.etype)
        | None -> None <: Tot (option d2.etype)))

instance exportable_purearrow_spec
  t1 t2 {| d1:importable t1 |} {| d2:exportable t2 |}
  (pre : t1 -> Type0) {| d3:checkable pre |}
  (post : t1 -> t2 -> Type0) :
  Tot (exportable ((x:t1) -> Pure t2 (pre x) (post x))) =
  mk_exportable (d1.itype -> Pure (option d2.etype) True (fun _ -> True))
    (fun (f:(x:t1 -> Pure t2 (pre x) (post x))) ->
      (fun (x:d1.itype) ->
        match import x with
        | Some x' ->
          if check #t1 #pre x' then Some (export (f x'))
          else None
        | None -> None))


instance exportable_IOwp
  (t1:Type) {| d1:importable t1 |}
  (t2:Type) {| d2:exportable t2 |}
  (pre:t1 -> trace -> Type0) {| d3:checkable2 pre |}
  (post:t1 -> trace -> (m:maybe t2) -> trace -> (r:Type0{Inr? m ==> r})) :
  Tot (exportable (x:t1 ->
    IOwp t2 (fun h p ->
      pre x h /\ (forall r lt. post x h r lt ==>  p r lt)))) =
  mk_exportable
    (d1.itype -> MIIO d2.etype)
    (fun (f:(x:t1 -> IOwp t2 (fun h p ->
      pre x h /\ (forall r lt. post x h r lt ==>  p r lt)))) ->
      (fun x ->
        match import x with
        | Some x' -> export (_IIOwp_as_MIIO d3.check2 post f x')
        | None -> DM.IIO.raise Contract_failure))
