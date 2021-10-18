module Export

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common
open DM
open Checkable

(** Principles for import/export:
1. they work only with basic types (no functions).
2. We need to be really careful with what we say it is `ml` since
   F* does not check any restrictions.
**)

(** ** `ml` class *)

class ml (t:Type) = { mldummy : unit }

// Basic MIO types
instance ml_unit : ml unit = { mldummy = () }
instance ml_bool : ml bool = { mldummy = () }
instance ml_int : ml int = { mldummy = () }
instance ml_string : ml string = { mldummy = () }
instance ml_pair t1 t2 {| ml t1 |} {| ml t2 |} : ml (t1 * t2) = { mldummy = () }
instance ml_option t1 {| ml t1 |} : ml (option t1) = { mldummy = () }
instance ml_maybe t1 {| ml t1 |} : ml (maybe t1) = { mldummy = () }
instance ml_file_descr : ml file_descr = { mldummy = () }
(** ** Arrows are not ml! **)
(**: Arrows are not ml, because in F* they have an associated effect, concept that does 
not exists in ML. **)


(** *** `exportable` and `importable` classes *)
(** One thing we learned is that our import function should not throw
errors because we need to use it in writing specifications, therefore
we want an import function of type t1 -> option t2.

ml types can be always imported safely. 'safely' must be understood as
there is no checking that can fail. Therefore, I added
safe_import of type t1 -> t2. **)

class exportable (t : Type) =
  { etype : Type; export : t -> etype; ml_etype : ml etype }
class importable (t : Type) =
  { itype : Type; import : itype -> option t; ml_itype : ml itype }

class safe_importable (t : Type) =
  { sitype : Type; safe_import : sitype -> t; ml_sitype : ml sitype }

let mk_exportable (#t1 t2 : Type) {| ml t2 |} (exp : t1 -> t2) : exportable t1 =
  { etype = t2; export = exp;  ml_etype = solve }

let mk_importable
  (t1 #t2 : Type) {| ml t1 |}
  (imp : t1 -> option t2) :
  Tot (importable t2) =
  { itype = t1; import = imp; ml_itype = solve }

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

instance safe_importable_exportable t {| d:exportable t |} : safe_importable d.etype =
  admit ();
  mk_safe_importable d.etype #t (fun x -> x)

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
