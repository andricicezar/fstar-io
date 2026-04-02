module QTypes

open LambdaIO
open IOStar
open FStar.Universe

(** Universe wrapper to accommodate io being in universe max 1 a **)
noeq
type uType : Type u#2 =
| U0 : Type u#0 -> uType
| U1 : Type u#1 -> uType

(** Operations on uType, following the pattern of ^-> from QExp.fsti **)
let uArr (a b:uType) : uType =
  match a, b with
  | U0 a, U0 b -> U0 (a -> b)
  | U0 a, U1 b -> U1 (a -> b)
  | U1 a, U0 b -> U1 (a -> b)
  | U1 a, U1 b -> U1 (a -> b)

let uArrIO (a b:uType) : uType =
  match a, b with
  | U0 a, U0 b -> U1 (a -> io b)
  | U0 a, U1 b -> U1 (a -> io b)
  | U1 a, U0 b -> U1 (a -> io b)
  | U1 a, U1 b -> U1 (a -> io b)

let uPair (a b:uType) : uType =
  match a, b with
  | U0 a, U0 b -> U0 (a & b)
  | U0 a, U1 b -> U1 (a & b)
  | U1 a, U0 b -> U1 (a & b)
  | U1 a, U1 b -> U1 (a & b)

let uSum (a b:uType) : uType =
  match a, b with
  | U0 a, U0 b -> U0 (either a b)
  | U0 a, U1 b -> U1 (either a b)
  | U1 a, U0 b -> U1 (either a b)
  | U1 a, U1 b -> U1 (either a b)

(** We define quotation for Type **)

(** We need quotation for types to define the logical relation. **)
noeq
type type_quotation : uType -> Type u#2 =
| QUnit : type_quotation (U0 unit)
| QBool : type_quotation (U0 bool)
| QFileDescriptor : type_quotation (U0 file_descr)
| QString : type_quotation (U0 string)
| QArr : #u1:uType -> #u2:uType ->
         type_quotation u1 ->
         type_quotation u2 ->
         type_quotation (uArr u1 u2)
| QArrIO : #u1:uType -> #u2:uType ->
         type_quotation u1 ->
         type_quotation u2 ->
         type_quotation (uArrIO u1 u2)
| QPair : #u1:uType -> #u2:uType ->
          type_quotation u1 ->
          type_quotation u2 ->
          type_quotation (uPair u1 u2)
| QSum  : #u1:uType -> #u2:uType ->
          type_quotation u1 ->
          type_quotation u2 ->
          type_quotation (uSum u1 u2)

let test_match (t:uType) (tq:type_quotation t) =
  match tq with
  | QUnit -> assert (t == U0 unit)
  | QBool -> assert (t == U0 bool)
  | QFileDescriptor -> assert (t == U0 file_descr)
  | QString -> assert (t == U0 string)
  | QArr #u1 #u2 _ _ -> assert (t == uArr u1 u2)
  | QArrIO #u1 #u2 _ _ -> assert (t == uArrIO u1 u2)
  | QPair #u1 #u2 _ _ -> assert (t == uPair u1 u2)
  | QSum #u1 #u2 _ _ -> assert (t == uSum u1 u2)

let rec type_quotation_to_typ #s (qt:type_quotation s) : Tot typ (decreases qt) =
  match qt with
  | QUnit -> TUnit
  | QBool -> TBool
  | QFileDescriptor -> TFileDescr
  | QString -> TString
  | QPair qt1 qt2 -> TPair (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)
  | QArr qt1 qt2
  | QArrIO qt1 qt2 ->
    TArr (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)
  | QSum qt1 qt2 -> TSum (type_quotation_to_typ qt1) (type_quotation_to_typ qt2)

(** Type of Quotable Types **)
type qType =
  t:uType & type_quotation t

let pack (q:type_quotation 's) : qType = (| _, q |)

let get_Type (t:qType) = Mkdtuple2?._1 t
let get_rel (t:qType) = Mkdtuple2?._2 t
let lem_pack_get_rel t : Lemma (pack (get_rel t) == t) = ()

let qUnit : qType = (| U0 unit, QUnit |)
let qBool : qType = (| U0 bool, QBool |)
let qFileDescr : qType = (| U0 file_descr, QFileDescriptor |)
let qString : qType = (| U0 string, QString |)
let (^->) (t1 t2:qType) : qType =
  (| _, QArr (get_rel t1) (get_rel t2) |)
let (^->!@) (t1 t2:qType) : qType =
  (| _, QArrIO (get_rel t1) (get_rel t2) |)

let (^*) (t1 t2:qType) : qType =
  (| _, QPair (get_rel t1) (get_rel t2) |)
let (^+) (t1 t2:qType) : qType =
  (| _, QSum (get_rel t1) (get_rel t2) |)

let qResexn (t1:qType) : qType = t1 ^+ qUnit


let q_io_args (o:io_ops) : qType =
  match o with
  | OOpen  -> qString
  | ORead  -> qFileDescr
  | OWrite -> qFileDescr ^* qString
  | OClose -> qFileDescr

let q_io_res (o:io_ops) : qType =
  match o with
  | OOpen  -> qResexn qFileDescr
  | ORead  -> qResexn qString
  | OWrite -> qResexn qUnit
  | OClose -> qResexn qUnit