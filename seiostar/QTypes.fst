module QTypes

open LambdaIO
open IOStar

(** We define quotation for Type **)

(** We need quotation for types to define the logical relation. **)
noeq
type type_quotation : Type0 -> Type u#1 =
| QUnit : type_quotation unit
| QBool : type_quotation bool
| QFileDescriptor : type_quotation file_descr
| QString : type_quotation string
| QArr : #t1:Type ->
         #t2:Type ->
         type_quotation t1 ->
         type_quotation t2 ->
         type_quotation (t1 -> t2)
| QArrIO : #t1:Type ->
         #t2:Type ->
         type_quotation t1 ->
         type_quotation t2 ->
         type_quotation (t1 -> io t2)
| QPair : #t1:Type ->
          #t2:Type ->
          type_quotation t1 ->
          type_quotation t2 ->
          type_quotation (t1 & t2)
| QSum  : #t1:Type ->
          #t2:Type ->
          type_quotation t1 ->
          type_quotation t2 ->
          type_quotation (either t1 t2)

let test_match t (tq:type_quotation t) = (** why does this work so well? **)
  match tq with
  | QUnit -> assert (t == unit)
  | QBool -> assert (t == bool)
  | QFileDescriptor -> assert (t == file_descr)
  | QString -> assert (t == string)
  | QArr #t1 #t2 _ _ -> assert (t == (t1 -> t2))
  | QArrIO #t1 #t2 _ _ -> assert (t == (t1 -> io t2))
  | QPair #t1 #t2 _ _ -> assert (t == (t1 & t2))
  | QSum #t1 #t2 _ _ -> assert (t == either t1 t2)

let rec type_quotation_to_typ #s (qt:type_quotation s) : typ =
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
  t:Type & type_quotation t

let pack (q:type_quotation 's) : qType = (| _, q |)

let get_Type (t:qType) = Mkdtuple2?._1 t
let get_rel (t:qType) = Mkdtuple2?._2 t
let lem_pack_get_rel t : Lemma (pack (get_rel t) == t) = ()

let qUnit : qType = (| _, QUnit |)
let qBool : qType = (| _, QBool |)
let qFileDescr : qType = (| _, QFileDescriptor |)
let qString : qType = (| _, QString |)
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