module QTypes

open LambdaIO
open IOStar

(** We define quotation for Type **)

(** We need quotation for types to define the logical relation. **)
// Refinements on every node, some kind of normal form
[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type type_quotation : Type0 -> Type u#1 =
| QUnit : #ref:(unit -> Type0) -> type_quotation (x:unit{ref x})
| QBool : #ref:(bool -> Type0) -> type_quotation (x:bool{ref x})
| QNat  : type_quotation nat
| QFileDescriptor : #ref:(file_descr -> Type0) -> type_quotation (x:file_descr{ref x})
| QString : #ref:(string -> Type0) -> type_quotation (x:string{ref x})
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
          #ref:(t1 & t2 -> Type0) ->
          type_quotation (x:(t1 & t2){ref x})
| QSum  : #t1:Type ->
          #t2:Type ->
          type_quotation t1 ->
          type_quotation t2 ->
          #ref:(either t1 t2 -> Type0) ->
          type_quotation (x:(either t1 t2){ref x})

let test_match t (tq:type_quotation t) = (** why does this work so well? **)
  match tq with
  | QUnit #ref -> assert (t == x:unit{ref x})
  | QBool #ref -> assert (t == x:bool{ref x})
  | QFileDescriptor #ref -> assert (t == x:file_descr{ref x})
  | QString #ref -> assert (t == x:string{ref x})
  | QArr #t1 #t2 _ _ -> assert (t == (t1 -> t2))
  | QArrIO #t1 #t2 _ _ -> assert (t == (t1 -> io t2))
  | QPair #t1 #t2 _ _ #ref -> assert (t == (x:(t1 & t2){ref x}))
  | QSum #t1 #t2 _ _ #ref -> assert (t == (x:(either t1 t2){ref x}))
  | QUnit -> assert (t == unit)
  | QBool -> assert (t == bool)
  | QFileDescriptor -> assert (t == file_descr)
  | QString -> assert (t == string)
  | QArr #t1 #t2 _ _ -> assert (t == (t1 -> t2))
  | QArrIO #t1 #t2 _ _ -> assert (t == (t1 -> io t2))
  | QPair #t1 #t2 _ _ -> assert (t == (t1 & t2))
  | QSum #t1 #t2 _ _ -> assert (t == either t1 t2)
  | QNat -> assert (t == nat)

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
  | QNat -> TNat

(** Type of Quotable Types **)
type qType =
  t:Type & type_quotation t

let pack (q:type_quotation 's) : qType = (| _, q |)

let get_Type (t:qType) = Mkdtuple2?._1 t
let get_rel (t:qType) = Mkdtuple2?._2 t
let lem_pack_get_rel t : Lemma (pack (get_rel t) == t) = ()
let rec io_map (#a #b:Type) (f:a -> b) (m:io a) : io b = // need this for forgetting refinement under io
  match m with
  | Return x -> Return (f x)
  | Call o args k -> Call o args (fun r -> io_map f (k r))
let forget_ref #t1 #t2 #post (x:t1) (y:t2{post x y}) : t2 = y

(** When the function applied by [io_map] is the identity on its argument,
    [io_map] does not change the [theta] of the computation. This is needed
    for forgetting trivial refinements on IO results. **)
let rec theta_io_map_id (#a:Type) (f:a -> a) (m:io a)
  : Lemma
      (requires (forall (x:a). f x == x))
      (ensures (theta (io_map f m) `hist_equiv` theta m))
      (decreases m) =
  match m with
  | Return x -> ()
  | Call o args k ->
    introduce forall r. theta (io_map f (k r)) `hist_equiv` theta (k r) with begin
      theta_io_map_id f (k r)
    end;
    lem_hist_bind_equiv (hist_call o args) (hist_call o args)
      (fun r -> theta (io_map f (k r))) (fun r -> theta (k r));
    assert (theta (io_map f (Call o args k)) ==
            hist_bind (hist_call o args) (fun r -> theta (io_map f (k r))))
      by (FStar.Tactics.compute ());
    assert (theta (Call o args k) ==
            hist_bind (hist_call o args) (fun r -> theta (k r)))
      by (FStar.Tactics.compute ())

let thetaP_io_map_id (#a:Type) (f:a -> a) (m:io a) (h:history) (lt:local_trace h) (r:a)
  : Lemma
      (requires (forall (x:a). f x == x))
      (ensures (thetaP (io_map f m) h lt r <==> thetaP m h lt r)) =
  theta_io_map_id f m

// let subQtype_of (a b:qType) : Type0 =
//   get_Type a `subtype_of` get_Type b

let qUnitR ref : qType = (| _, QUnit #ref |)
let qBoolR ref : qType = (| _, QBool #ref |)
let qFileDescrR ref : qType = (| _, QFileDescriptor #ref |)
let qStringR ref : qType = (| _, QString #ref |)
let qSumR t1 t2 ref : qType = (| _, QSum (get_rel t1) (get_rel t2) #ref |)
let qPairR t1 t2 ref : qType = (| _, QPair (get_rel t1) (get_rel t2) #ref |)

//let qArrR (t1 t2:qType) post : qType = (| _, QArr (get_rel t1) (get_rel t2) #post |)
//let qArrIOR (t1 t2:qType) post : qType = (| _, QArrIO (get_rel t1) (get_rel t2) #post |)

let qUnit : qType = qUnitR (fun _ -> True)
let qBool : qType = qBoolR (fun _ -> True)
let qFileDescr : qType = qFileDescrR (fun _ -> True)
let qString : qType = qStringR (fun _ -> True)

// let qRef (t:qType) (ref: get_Type t -> Type0) : qType =
//   (| _, QRefinement (get_rel t) ref |)
let (^->) (t1 t2:qType) : qType =
  (| _, QArr (get_rel t1) (get_rel t2) |)
let (^->!@) (t1 t2:qType) : qType =
  (| _, QArrIO (get_rel t1) (get_rel t2) |)
let (^*) (t1 t2:qType) : qType =
  (| _, QPair (get_rel t1) (get_rel t2) #(fun _ -> True) |)
let (^+) (t1 t2:qType) : qType =
  (| _, QSum (get_rel t1) (get_rel t2) #(fun _ -> True) |)

let qNat : qType = (| _, QNat |)

let qResexn (t1:qType) : qType = t1 ^+ qUnit

unfold
let ref_type' #t (qt:type_quotation t) : Type0 =
  match qt with
  | QUnit -> unit
  | QBool -> bool
  | QFileDescriptor -> file_descr
  | QNat -> nat
  | QString -> string
  | QSum #t1 #t2 qt1 qt2 -> either t1 t2
  | QPair #t1 #t2 qt1 qt2 -> t1 & t2
  | QArr #t1 #t2 qt1 qt2 -> (t1 -> t2)
  | QArrIO #t1 #t2 qt1 qt2 -> (t1 -> io t2)

unfold
let ref_type (t:qType) : Type0 =
  ref_type' (get_rel t)

let ref_of (a:qType) : ref_type a -> Type0 =
  match get_rel a with
  | QUnit #ref -> ref
  | QBool #ref -> ref
  | QFileDescriptor #ref -> ref
  | QString #ref -> ref
  | QPair _ _ #ref -> ref
  | QSum _ _ #ref -> ref
  | QNat -> (fun _ -> True)
  | QArr _ _ -> (fun _ -> True)
  | QArrIO _ _ -> (fun _ -> True)

let change_refinement (t:qType) (ref: ref_type t -> Type0) : qType =
  match get_rel t with
  | QUnit -> qUnitR ref
  | QBool -> qBoolR ref
  | QFileDescriptor -> qFileDescrR ref
  | QString -> qStringR ref
  | QSum qt1 qt2 -> qSumR (pack qt1) (pack qt2) ref
  | QPair qt1 qt2 -> qPairR (pack qt1) (pack qt2) ref
  | QNat -> t
  | QArr _ _ -> t
  | QArrIO _ _ -> t

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

let lem_q_io_args (o:io_ops) :
  Lemma (get_Type (q_io_args o) == io_args o) =
  match o with
  | OOpen -> assert (get_Type (q_io_args OOpen) == io_args OOpen) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
  | ORead -> assert (get_Type (q_io_args ORead) == io_args ORead) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
  | OWrite -> assert (get_Type (q_io_args OWrite) == io_args OWrite) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
  | OClose -> assert (get_Type (q_io_args OClose) == io_args OClose) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())

let lem_q_io_res (o:io_ops) :
  Lemma (forall (a:io_args o). get_Type (q_io_res o) == io_res o a) =
  match o with
  | OOpen -> assert (get_Type (q_io_res OOpen) == resexn file_descr) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
  | ORead -> assert (get_Type (q_io_res ORead) == resexn string) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
  | OWrite -> assert (get_Type (q_io_res OWrite) == resexn unit) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
  | OClose -> assert (get_Type (q_io_res OClose) == resexn unit) by (FStar.Tactics.V1.compute (); FStar.Tactics.V1.trefl ())
