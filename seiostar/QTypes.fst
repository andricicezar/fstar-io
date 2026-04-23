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
// | QRefinement : #t:Type ->
//                 type_quotation t ->
//                 ref: (t -> Type0) ->
//                 type_quotation (x:t{ref x})

let test_match t (tq:type_quotation t) = (** why does this work so well? **)
  match tq with
  | QUnit #ref -> assert (t == x:unit{ref x})
  | QBool #ref -> assert (t == x:bool{ref x})
  | QFileDescriptor #ref -> assert (t == x:file_descr{ref x})
  | QString #ref -> assert (t == x:string{ref x})
  | QArr #t1 #t2 _ _ -> assert (t == ((x:t1 -> y:t2)))
  | QArrIO #t1 #t2 _ _ -> assert (t == ((x:t1 -> io (y:t2))))
  | QPair #t1 #t2 _ _ #ref -> assert (t == (x:(t1 & t2){ref x}))
  | QSum #t1 #t2 _ _ #ref -> assert (t == (x:(either t1 t2){ref x}))

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
