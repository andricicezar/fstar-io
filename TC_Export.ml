open Prims

(** this file is needed because of the bug:
    https://github.com/FStarLang/FStar/issues/2241 **)

type 't ml = {
  mldummy: unit }


let (ml_unit : unit ml) = { mldummy = () }
let (ml_bool : Prims.bool ml) = { mldummy = () }
let (ml_int : Prims.int ml) = { mldummy = () }
let (ml_uint8 : FStar_UInt8.t ml) = { mldummy = () }
let (ml_string : Prims.string ml) = { mldummy = () }
let (ml_bytes : FStar_Bytes.bytes ml) = { mldummy = () }
let (ml_open_flag : Types.open_flag ml) = { mldummy = () }
let (ml_socket_bool_option : Types.socket_bool_option ml) = { mldummy = () }
let (ml_file_descr : Types.file_descr ml) = { mldummy = () }
let (ml_zfile_perm : Common.zfile_perm ml) = { mldummy = () }
let ml_pair : 't1 't2 . 't1 ml -> 't2 ml -> ('t1 * 't2) ml =
  fun uu___ -> fun uu___1 -> { mldummy = () }
let ml_pair_2 :
  't1 't2 't3 . 't1 ml -> 't2 ml -> 't3 ml -> ('t1 * 't2 * 't3) ml =
  fun uu___ -> fun uu___1 -> fun uu___2 -> { mldummy = () }
let ml_pair_3 :
  't1 't2 't3 't4 .
    't1 ml -> 't2 ml -> 't3 ml -> 't4 ml -> ('t1 * 't2 * 't3 * 't4) ml
  = fun uu___ -> fun uu___1 -> fun uu___2 -> fun uu___3 -> { mldummy = () }
let ml_option : 't1 . 't1 ml -> 't1 FStar_Pervasives_Native.option ml =
  fun uu___ -> { mldummy = () }
let ml_maybe : 't1 . 't1 ml -> 't1 Common.maybe ml =
  fun uu___ -> { mldummy = () }
let ml_list : 't1 . 't1 ml -> 't1 Prims.list ml =
  fun uu___ -> { mldummy = () }
type 't exportable = {
  etype: unit ;
  export: 't -> Obj.t ;
  ml_etype: Obj.t ml }
let __proj__Mkexportable__item__export : 't . 't exportable -> 't -> Obj.t =
  fun projectee ->
    match projectee with | { etype; export; ml_etype;_} -> export
let __proj__Mkexportable__item__ml_etype : 't . 't exportable -> unit ml =
  fun uu___ ->
    (fun projectee ->
       match projectee with
       | { etype; export; ml_etype;_} -> Obj.magic ml_etype) uu___
type ('t, 'd) etype = Obj.t
let export : 't . 't exportable -> 't -> Obj.t =
  fun d -> __proj__Mkexportable__item__export d
let ml_etype : 't . 't exportable -> unit ml =
  fun d -> __proj__Mkexportable__item__ml_etype d
type 't importable =
  {
  itype: unit ;
  import: Obj.t -> 't FStar_Pervasives_Native.option ;
  ml_itype: Obj.t ml }
let __proj__Mkimportable__item__import :
  't . 't importable -> Obj.t -> 't FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with | { itype; import; ml_itype;_} -> import
let __proj__Mkimportable__item__ml_itype : 't . 't importable -> unit ml =
  fun uu___ ->
    (fun projectee ->
       match projectee with
       | { itype; import; ml_itype;_} -> Obj.magic ml_itype) uu___
type ('t, 'd) itype = Obj.t
let import : 't . 't importable -> Obj.t -> 't FStar_Pervasives_Native.option
  = fun d -> __proj__Mkimportable__item__import d
let ml_itype : 't . 't importable -> unit ml =
  fun d -> __proj__Mkimportable__item__ml_itype d
type 't safe_importable =
  {
  sitype: unit ;
  safe_import: Obj.t -> 't ;
  ml_sitype: Obj.t ml }
let __proj__Mksafe_importable__item__safe_import :
  't . 't safe_importable -> Obj.t -> 't =
  fun projectee ->
    match projectee with | { sitype; safe_import; ml_sitype;_} -> safe_import
let __proj__Mksafe_importable__item__ml_sitype :
  't . 't safe_importable -> unit ml =
  fun uu___ ->
    (fun projectee ->
       match projectee with
       | { sitype; safe_import; ml_sitype;_} -> Obj.magic ml_sitype) uu___
type ('t, 'd) sitype = Obj.t
let safe_import : 't . 't safe_importable -> Obj.t -> 't =
  fun d -> __proj__Mksafe_importable__item__safe_import d
let ml_sitype : 't . 't safe_importable -> unit ml =
  fun d -> __proj__Mksafe_importable__item__ml_sitype d
let mk_exportable : 't1 't2 . 't2 ml -> ('t1 -> 't2) -> 't1 exportable =
  fun uu___ ->
    fun exp ->
      {
        etype = ();
        export = (fun uu___1 -> (Obj.magic exp) uu___1);
        ml_etype = (Obj.magic uu___)
      }
let mk_importable :
  't1 't2 .
    't1 ml -> ('t1 -> 't2 FStar_Pervasives_Native.option) -> 't2 importable
  =
  fun uu___ ->
    fun imp ->
      {
        itype = ();
        import = (fun uu___1 -> (Obj.magic imp) uu___1);
        ml_itype = (Obj.magic uu___)
      }
let mk_safe_importable :
  't1 't2 . 't1 ml -> ('t1 -> 't2) -> 't2 safe_importable =
  fun uu___ ->
    fun imp ->
      {
        sitype = ();
        safe_import = (fun uu___1 -> (Obj.magic imp) uu___1);
        ml_sitype = (Obj.magic uu___)
      }
let ml_exportable : 't . 't exportable -> unit ml = fun d -> Obj.magic d.ml_etype
let ml_importable : 't . 't importable -> unit ml = fun d -> Obj.magic d.ml_itype
let exportable_ml : 't . 't ml -> 't exportable =
  fun uu___ -> mk_exportable uu___ (fun x -> x)
let safe_importable_ml : 't . 't ml -> 't safe_importable =
  fun uu___ -> mk_safe_importable uu___ (fun x -> x)
let importable_safe_importable : 't . 't safe_importable -> 't importable =
  fun d ->
    mk_importable (Obj.magic d.ml_sitype)
      (fun x -> FStar_Pervasives_Native.Some (safe_import d x))
let safe_importable_exportable : 't . 't exportable -> unit safe_importable =
  fun uu___ ->
    (fun d ->
       Obj.magic
         (mk_safe_importable (Obj.magic (ml_exportable d))
            (fun uu___ -> (fun x -> Obj.magic x) uu___))) uu___
let exportable_refinement : 't . 't exportable -> unit -> 't exportable =
  fun d -> fun p -> mk_exportable (Obj.magic (ml_exportable d)) (export d)
let importable_refinement :
  't .
    't importable ->
      unit -> ('t, Obj.t) TC_Checkable.checkable -> 't importable
  =
  fun d ->
    fun rp ->
      fun uu___ ->
        mk_importable (Obj.magic (ml_importable d))
          (fun x ->
             match import d x with
             | FStar_Pervasives_Native.Some x1 ->
                 if TC_Checkable.check () uu___ x1
                 then FStar_Pervasives_Native.Some x1
                 else FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let exportable_pair :
  't1 't2 . 't1 exportable -> 't2 exportable -> ('t1 * 't2) exportable =
  fun d1 ->
    fun d2 ->
      mk_exportable
        (Obj.magic
           (ml_pair (Obj.magic (ml_exportable d1))
              (Obj.magic (ml_exportable d2))))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (x, y) -> Obj.magic ((export d1 x), (export d2 y))) uu___)
let importable_pair :
  't1 't2 . 't1 importable -> 't2 importable -> ('t1 * 't2) importable =
  fun d1 ->
    fun d2 ->
      mk_importable
        (Obj.magic
           (ml_pair (Obj.magic (ml_importable d1))
              (Obj.magic (ml_importable d2))))
        (fun uu___ ->
           match Obj.magic uu___ with
           | (x, y) ->
               (match ((import d1 x), (import d2 y)) with
                | (FStar_Pervasives_Native.Some x1,
                   FStar_Pervasives_Native.Some y1) ->
                    FStar_Pervasives_Native.Some (x1, y1)
                | uu___1 -> FStar_Pervasives_Native.None))
let importable_dpair_refined :
  't1 't2 'p .
    't1 importable ->
      't2 importable ->
        ('t1, 't2, 'p) TC_Checkable.checkable2 ->
          ('t1, 't2) Prims.dtuple2 importable
  =
  fun d1 ->
    fun d2 ->
      fun d3 ->
        mk_importable
          (Obj.magic
             (ml_pair (Obj.magic (ml_importable d1))
                (Obj.magic (ml_importable d2))))
          (fun uu___ ->
             match Obj.magic uu___ with
             | (x', y') ->
                 (match ((import d1 x'), (import d2 y')) with
                  | (FStar_Pervasives_Native.Some x,
                     FStar_Pervasives_Native.Some y) ->
                      if
                        TC_Checkable.check2 () () (Obj.magic d3) x
                          (Obj.magic y)
                      then
                        FStar_Pervasives_Native.Some (Prims.Mkdtuple2 (x, y))
                      else FStar_Pervasives_Native.None
                  | uu___1 -> FStar_Pervasives_Native.None))
let exportable_option :
  't1 . 't1 exportable -> 't1 FStar_Pervasives_Native.option exportable =
  fun d1 ->
    mk_exportable (Obj.magic (ml_option (Obj.magic (ml_exportable d1))))
      (fun uu___ ->
         (fun x ->
            match x with
            | FStar_Pervasives_Native.Some x' ->
                Obj.magic (FStar_Pervasives_Native.Some (export d1 x'))
            | FStar_Pervasives_Native.None ->
                Obj.magic FStar_Pervasives_Native.None) uu___)
