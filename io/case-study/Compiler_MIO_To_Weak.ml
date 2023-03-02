open Prims
type 'a tree =
  | Leaf 
  | EmptyNode of 'a tree * 'a tree 
  | Node of 'a * 'a tree * 'a tree 
let uu___is_Leaf : 'a . 'a tree -> Prims.bool =
  fun projectee -> match projectee with | Leaf -> true | uu___ -> false
let uu___is_EmptyNode : 'a . 'a tree -> Prims.bool =
  fun projectee ->
    match projectee with | EmptyNode (left, right) -> true | uu___ -> false
let __proj__EmptyNode__item__left : 'a . 'a tree -> 'a tree =
  fun projectee -> match projectee with | EmptyNode (left, right) -> left
let __proj__EmptyNode__item__right : 'a . 'a tree -> 'a tree =
  fun projectee -> match projectee with | EmptyNode (left, right) -> right
let uu___is_Node : 'a . 'a tree -> Prims.bool =
  fun projectee ->
    match projectee with | Node (data, left, right) -> true | uu___ -> false
let __proj__Node__item__data : 'a . 'a tree -> 'a =
  fun projectee -> match projectee with | Node (data, left, right) -> data
let __proj__Node__item__left : 'a . 'a tree -> 'a tree =
  fun projectee -> match projectee with | Node (data, left, right) -> left
let __proj__Node__item__right : 'a . 'a tree -> 'a tree =
  fun projectee -> match projectee with | Node (data, left, right) -> right
let root : 'a . 'a tree -> 'a = fun t -> __proj__Node__item__data t
let left : 'a . 'a tree -> 'a tree =
  fun t ->
    match t with
    | Node (uu___, lt, uu___1) -> lt
    | EmptyNode (lt, uu___) -> lt
let right : 'a . 'a tree -> 'a tree =
  fun t ->
    match t with
    | Node (uu___, uu___1, rt) -> rt
    | EmptyNode (uu___, rt) -> rt
type ('a, 't1, 't2) equal_trees = Obj.t
let rec map_tree : 'a 'b . 'a tree -> ('a -> 'b) -> 'b tree =
  fun t ->
    fun f ->
      match t with
      | Leaf -> Leaf
      | EmptyNode (lhs, rhs) ->
          EmptyNode ((map_tree lhs f), (map_tree rhs f))
      | Node (x, lhs, rhs) ->
          Node ((f x), (map_tree lhs f), (map_tree rhs f))
let (get_local_trace : MIO_Sig.trace -> MIO_Sig.trace -> MIO_Sig.trace) =
  fun h' ->
    fun h ->
      let n =
        (FStar_List_Tot_Base.length h) - (FStar_List_Tot_Base.length h') in
      let uu___ = FStar_List_Tot_Base.splitAt n h in
      match uu___ with | (lt', ht) -> FStar_List_Tot_Base.rev lt'
type ('argt, 'rett) rc_typ =
  'argt -> MIO_Sig.trace -> 'rett -> MIO_Sig.trace -> Prims.bool
type ('a, 'b, 'rc, 'initialuh, 'x, 'y, 'currentuh, 'b1,
  'lt) eff_rc_typ_cont_post = unit
type ('fl, 't1, 't2, 'rc, 'x, 'initialuh) eff_rc_typ_cont =
  't2 -> (Prims.bool, unit, unit) MIO.dm_gmio
type ('fl, 't1, 't2, 'rc) eff_rc_typ =
  't1 ->
    ((unit, (unit, 't1, 't2, unit, unit, unit) eff_rc_typ_cont) Prims.dtuple2,
      unit, unit) MIO.dm_gmio
let enforce_rc :
  'argt 'rett .
    ('argt, 'rett) rc_typ -> (unit, 'argt, 'rett, unit) eff_rc_typ
  =
  fun uu___ ->
    (fun rc ->
       Obj.magic
         (fun x ->
            MIO.dm_gmio_bind () () () () (Obj.magic (MIO.get_trace true))
              (fun initial_h ->
                 MIO.lift_pure_dm_gmio
                   (fun uu___ ->
                      Prims.Mkdtuple2
                        ((),
                          (Obj.magic
                             (fun y ->
                                MIO.dm_gmio_bind () () () ()
                                  (Obj.magic (MIO.get_trace true))
                                  (fun current_h ->
                                     MIO.lift_pure_dm_gmio
                                       (fun uu___1 ->
                                          rc x initial_h y
                                            (get_local_trace initial_h
                                               current_h)))))))))) uu___
type pck_rc = (unit, unit, (Obj.t, Obj.t) rc_typ) FStar_Pervasives.dtuple3
type 'ctr arg_typ = Obj.t
type 'ctr ret_typ = Obj.t
let (check :
  pck_rc -> Obj.t -> MIO_Sig.trace -> Obj.t -> MIO_Sig.trace -> Prims.bool) =
  fun ctr ->
    fun arg ->
      fun h ->
        fun ret ->
          fun lt ->
            FStar_Pervasives.__proj__Mkdtuple3__item___3 ctr arg h ret lt
type 'fl eff_pck_rc =
  (pck_rc, (unit, unit, unit, unit) eff_rc_typ) Prims.dtuple2
let (make_rc_eff : pck_rc -> unit eff_pck_rc) =
  fun r ->
    Prims.Mkdtuple2
      (r,
        (Obj.magic
           (enforce_rc (FStar_Pervasives.__proj__Mkdtuple3__item___3 r))))
type ('fl, 'rcs) typ_eff_rcs = unit eff_pck_rc tree
let (typ_left :
  unit -> pck_rc tree -> (unit, unit) typ_eff_rcs -> (unit, unit) typ_eff_rcs)
  = fun fl -> fun rcs -> fun t -> left t
let (typ_right :
  unit -> pck_rc tree -> (unit, unit) typ_eff_rcs -> (unit, unit) typ_eff_rcs)
  = fun fl -> fun rcs -> fun t -> right t
let (make_rcs_eff : pck_rc tree -> (unit, unit) typ_eff_rcs) =
  fun rcs ->
    let r = map_tree rcs make_rc_eff in
    let comp x = FStar_Pervasives.dfst (make_rc_eff x) in r
type ('styp, 'pi, 'rcs, 'fl) exportable =
  {
  wtyp: unit ;
  c_wtyp: (Obj.t, unit, 'pi) Compiler_Languages.weak ;
  export: (unit, unit) typ_eff_rcs -> 'styp -> Obj.t }
let __proj__Mkexportable__item__c_wtyp :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) exportable ->
          (unit, unit, 'pi) Compiler_Languages.weak
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun rcs ->
           fun fl ->
             fun projectee ->
               match projectee with
               | { wtyp; c_wtyp; export;_} -> Obj.magic c_wtyp) uu___2 uu___1
          uu___
let __proj__Mkexportable__item__export :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) exportable ->
          (unit, unit) typ_eff_rcs -> 'styp -> Obj.t
  =
  fun rcs ->
    fun fl ->
      fun projectee ->
        match projectee with | { wtyp; c_wtyp; export;_} -> export
type ('styp, 'pi, 'rcs, 'fl) safe_importable =
  {
  swtyp: unit ;
  c_swtyp: (Obj.t, unit, 'pi) Compiler_Languages.weak ;
  safe_import: Obj.t -> (unit, unit) typ_eff_rcs -> 'styp }
let __proj__Mksafe_importable__item__c_swtyp :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) safe_importable ->
          (unit, unit, 'pi) Compiler_Languages.weak
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun rcs ->
           fun fl ->
             fun projectee ->
               match projectee with
               | { swtyp; c_swtyp; safe_import;_} -> Obj.magic c_swtyp)
          uu___2 uu___1 uu___
let __proj__Mksafe_importable__item__safe_import :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) safe_importable ->
          Obj.t -> (unit, unit) typ_eff_rcs -> 'styp
  =
  fun rcs ->
    fun fl ->
      fun projectee ->
        match projectee with
        | { swtyp; c_swtyp; safe_import;_} -> safe_import
type ('styp, 'pi, 'rcs, 'fl) importable =
  {
  wtyp1: unit ;
  c_wtyp1: (Obj.t, unit, 'pi) Compiler_Languages.weak ;
  import: Obj.t -> (unit, unit) typ_eff_rcs -> 'styp CommonUtils.resexn }
let __proj__Mkimportable__item__c_wtyp :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) importable ->
          (unit, unit, 'pi) Compiler_Languages.weak
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun rcs ->
           fun fl ->
             fun projectee ->
               match projectee with
               | { wtyp1 = wtyp; c_wtyp1 = c_wtyp; import;_} ->
                   Obj.magic c_wtyp) uu___2 uu___1 uu___
let __proj__Mkimportable__item__import :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) importable ->
          Obj.t -> (unit, unit) typ_eff_rcs -> 'styp CommonUtils.resexn
  =
  fun rcs ->
    fun fl ->
      fun projectee ->
        match projectee with
        | { wtyp1 = wtyp; c_wtyp1 = c_wtyp; import;_} -> import
let weak_importable_super :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) importable ->
          (unit, unit, 'pi) Compiler_Languages.weak
  = fun rcs -> fun fl -> fun d -> Obj.magic d.c_wtyp1
let weak_exportable_super :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) exportable ->
          (unit, unit, 'pi) Compiler_Languages.weak
  = fun rcs -> fun fl -> fun d -> Obj.magic d.c_wtyp
let weak_safe_importable_super :
  'styp 'pi .
    pck_rc tree ->
      unit ->
        ('styp, 'pi, unit, unit) safe_importable ->
          (unit, unit, 'pi) Compiler_Languages.weak
  = fun rcs -> fun fl -> fun d -> Obj.magic d.c_swtyp
let weak_is_exportable :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, unit, 'pi) Compiler_Languages.weak ->
            (Obj.t, 'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun t ->
        fun d1 ->
          {
            wtyp = ();
            c_wtyp = d1;
            export = (fun uu___ -> fun x -> match uu___ with | Leaf -> x)
          }
let exportable_unit : 'pi . unit -> (unit, 'pi, unit, unit) exportable =
  fun fl ->
    {
      wtyp = ();
      c_wtyp = (Obj.magic (Compiler_Languages.weak_unit () ()));
      export =
        (fun uu___1 ->
           fun uu___ ->
             (fun uu___ -> fun uu___1 -> Obj.magic ()) uu___1 uu___)
    }
let exportable_file_descr :
  'pi . unit -> (UnixTypes.file_descr, 'pi, unit, unit) exportable =
  fun fl ->
    {
      wtyp = ();
      c_wtyp = (Obj.magic (Compiler_Languages.weak_int () ()));
      export =
        (fun uu___1 ->
           fun uu___ ->
             (fun uu___ -> fun fd -> match uu___ with | Leaf -> Obj.magic fd)
               uu___1 uu___)
    }
let exportable_bytes :
  'pi . unit -> (FStar_Bytes.bytes, 'pi, unit, unit) exportable =
  fun fl ->
    {
      wtyp = ();
      c_wtyp = (Obj.magic (Compiler_Languages.weak_bytes () ()));
      export =
        (fun uu___1 ->
           fun uu___ ->
             (fun uu___ -> fun b -> match uu___ with | Leaf -> Obj.magic b)
               uu___1 uu___)
    }
let exportable_refinement :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) exportable ->
            unit -> (Obj.t, 'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun t ->
        fun d ->
          fun p ->
            {
              wtyp = ();
              c_wtyp = (Obj.magic (weak_exportable_super rcs () d));
              export = (d.export)
            }
let exportable_option :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) exportable ->
            (Obj.t FStar_Pervasives_Native.option, 'pi, unit, unit)
              exportable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          {
            wtyp = ();
            c_wtyp =
              (Obj.magic
                 (Compiler_Languages.weak_option () () ()
                    (Obj.magic (weak_exportable_super rcs () d1))));
            export =
              (fun uu___1 ->
                 fun uu___ ->
                   (fun eff_rcs ->
                      fun x ->
                        match x with
                        | FStar_Pervasives_Native.Some x' ->
                            Obj.magic
                              (FStar_Pervasives_Native.Some
                                 (d1.export eff_rcs x'))
                        | FStar_Pervasives_Native.None ->
                            Obj.magic FStar_Pervasives_Native.None) uu___1
                     uu___)
          }
let exportable_pair :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) exportable ->
            unit ->
              (Obj.t, 'pi, unit, unit) exportable ->
                ((Obj.t * Obj.t), 'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          fun t2 ->
            fun d2 ->
              {
                wtyp = ();
                c_wtyp =
                  (Obj.magic
                     (Compiler_Languages.weak_pair () () ()
                        (Obj.magic (weak_exportable_super (left rcs) () d1))
                        ()
                        (Obj.magic (weak_exportable_super (right rcs) () d2))));
                export =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun eff_rcs ->
                          fun uu___ ->
                            match uu___ with
                            | (x, y) ->
                                Obj.magic
                                  ((d1.export (left eff_rcs) x),
                                    (d2.export (right eff_rcs) y))) uu___1
                         uu___)
              }
let exportable_either :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) exportable ->
            unit ->
              (Obj.t, 'pi, unit, unit) exportable ->
                ((Obj.t, Obj.t) FStar_Pervasives.either, 'pi, unit, unit)
                  exportable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          fun t2 ->
            fun d2 ->
              {
                wtyp = ();
                c_wtyp =
                  (Obj.magic
                     (Compiler_Languages.weak_either () () ()
                        (Obj.magic (weak_exportable_super (left rcs) () d1))
                        ()
                        (Obj.magic (weak_exportable_super (right rcs) () d2))));
                export =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun eff_rcs ->
                          fun x ->
                            match x with
                            | FStar_Pervasives.Inl x1 ->
                                Obj.magic
                                  (FStar_Pervasives.Inl
                                     (d1.export (left eff_rcs) x1))
                            | FStar_Pervasives.Inr x1 ->
                                Obj.magic
                                  (FStar_Pervasives.Inr
                                     (d2.export (right eff_rcs) x1))) uu___1
                         uu___)
              }
let exportable_arrow_with_no_pre_and_no_post :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) importable ->
            unit ->
              (Obj.t, 'pi, unit, unit) exportable ->
                (Obj.t -> (Obj.t CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                  'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          fun t2 ->
            fun d2 ->
              {
                wtyp = ();
                c_wtyp =
                  (Obj.magic
                     (Compiler_Languages.weak_arrow () () ()
                        (Obj.magic (weak_importable_super (left rcs) () d1))
                        ()
                        (Obj.magic
                           (Compiler_Languages.weak_resexn () () ()
                              (Obj.magic
                                 (weak_exportable_super (right rcs) () d2))))));
                export =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun eff_rcs ->
                          fun f ->
                            Obj.magic
                              (fun x ->
                                 match d1.import x (left eff_rcs) with
                                 | FStar_Pervasives.Inl x' ->
                                     MIO.dm_gmio_bind () () () ()
                                       (Obj.magic (f x'))
                                       (fun uu___ ->
                                          match uu___ with
                                          | FStar_Pervasives.Inl x'' ->
                                              MIO.lift_pure_dm_gmio
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Pervasives.Inl
                                                           (d2.export
                                                              (right eff_rcs)
                                                              x''))) uu___1)
                                          | FStar_Pervasives.Inr err ->
                                              MIO.lift_pure_dm_gmio
                                                (fun uu___1 ->
                                                   (fun uu___1 ->
                                                      Obj.magic
                                                        (FStar_Pervasives.Inr
                                                           err)) uu___1))
                                 | FStar_Pervasives.Inr err ->
                                     MIO.lift_pure_dm_gmio
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             Obj.magic
                                               (FStar_Pervasives.Inr err))
                                            uu___))) uu___1 uu___)
              }
let exportable_arrow_post_args :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) importable ->
            unit ->
              (Obj.t, 'pi, unit, unit) exportable ->
                unit ->
                  unit ->
                    (Obj.t ->
                       (Obj.t CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          fun t2 ->
            fun d2 ->
              fun post ->
                fun c1 ->
                  {
                    wtyp = ();
                    c_wtyp =
                      (Obj.magic
                         (Compiler_Languages.weak_arrow () () ()
                            (Obj.magic
                               (weak_importable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (Compiler_Languages.weak_resexn () () ()
                                  (Obj.magic
                                     (weak_exportable_super (right rcs) () d2))))));
                    export =
                      (fun eff_rcs ->
                         fun f ->
                           let f' = f in
                           (exportable_arrow_with_no_pre_and_no_post rcs ()
                              () d1 () d2).export eff_rcs f')
                  }
let exportable_arrow_post :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) importable ->
            unit ->
              (Obj.t, 'pi, unit, unit) exportable ->
                unit ->
                  unit ->
                    (Obj.t ->
                       (Obj.t CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          fun t2 ->
            fun d2 ->
              fun post ->
                fun c1 -> exportable_arrow_post_args rcs () () d1 () d2 () ()
type ('a, 'b, 'pre, 'post, 'x, 'h, 'r, 'lt) trivialize_new_post = unit
let enforce_pre :
  't1 't2 .
    unit ->
      unit ->
        (unit, unit) rc_typ ->
          (unit, unit, unit, unit) eff_rc_typ ->
            unit ->
              unit ->
                ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio) ->
                  't1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun fl ->
                     fun pre ->
                       fun rc ->
                         fun eff_rc ->
                           fun post ->
                             fun c_pre ->
                               fun f ->
                                 fun x ->
                                   Obj.magic
                                     (MIO.dm_gmio_bind () () () ()
                                        (Obj.magic (eff_rc ()))
                                        (fun uu___ ->
                                           match uu___ with
                                           | Prims.Mkdtuple2 (h, eff_rc') ->
                                               MIO.dm_gmio_bind () () () ()
                                                 (MIO.lift_pure_dm_gmio
                                                    (fun uu___1 -> uu___))
                                                 (fun uu___1 ->
                                                    MIO.dm_gmio_bind () () ()
                                                      ()
                                                      (Obj.magic (eff_rc' ()))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            if uu___2
                                                            then
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (f x))
                                                            else
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))
                                                           uu___2))))) uu___7
                    uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let enforce_pre_args :
  't1 't2 .
    unit ->
      unit ->
        ('t1, unit) rc_typ ->
          (unit, 't1, unit, unit) eff_rc_typ ->
            unit ->
              unit ->
                ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio) ->
                  't1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun fl ->
                     fun pre ->
                       fun rc ->
                         fun eff_rc ->
                           fun post ->
                             fun c_pre ->
                               fun f ->
                                 fun x ->
                                   Obj.magic
                                     (MIO.dm_gmio_bind () () () ()
                                        (Obj.magic (eff_rc x))
                                        (fun uu___ ->
                                           match uu___ with
                                           | Prims.Mkdtuple2 (h, eff_rc') ->
                                               MIO.dm_gmio_bind () () () ()
                                                 (MIO.lift_pure_dm_gmio
                                                    (fun uu___1 -> uu___))
                                                 (fun uu___1 ->
                                                    MIO.dm_gmio_bind () () ()
                                                      ()
                                                      (Obj.magic (eff_rc' ()))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            if uu___2
                                                            then
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (f x))
                                                            else
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))
                                                           uu___2))))) uu___7
                    uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let rwtyp_rc : 'a 'b 'c 'd . ('a, 'b) rc_typ -> ('c, 'd) rc_typ =
  fun uu___ -> (fun rc -> Obj.magic rc) uu___
let (rwtyp_eff_rc :
  unit ->
    unit ->
      unit ->
        unit ->
          unit ->
            (Obj.t, Obj.t) rc_typ ->
              (unit, Obj.t, Obj.t, unit) eff_rc_typ ->
                (unit, Obj.t, Obj.t, unit) eff_rc_typ)
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun fl ->
                   fun a ->
                     fun b ->
                       fun c ->
                         fun d ->
                           fun rc ->
                             fun eff_rc ->
                               Obj.magic
                                 (fun x ->
                                    MIO.dm_gmio_bind () () () ()
                                      (Obj.magic (eff_rc x))
                                      (fun uu___ ->
                                         MIO.lift_pure_dm_gmio
                                           (fun uu___1 ->
                                              match uu___ with
                                              | Prims.Mkdtuple2
                                                  (initial_h, cont) ->
                                                  Prims.Mkdtuple2
                                                    ((), ((fun y -> cont y)))))))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let exportable_arrow_pre_post_args :
  't1 't2 'pi .
    pck_rc tree ->
      unit ->
        ('t1, 'pi, unit, unit) importable ->
          ('t2, 'pi, unit, unit) exportable ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun d1 ->
        fun d2 ->
          fun pre ->
            fun post ->
              fun c_pre ->
                fun c1 ->
                  {
                    wtyp = ();
                    c_wtyp =
                      (Obj.magic
                         (Compiler_Languages.weak_arrow () () ()
                            (Obj.magic
                               (weak_importable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (Compiler_Languages.weak_resexn () () ()
                                  (Obj.magic
                                     (weak_exportable_super (right rcs) () d2))))));
                    export =
                      (fun eff_rcs ->
                         fun f ->
                           let uu___ = root eff_rcs in
                           match uu___ with
                           | Prims.Mkdtuple2
                               (FStar_Pervasives.Mkdtuple3 (a, b, rc),
                                eff_rc)
                               ->
                               let eff_rc1 =
                                 Obj.magic
                                   (rwtyp_eff_rc () () () () ()
                                      (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                         (FStar_Pervasives.Mkdtuple3
                                            ((), (), rc))) (Obj.magic eff_rc)) in
                               let f' =
                                 enforce_pre_args () () (Obj.magic rc)
                                   eff_rc1 () () f in
                               let rc_pre x h = rc x h (Obj.repr ()) [] in
                               let rcs' = EmptyNode ((left rcs), (right rcs)) in
                               let eff_rcs' =
                                 EmptyNode ((left eff_rcs), (right eff_rcs)) in
                               let d uu___1 =
                                 (Obj.magic
                                    (exportable_arrow_post_args rcs' () ()
                                       (Obj.magic d1) () (Obj.magic d2) ()))
                                   uu___1 in
                               (d ()).export eff_rcs' f')
                  }
let exportable_arrow_pre_post :
  't1 't2 'pi .
    pck_rc tree ->
      unit ->
        ('t1, 'pi, unit, unit) importable ->
          ('t2, 'pi, unit, unit) exportable ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) exportable
  =
  fun rcs ->
    fun fl ->
      fun d1 ->
        fun d2 ->
          fun pre ->
            fun post ->
              fun c_pre ->
                fun c1 ->
                  {
                    wtyp = ();
                    c_wtyp =
                      (Obj.magic
                         (Compiler_Languages.weak_arrow () () ()
                            (Obj.magic
                               (weak_importable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (Compiler_Languages.weak_resexn () () ()
                                  (Obj.magic
                                     (weak_exportable_super (right rcs) () d2))))));
                    export =
                      (fun eff_rcs ->
                         fun f ->
                           let uu___ = root eff_rcs in
                           match uu___ with
                           | Prims.Mkdtuple2
                               (FStar_Pervasives.Mkdtuple3 (a, b, rc),
                                eff_rc)
                               ->
                               let eff_rc1 =
                                 Obj.magic
                                   (rwtyp_eff_rc () () () () ()
                                      (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                         (FStar_Pervasives.Mkdtuple3
                                            ((), (), rc))) (Obj.magic eff_rc)) in
                               let f' =
                                 enforce_pre () () (Obj.magic rc) eff_rc1 ()
                                   () f in
                               let rc_pre x h =
                                 rc (Obj.repr ()) h (Obj.repr ()) [] in
                               let rcs' = EmptyNode ((left rcs), (right rcs)) in
                               let eff_rcs' =
                                 EmptyNode ((left eff_rcs), (right eff_rcs)) in
                               let d uu___1 =
                                 (Obj.magic
                                    (exportable_arrow_post_args rcs' () ()
                                       (Obj.magic d1) () (Obj.magic d2) ()))
                                   uu___1 in
                               (d ()).export eff_rcs' f')
                  }
let weak_is_safely_importable :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, unit, 'pi) Compiler_Languages.weak ->
            (Obj.t, 'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun fl ->
      fun t ->
        fun d ->
          {
            swtyp = ();
            c_swtyp = d;
            safe_import =
              (fun x -> fun uu___ -> match uu___ with | Leaf -> x)
          }
let importable_unit : 'pi . unit -> (unit, 'pi, unit, unit) importable =
  fun fl ->
    {
      wtyp1 = ();
      c_wtyp1 = (Obj.magic (Compiler_Languages.weak_unit () ()));
      import =
        (fun uu___1 ->
           fun uu___ ->
             (fun uu___ ->
                let uu___ = Obj.magic uu___ in
                fun uu___1 ->
                  match uu___1 with
                  | Leaf -> Obj.magic (FStar_Pervasives.Inl ())) uu___1 uu___)
    }
let importable_file_descr :
  'pi . unit -> (UnixTypes.file_descr, 'pi, unit, unit) importable =
  fun fl ->
    {
      wtyp1 = ();
      c_wtyp1 = (Obj.magic (Compiler_Languages.weak_int () ()));
      import =
        (fun uu___1 ->
           fun uu___ ->
             (fun fd ->
                let fd = Obj.magic fd in
                fun uu___ ->
                  match uu___ with
                  | Leaf -> Obj.magic (FStar_Pervasives.Inl fd)) uu___1 uu___)
    }
let importable_bytes :
  'pi . unit -> (FStar_Bytes.bytes, 'pi, unit, unit) importable =
  fun fl ->
    {
      wtyp1 = ();
      c_wtyp1 = (Obj.magic (Compiler_Languages.weak_bytes () ()));
      import =
        (fun uu___1 ->
           fun uu___ ->
             (fun b ->
                let b = Obj.magic b in
                fun uu___ ->
                  match uu___ with
                  | Leaf -> Obj.magic (FStar_Pervasives.Inl b)) uu___1 uu___)
    }
let safe_importable_is_importable :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) safe_importable ->
            (Obj.t, 'pi, unit, unit) importable
  =
  fun rcs ->
    fun fl ->
      fun t ->
        fun d ->
          {
            wtyp1 = ();
            c_wtyp1 = (Obj.magic (weak_safe_importable_super rcs () d));
            import =
              (fun x ->
                 fun eff_rcs ->
                   FStar_Pervasives.Inl (d.safe_import x eff_rcs))
          }
let importable_refinement :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) importable ->
            unit ->
              (Obj.t, Obj.t) TC_Checkable.checkable ->
                (Obj.t, 'pi, unit, unit) importable
  =
  fun rcs ->
    fun fl ->
      fun t ->
        fun d ->
          fun rp ->
            fun d1 ->
              {
                wtyp1 = ();
                c_wtyp1 = (Obj.magic (weak_importable_super rcs () d));
                import =
                  (fun x ->
                     fun eff_rcs ->
                       match d.import x eff_rcs with
                       | FStar_Pervasives.Inl x1 ->
                           if d1.TC_Checkable.check x1
                           then FStar_Pervasives.Inl x1
                           else
                             FStar_Pervasives.Inr
                               CommonUtils.Contract_failure
                       | FStar_Pervasives.Inr err -> FStar_Pervasives.Inr err)
              }
let importable_option :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) importable ->
            (Obj.t FStar_Pervasives_Native.option, 'pi, unit, unit)
              importable
  =
  fun rcs ->
    fun fl ->
      fun t ->
        fun d ->
          {
            wtyp1 = ();
            c_wtyp1 =
              (Obj.magic
                 (Compiler_Languages.weak_option () () ()
                    (Obj.magic (weak_importable_super rcs () d))));
            import =
              (fun uu___1 ->
                 fun uu___ ->
                   (fun x ->
                      let x = Obj.magic x in
                      fun eff_rcs ->
                        match Obj.magic x with
                        | FStar_Pervasives_Native.Some x' ->
                            (match d.import x' eff_rcs with
                             | FStar_Pervasives.Inl x'' ->
                                 Obj.magic
                                   (FStar_Pervasives.Inl
                                      (FStar_Pervasives_Native.Some x''))
                             | FStar_Pervasives.Inr err ->
                                 Obj.magic (FStar_Pervasives.Inr err))
                        | FStar_Pervasives_Native.None ->
                            Obj.magic
                              (FStar_Pervasives.Inr
                                 CommonUtils.Contract_failure)) uu___1 uu___)
          }
let importable_pair :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            (Obj.t, 'pi, unit, unit) importable ->
              (Obj.t, 'pi, unit, unit) importable ->
                ((Obj.t * Obj.t), 'pi, unit, unit) importable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun t2 ->
          fun d1 ->
            fun d2 ->
              {
                wtyp1 = ();
                c_wtyp1 =
                  (Obj.magic
                     (Compiler_Languages.weak_pair () () ()
                        (Obj.magic (weak_importable_super (left rcs) () d1))
                        ()
                        (Obj.magic (weak_importable_super (right rcs) () d2))));
                import =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun uu___ ->
                          let uu___ = Obj.magic uu___ in
                          fun eff_rcs ->
                            match Obj.magic uu___ with
                            | (x, y) ->
                                (match ((d1.import x (left eff_rcs)),
                                         (d2.import y (right eff_rcs)))
                                 with
                                 | (FStar_Pervasives.Inl x1,
                                    FStar_Pervasives.Inl y1) ->
                                     Obj.magic
                                       (FStar_Pervasives.Inl (x1, y1))
                                 | uu___1 ->
                                     Obj.magic
                                       (FStar_Pervasives.Inr
                                          CommonUtils.Contract_failure)))
                         uu___1 uu___)
              }
let importable_either :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            (Obj.t, 'pi, unit, unit) importable ->
              (Obj.t, 'pi, unit, unit) importable ->
                ((Obj.t, Obj.t) FStar_Pervasives.either, 'pi, unit, unit)
                  importable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun t2 ->
          fun d1 ->
            fun d2 ->
              {
                wtyp1 = ();
                c_wtyp1 =
                  (Obj.magic
                     (Compiler_Languages.weak_either () () ()
                        (Obj.magic (weak_importable_super (left rcs) () d1))
                        ()
                        (Obj.magic (weak_importable_super (right rcs) () d2))));
                import =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun x ->
                          let x = Obj.magic x in
                          fun eff_rcs ->
                            match Obj.magic x with
                            | FStar_Pervasives.Inl x' ->
                                (match d1.import x' (left eff_rcs) with
                                 | FStar_Pervasives.Inl x'' ->
                                     Obj.magic
                                       (FStar_Pervasives.Inl
                                          (FStar_Pervasives.Inl x''))
                                 | FStar_Pervasives.Inr err ->
                                     Obj.magic (FStar_Pervasives.Inr err))
                            | FStar_Pervasives.Inr y ->
                                (match d2.import y (right eff_rcs) with
                                 | FStar_Pervasives.Inl y' ->
                                     Obj.magic
                                       (FStar_Pervasives.Inl
                                          (FStar_Pervasives.Inr y'))
                                 | FStar_Pervasives.Inr err ->
                                     Obj.magic (FStar_Pervasives.Inr err)))
                         uu___1 uu___)
              }
let importable_dpair_refined :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            unit ->
              (Obj.t, 'pi, unit, unit) importable ->
                (Obj.t, 'pi, unit, unit) importable ->
                  (Obj.t, Obj.t, Obj.t) TC_Checkable.checkable2 ->
                    ((Obj.t, Obj.t) Prims.dtuple2, 'pi, unit, unit)
                      importable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun t2 ->
          fun p ->
            fun d1 ->
              fun d2 ->
                fun d3 ->
                  {
                    wtyp1 = ();
                    c_wtyp1 =
                      (Obj.magic
                         (Compiler_Languages.weak_pair () () ()
                            (Obj.magic
                               (weak_importable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (weak_importable_super (right rcs) () d2))));
                    import =
                      (fun uu___1 ->
                         fun uu___ ->
                           (fun uu___ ->
                              let uu___ = Obj.magic uu___ in
                              fun eff_rcs ->
                                match Obj.magic uu___ with
                                | (x', y') ->
                                    (match ((d1.import x' (left eff_rcs)),
                                             (d2.import y' (right eff_rcs)))
                                     with
                                     | (FStar_Pervasives.Inl x,
                                        FStar_Pervasives.Inl y) ->
                                         if TC_Checkable.check2 () () d3 x y
                                         then
                                           Obj.magic
                                             (FStar_Pervasives.Inl
                                                (Prims.Mkdtuple2 (x, y)))
                                         else
                                           Obj.magic
                                             (FStar_Pervasives.Inr
                                                CommonUtils.Contract_failure)
                                     | uu___1 ->
                                         Obj.magic
                                           (FStar_Pervasives.Inr
                                              CommonUtils.Contract_failure)))
                             uu___1 uu___)
                  }
let safe_importable_resexn :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) importable ->
            (Obj.t CommonUtils.resexn, 'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          {
            swtyp = ();
            c_swtyp =
              (Obj.magic
                 (Compiler_Languages.weak_resexn () () ()
                    (Obj.magic (weak_importable_super rcs () d1))));
            safe_import =
              (fun uu___1 ->
                 fun uu___ ->
                   (fun x ->
                      let x = Obj.magic x in
                      fun eff_rcs ->
                        match Obj.magic x with
                        | FStar_Pervasives.Inl x' ->
                            Obj.magic (d1.import x' eff_rcs)
                        | FStar_Pervasives.Inr y ->
                            Obj.magic (FStar_Pervasives.Inr y)) uu___1 uu___)
          }
let safe_importable_arrow :
  'pi .
    pck_rc tree ->
      unit ->
        unit ->
          (Obj.t, 'pi, unit, unit) exportable ->
            unit ->
              (Obj.t, 'pi, unit, unit) importable ->
                (Obj.t -> (Obj.t CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                  'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun fl ->
      fun t1 ->
        fun d1 ->
          fun t2 ->
            fun d2 ->
              {
                swtyp = ();
                c_swtyp =
                  (Obj.magic
                     (Compiler_Languages.weak_arrow () () ()
                        (Obj.magic (weak_exportable_super (left rcs) () d1))
                        ()
                        (Obj.magic
                           (Compiler_Languages.weak_resexn () () ()
                              (Obj.magic
                                 (weak_importable_super (right rcs) () d2))))));
                safe_import =
                  (fun uu___2 ->
                     fun uu___1 ->
                       fun uu___ ->
                         (fun f ->
                            let f = Obj.magic f in
                            fun eff_rcs ->
                              fun x ->
                                Obj.magic
                                  (MIO.dm_gmio_bind () () () ()
                                     (MIO.lift_pure_dm_gmio
                                        (fun uu___ ->
                                           d1.export (left eff_rcs) x))
                                     (fun x' ->
                                        MIO.dm_gmio_bind () () () ()
                                          (Obj.magic (f x'))
                                          (fun y ->
                                             MIO.lift_pure_dm_gmio
                                               (fun uu___ ->
                                                  (safe_importable_resexn
                                                     (right rcs) () () d2).safe_import
                                                    (Obj.magic y)
                                                    (right eff_rcs))))))
                           uu___2 uu___1 uu___)
              }
let enforce_post_args_res :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            ('t1, 't2 CommonUtils.resexn) rc_typ ->
              (unit, 't1, 't2 CommonUtils.resexn, unit) eff_rc_typ ->
                unit ->
                  unit ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio)
                      ->
                      't1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio
  =
  fun uu___9 ->
    fun uu___8 ->
      fun uu___7 ->
        fun uu___6 ->
          fun uu___5 ->
            fun uu___4 ->
              fun uu___3 ->
                fun uu___2 ->
                  fun uu___1 ->
                    fun uu___ ->
                      (fun fl ->
                         fun pi ->
                           fun pre ->
                             fun post ->
                               fun rc ->
                                 fun eff_rc ->
                                   fun c1post ->
                                     fun c2post ->
                                       fun f ->
                                         fun x ->
                                           Obj.magic
                                             (MIO.dm_gmio_bind () () () ()
                                                (Obj.magic (eff_rc x))
                                                (fun uu___ ->
                                                   match uu___ with
                                                   | Prims.Mkdtuple2
                                                       (h, eff_rc') ->
                                                       MIO.dm_gmio_bind () ()
                                                         () ()
                                                         (Obj.magic (f x))
                                                         (fun r ->
                                                            MIO.dm_gmio_bind
                                                              () () () ()
                                                              (Obj.magic
                                                                 (eff_rc' r))
                                                              (fun uu___1 ->
                                                                 if uu___1
                                                                 then
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___2 ->
                                                                    r)
                                                                 else
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                        uu___9 uu___8 uu___7 uu___6 uu___5 uu___4 uu___3
                        uu___2 uu___1 uu___
let enforce_post_args :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            ('t1, unit) rc_typ ->
              (unit, 't1, unit, unit) eff_rc_typ ->
                unit ->
                  unit ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio)
                      ->
                      't1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio
  =
  fun uu___9 ->
    fun uu___8 ->
      fun uu___7 ->
        fun uu___6 ->
          fun uu___5 ->
            fun uu___4 ->
              fun uu___3 ->
                fun uu___2 ->
                  fun uu___1 ->
                    fun uu___ ->
                      (fun fl ->
                         fun pi ->
                           fun pre ->
                             fun post ->
                               fun rc ->
                                 fun eff_rc ->
                                   fun c1post ->
                                     fun c2post ->
                                       fun f ->
                                         fun x ->
                                           Obj.magic
                                             (MIO.dm_gmio_bind () () () ()
                                                (Obj.magic (eff_rc x))
                                                (fun uu___ ->
                                                   match uu___ with
                                                   | Prims.Mkdtuple2
                                                       (h, eff_rc') ->
                                                       MIO.dm_gmio_bind () ()
                                                         () ()
                                                         (Obj.magic (f x))
                                                         (fun r ->
                                                            MIO.dm_gmio_bind
                                                              () () () ()
                                                              (Obj.magic
                                                                 (eff_rc' ()))
                                                              (fun uu___1 ->
                                                                 if uu___1
                                                                 then
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___2 ->
                                                                    r)
                                                                 else
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                        uu___9 uu___8 uu___7 uu___6 uu___5 uu___4 uu___3
                        uu___2 uu___1 uu___
let enforce_post_res :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            (unit, 't2 CommonUtils.resexn) rc_typ ->
              (unit, unit, 't2 CommonUtils.resexn, unit) eff_rc_typ ->
                unit ->
                  unit ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio)
                      ->
                      't1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio
  =
  fun uu___9 ->
    fun uu___8 ->
      fun uu___7 ->
        fun uu___6 ->
          fun uu___5 ->
            fun uu___4 ->
              fun uu___3 ->
                fun uu___2 ->
                  fun uu___1 ->
                    fun uu___ ->
                      (fun fl ->
                         fun pi ->
                           fun pre ->
                             fun post ->
                               fun rc ->
                                 fun eff_rc ->
                                   fun c1post ->
                                     fun c2post ->
                                       fun f ->
                                         fun x ->
                                           Obj.magic
                                             (MIO.dm_gmio_bind () () () ()
                                                (Obj.magic (eff_rc ()))
                                                (fun uu___ ->
                                                   match uu___ with
                                                   | Prims.Mkdtuple2
                                                       (h, eff_rc') ->
                                                       MIO.dm_gmio_bind () ()
                                                         () ()
                                                         (Obj.magic (f x))
                                                         (fun r ->
                                                            MIO.dm_gmio_bind
                                                              () () () ()
                                                              (Obj.magic
                                                                 (eff_rc' r))
                                                              (fun uu___1 ->
                                                                 if uu___1
                                                                 then
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___2 ->
                                                                    r)
                                                                 else
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                        uu___9 uu___8 uu___7 uu___6 uu___5 uu___4 uu___3
                        uu___2 uu___1 uu___
let enforce_post :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            (unit, unit) rc_typ ->
              (unit, unit, unit, unit) eff_rc_typ ->
                unit ->
                  unit ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio)
                      ->
                      't1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio
  =
  fun uu___9 ->
    fun uu___8 ->
      fun uu___7 ->
        fun uu___6 ->
          fun uu___5 ->
            fun uu___4 ->
              fun uu___3 ->
                fun uu___2 ->
                  fun uu___1 ->
                    fun uu___ ->
                      (fun fl ->
                         fun pi ->
                           fun pre ->
                             fun post ->
                               fun rc ->
                                 fun eff_rc ->
                                   fun c1post ->
                                     fun c2post ->
                                       fun f ->
                                         fun x ->
                                           Obj.magic
                                             (MIO.dm_gmio_bind () () () ()
                                                (Obj.magic (eff_rc ()))
                                                (fun uu___ ->
                                                   match uu___ with
                                                   | Prims.Mkdtuple2
                                                       (h, eff_rc') ->
                                                       MIO.dm_gmio_bind () ()
                                                         () ()
                                                         (Obj.magic (f x))
                                                         (fun r ->
                                                            MIO.dm_gmio_bind
                                                              () () () ()
                                                              (Obj.magic
                                                                 (eff_rc' ()))
                                                              (fun uu___1 ->
                                                                 if uu___1
                                                                 then
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___2 ->
                                                                    r)
                                                                 else
                                                                   MIO.lift_pure_dm_gmio
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                        uu___9 uu___8 uu___7 uu___6 uu___5 uu___4 uu___3
                        uu___2 uu___1 uu___
let safe_importable_arrow_pre_post_args_res :
  't1 't2 'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            unit ->
              unit ->
                ('t1, 'pi, unit, unit) exportable ->
                  ('t2, 'pi, unit, unit) importable ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun fl ->
      fun pre ->
        fun post ->
          fun c1post ->
            fun c2post ->
              fun d1 ->
                fun d2 ->
                  {
                    swtyp = ();
                    c_swtyp =
                      (Obj.magic
                         (Compiler_Languages.weak_arrow () () ()
                            (Obj.magic
                               (weak_exportable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (Compiler_Languages.weak_resexn () () ()
                                  (Obj.magic
                                     (weak_importable_super (right rcs) () d2))))));
                    safe_import =
                      (fun uu___2 ->
                         fun uu___1 ->
                           fun uu___ ->
                             (fun f ->
                                let f = Obj.magic f in
                                fun eff_rcs ->
                                  let rcs' =
                                    EmptyNode ((left rcs), (right rcs)) in
                                  let eff_rcs' =
                                    EmptyNode
                                      ((left eff_rcs), (right eff_rcs)) in
                                  let f' =
                                    (Obj.magic
                                       (safe_importable_arrow rcs' () ()
                                          (Obj.magic d1) () (Obj.magic d2))).safe_import
                                      (Obj.magic f) eff_rcs' in
                                  let uu___ = root eff_rcs in
                                  match uu___ with
                                  | Prims.Mkdtuple2 (rc_pck, eff_rc) ->
                                      Obj.magic
                                        (enforce_post_args_res () () () ()
                                           (Obj.magic
                                              (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                 rc_pck))
                                           (Obj.magic
                                              (rwtyp_eff_rc () () () () ()
                                                 (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                    rc_pck)
                                                 (Obj.magic eff_rc))) () ()
                                           f')) uu___2 uu___1 uu___)
                  }
let safe_importable_arrow_pre_post_res :
  't1 't2 'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            unit ->
              unit ->
                ('t1, 'pi, unit, unit) exportable ->
                  ('t2, 'pi, unit, unit) importable ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun fl ->
      fun pre ->
        fun post ->
          fun c1post ->
            fun c2post ->
              fun d1 ->
                fun d2 ->
                  {
                    swtyp = ();
                    c_swtyp =
                      (Obj.magic
                         (Compiler_Languages.weak_arrow () () ()
                            (Obj.magic
                               (weak_exportable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (Compiler_Languages.weak_resexn () () ()
                                  (Obj.magic
                                     (weak_importable_super (right rcs) () d2))))));
                    safe_import =
                      (fun uu___2 ->
                         fun uu___1 ->
                           fun uu___ ->
                             (fun f ->
                                let f = Obj.magic f in
                                fun eff_rcs ->
                                  let rcs' =
                                    EmptyNode ((left rcs), (right rcs)) in
                                  let eff_rcs' =
                                    EmptyNode
                                      ((left eff_rcs), (right eff_rcs)) in
                                  let f' =
                                    (Obj.magic
                                       (safe_importable_arrow rcs' () ()
                                          (Obj.magic d1) () (Obj.magic d2))).safe_import
                                      (Obj.magic f) eff_rcs' in
                                  let uu___ = root eff_rcs in
                                  match uu___ with
                                  | Prims.Mkdtuple2 (rc_pck, eff_rc) ->
                                      Obj.magic
                                        (enforce_post_res () () () ()
                                           (Obj.magic
                                              (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                 rc_pck))
                                           (Obj.magic
                                              (rwtyp_eff_rc () () () () ()
                                                 (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                    rc_pck)
                                                 (Obj.magic eff_rc))) () ()
                                           f')) uu___2 uu___1 uu___)
                  }
let safe_importable_arrow_pre_post_args :
  't1 't2 'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            unit ->
              unit ->
                ('t1, 'pi, unit, unit) exportable ->
                  ('t2, 'pi, unit, unit) importable ->
                    ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                      'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun fl ->
      fun pre ->
        fun post ->
          fun c1post ->
            fun c2post ->
              fun d1 ->
                fun d2 ->
                  {
                    swtyp = ();
                    c_swtyp =
                      (Obj.magic
                         (Compiler_Languages.weak_arrow () () ()
                            (Obj.magic
                               (weak_exportable_super (left rcs) () d1)) ()
                            (Obj.magic
                               (Compiler_Languages.weak_resexn () () ()
                                  (Obj.magic
                                     (weak_importable_super (right rcs) () d2))))));
                    safe_import =
                      (fun uu___2 ->
                         fun uu___1 ->
                           fun uu___ ->
                             (fun f ->
                                let f = Obj.magic f in
                                fun eff_rcs ->
                                  let rcs' =
                                    EmptyNode ((left rcs), (right rcs)) in
                                  let eff_rcs' =
                                    EmptyNode
                                      ((left eff_rcs), (right eff_rcs)) in
                                  let f' =
                                    (Obj.magic
                                       (safe_importable_arrow rcs' () ()
                                          (Obj.magic d1) () (Obj.magic d2))).safe_import
                                      (Obj.magic f) eff_rcs' in
                                  let uu___ = root eff_rcs in
                                  match uu___ with
                                  | Prims.Mkdtuple2 (rc_pck, eff_rc) ->
                                      Obj.magic
                                        (enforce_post_args () () () ()
                                           (Obj.magic
                                              (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                 rc_pck))
                                           (Obj.magic
                                              (rwtyp_eff_rc () () () () ()
                                                 (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                    rc_pck)
                                                 (Obj.magic eff_rc))) () ()
                                           f')) uu___2 uu___1 uu___)
                  }
let safe_importable_arrow_pre_post :
  't1 't2 'pre 'post 'pi .
    pck_rc tree ->
      unit ->
        unit ->
          unit ->
            ('t1, 'pi, unit, unit) exportable ->
              ('t2, 'pi, unit, unit) importable ->
                ('t1 -> ('t2 CommonUtils.resexn, unit, unit) MIO.dm_gmio,
                  'pi, unit, unit) safe_importable
  =
  fun rcs ->
    fun c1post ->
      fun c2post ->
        fun fl ->
          fun d1 ->
            fun d2 ->
              {
                swtyp = ();
                c_swtyp =
                  (Obj.magic
                     (Compiler_Languages.weak_arrow () () ()
                        (Obj.magic (weak_exportable_super (left rcs) () d1))
                        ()
                        (Obj.magic
                           (Compiler_Languages.weak_resexn () () ()
                              (Obj.magic
                                 (weak_importable_super (right rcs) () d2))))));
                safe_import =
                  (fun uu___2 ->
                     fun uu___1 ->
                       fun uu___ ->
                         (fun f ->
                            let f = Obj.magic f in
                            fun eff_rcs ->
                              let rcs' = EmptyNode ((left rcs), (right rcs)) in
                              let eff_rcs' =
                                EmptyNode ((left eff_rcs), (right eff_rcs)) in
                              let f' =
                                (Obj.magic
                                   (safe_importable_arrow rcs' () ()
                                      (Obj.magic d1) () (Obj.magic d2))).safe_import
                                  (Obj.magic f) eff_rcs' in
                              let uu___ = root eff_rcs in
                              match uu___ with
                              | Prims.Mkdtuple2 (rc_pck, eff_rc) ->
                                  Obj.magic
                                    (enforce_post () () () ()
                                       (Obj.magic
                                          (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                             rc_pck))
                                       (Obj.magic
                                          (rwtyp_eff_rc () () () () ()
                                             (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                rc_pck) (Obj.magic eff_rc)))
                                       () () f')) uu___2 uu___1 uu___)
              }
