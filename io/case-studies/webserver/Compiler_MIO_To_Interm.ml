open Prims
let (get_trace : unit -> unit -> (unit, unit, unit, Obj.t) MIO.dm_gmio) =
  fun mst ->
    fun uu___ ->
      MIO_Sig_Call.mio_call () Free.Prog MIO_Sig.GetTrace (Obj.repr ())
let (get_state : unit -> unit -> (unit, unit, unit, unit) MIO.dm_gmio) =
  fun mst ->
    fun uu___ ->
      MIO_Sig_Call.mio_call () Free.Prog MIO_Sig.GetST (Obj.repr ())
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
type ('mst, 'argt, 'rett) dc_typ =
  'argt -> Obj.t -> 'rett -> Obj.t -> Prims.bool
type ('a, 'b, 'mst, 'dc, 's0, 'x, 'y, 'h1, 'uuuuu,
  'lt) eff_dc_typ_cont_post = Obj.t
type ('mst, 'fl, 't1, 't2, 'dc, 'x, 's0) eff_dc_typ_cont =
  't2 -> ((unit * Prims.bool), unit, unit, unit) MIO.dm_gmio
type ('mst, 'fl, 't1, 't2, 'dc) eff_dc_typ =
  't1 ->
    ((unit, (unit, unit, 't1, 't2, unit, unit, unit) eff_dc_typ_cont)
       Prims.dtuple2,
      unit, unit, unit) MIO.dm_gmio
let (enforce_dc :
  unit ->
    unit ->
      unit ->
        (unit, Obj.t, Obj.t) dc_typ ->
          (unit, unit, Obj.t, Obj.t, unit) eff_dc_typ)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun mst ->
             fun argt ->
               fun rett ->
                 fun dc ->
                   Obj.magic
                     (fun x ->
                        MIO.dm_gmio_bind () () () () ()
                          (Obj.magic (get_state () ()))
                          (fun s0 ->
                             MIO.lift_pure_dm_gmio () ()
                               (fun uu___ ->
                                  Prims.Mkdtuple2
                                    ((),
                                      (Obj.magic
                                         (fun y ->
                                            MIO.dm_gmio_bind () () () () ()
                                              (Obj.magic (get_state () ()))
                                              (fun s1 ->
                                                 MIO.lift_pure_dm_gmio () ()
                                                   (fun uu___1 ->
                                                      ((), (dc x s0 y s1)))))))))))
            uu___3 uu___2 uu___1 uu___
type 'mst pck_dc =
  (unit, unit, (unit, Obj.t, Obj.t) dc_typ) FStar_Pervasives.dtuple3
type ('mst, 'ctr) arg_typ = Obj.t
type ('mst, 'ctr) ret_typ = Obj.t
let (check :
  unit -> unit pck_dc -> Obj.t -> Obj.t -> Obj.t -> Obj.t -> Prims.bool) =
  fun mst ->
    fun ctr ->
      fun arg ->
        fun s0 ->
          fun ret ->
            fun s1 ->
              FStar_Pervasives.__proj__Mkdtuple3__item___3 ctr arg s0 ret s1
type ('mst, 'fl) eff_pck_dc =
  (unit pck_dc, (unit, unit, unit, unit, unit) eff_dc_typ) Prims.dtuple2
let (make_dc_eff : unit -> unit pck_dc -> (unit, unit) eff_pck_dc) =
  fun mst ->
    fun r ->
      Prims.Mkdtuple2
        (r,
          (Obj.magic
             (enforce_dc () () ()
                (FStar_Pervasives.__proj__Mkdtuple3__item___3 r))))
type ('mst, 'fl, 'dcs) typ_eff_dcs = (unit, unit) eff_pck_dc tree
let (typ_left :
  unit ->
    unit ->
      unit pck_dc tree ->
        (unit, unit, unit) typ_eff_dcs -> (unit, unit, unit) typ_eff_dcs)
  = fun mst -> fun fl -> fun dcs -> fun t -> left t
let (typ_right :
  unit ->
    unit ->
      unit pck_dc tree ->
        (unit, unit, unit) typ_eff_dcs -> (unit, unit, unit) typ_eff_dcs)
  = fun mst -> fun fl -> fun dcs -> fun t -> right t
let (make_dcs_eff :
  unit -> unit pck_dc tree -> (unit, unit, unit) typ_eff_dcs) =
  fun mst ->
    fun dcs ->
      let r = map_tree dcs (make_dc_eff ()) in
      let comp x = FStar_Pervasives.dfst (make_dc_eff () x) in r
type ('styp, 'fl, 'pi, 'mst, 'dcs) exportable =
  {
  ityp: unit ;
  c_ityp: (Obj.t, unit, 'pi, unit) Compiler_Languages.interm ;
  export: (unit, unit, unit) typ_eff_dcs -> 'styp -> Obj.t }
let __proj__Mkexportable__item__c_ityp :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) exportable ->
              (unit, unit, Obj.t, unit) Compiler_Languages.interm
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun fl ->
               fun pi ->
                 fun mst ->
                   fun dcs ->
                     fun projectee ->
                       match projectee with
                       | { ityp; c_ityp; export;_} -> Obj.magic c_ityp)
              uu___4 uu___3 uu___2 uu___1 uu___
let __proj__Mkexportable__item__export :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) exportable ->
              (unit, unit, unit) typ_eff_dcs -> 'styp -> Obj.t
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun projectee ->
            match projectee with | { ityp; c_ityp; export;_} -> export
type ('styp, 'fl, 'pi, 'mst, 'dcs) safe_importable =
  {
  ityp1: unit ;
  c_ityp1: (Obj.t, unit, 'pi, unit) Compiler_Languages.interm ;
  safe_import: Obj.t -> (unit, unit, unit) typ_eff_dcs -> 'styp }
let __proj__Mksafe_importable__item__c_ityp :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) safe_importable ->
              (unit, unit, Obj.t, unit) Compiler_Languages.interm
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun fl ->
               fun pi ->
                 fun mst ->
                   fun dcs ->
                     fun projectee ->
                       match projectee with
                       | { ityp1 = ityp; c_ityp1 = c_ityp; safe_import;_} ->
                           Obj.magic c_ityp) uu___4 uu___3 uu___2 uu___1
              uu___
let __proj__Mksafe_importable__item__safe_import :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) safe_importable ->
              Obj.t -> (unit, unit, unit) typ_eff_dcs -> 'styp
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun projectee ->
            match projectee with
            | { ityp1 = ityp; c_ityp1 = c_ityp; safe_import;_} -> safe_import
type ('styp, 'fl, 'pi, 'mst, 'dcs) importable =
  {
  ityp2: unit ;
  c_ityp2: (Obj.t, unit, 'pi, unit) Compiler_Languages.interm ;
  import: Obj.t -> (unit, unit, unit) typ_eff_dcs -> 'styp CommonUtils.resexn }
let __proj__Mkimportable__item__c_ityp :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) importable ->
              (unit, unit, Obj.t, unit) Compiler_Languages.interm
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun fl ->
               fun pi ->
                 fun mst ->
                   fun dcs ->
                     fun projectee ->
                       match projectee with
                       | { ityp2 = ityp; c_ityp2 = c_ityp; import;_} ->
                           Obj.magic c_ityp) uu___4 uu___3 uu___2 uu___1
              uu___
let __proj__Mkimportable__item__import :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) importable ->
              Obj.t ->
                (unit, unit, unit) typ_eff_dcs -> 'styp CommonUtils.resexn
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun projectee ->
            match projectee with
            | { ityp2 = ityp; c_ityp2 = c_ityp; import;_} -> import
let interm_importable_super :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) importable ->
              (unit, unit, Obj.t, unit) Compiler_Languages.interm
  = fun fl -> fun pi -> fun mst -> fun dcs -> fun d -> Obj.magic d.c_ityp2
let interm_exportable_super :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) exportable ->
              (unit, unit, Obj.t, unit) Compiler_Languages.interm
  = fun fl -> fun pi -> fun mst -> fun dcs -> fun d -> Obj.magic d.c_ityp
let interm_safe_importable_super :
  'styp .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('styp, unit, Obj.t, unit, unit) safe_importable ->
              (unit, unit, Obj.t, unit) Compiler_Languages.interm
  = fun fl -> fun pi -> fun mst -> fun dcs -> fun d -> Obj.magic d.c_ityp1
let (interm_is_exportable :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit) Compiler_Languages.interm ->
              (Obj.t, unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t ->
            fun d1 ->
              {
                ityp = ();
                c_ityp = d1;
                export = (fun uu___ -> fun x -> match uu___ with | Leaf -> x)
              }
let (exportable_unit :
  unit -> unit -> unit -> (unit, unit, Obj.t, unit, unit) exportable) =
  fun fl ->
    fun pi ->
      fun mst ->
        {
          ityp = ();
          c_ityp = (Obj.magic (Compiler_Languages.interm_unit () () ()));
          export =
            (fun uu___1 ->
               fun uu___ ->
                 (fun uu___ -> fun uu___1 -> Obj.magic ()) uu___1 uu___)
        }
let (exportable_file_descr :
  unit ->
    unit ->
      unit -> (UnixTypes.file_descr, unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        {
          ityp = ();
          c_ityp = (Obj.magic (Compiler_Languages.interm_int () () ()));
          export =
            (fun uu___1 ->
               fun uu___ ->
                 (fun uu___ ->
                    fun fd -> match uu___ with | Leaf -> Obj.magic fd) uu___1
                   uu___)
        }
let (exportable_bytes :
  unit ->
    unit -> unit -> (FStar_Bytes.bytes, unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        {
          ityp = ();
          c_ityp = (Obj.magic (Compiler_Languages.interm_bytes () () ()));
          export =
            (fun uu___1 ->
               fun uu___ ->
                 (fun uu___ ->
                    fun b -> match uu___ with | Leaf -> Obj.magic b) uu___1
                   uu___)
        }
let (exportable_refinement :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) exportable ->
              unit -> (Obj.t, unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t ->
            fun d ->
              fun p ->
                {
                  ityp = ();
                  c_ityp =
                    (Obj.magic (interm_exportable_super () () () dcs d));
                  export = (d.export)
                }
let (exportable_option :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) exportable ->
              (Obj.t FStar_Pervasives_Native.option, unit, Obj.t, unit, 
                unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              {
                ityp = ();
                c_ityp =
                  (Obj.magic
                     (Compiler_Languages.interm_option () () () ()
                        (Obj.magic (interm_exportable_super () () () dcs d1))));
                export =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun eff_dcs ->
                          fun x ->
                            match x with
                            | FStar_Pervasives_Native.Some x' ->
                                Obj.magic
                                  (FStar_Pervasives_Native.Some
                                     (d1.export eff_dcs x'))
                            | FStar_Pervasives_Native.None ->
                                Obj.magic FStar_Pervasives_Native.None)
                         uu___1 uu___)
              }
let (exportable_pair :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) exportable ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) exportable ->
                  ((Obj.t * Obj.t), unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              fun t2 ->
                fun d2 ->
                  {
                    ityp = ();
                    c_ityp =
                      (Obj.magic
                         (Compiler_Languages.interm_pair () () () ()
                            (Obj.magic
                               (interm_exportable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (interm_exportable_super () () () (right dcs)
                                  d2))));
                    export =
                      (fun uu___1 ->
                         fun uu___ ->
                           (fun eff_dcs ->
                              fun uu___ ->
                                match uu___ with
                                | (x, y) ->
                                    Obj.magic
                                      ((d1.export (left eff_dcs) x),
                                        (d2.export (right eff_dcs) y)))
                             uu___1 uu___)
                  }
let (exportable_either :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) exportable ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) exportable ->
                  ((Obj.t, Obj.t) FStar_Pervasives.either, unit, Obj.t, 
                    unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              fun t2 ->
                fun d2 ->
                  {
                    ityp = ();
                    c_ityp =
                      (Obj.magic
                         (Compiler_Languages.interm_either () () () ()
                            (Obj.magic
                               (interm_exportable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (interm_exportable_super () () () (right dcs)
                                  d2))));
                    export =
                      (fun uu___1 ->
                         fun uu___ ->
                           (fun eff_dcs ->
                              fun x ->
                                match x with
                                | FStar_Pervasives.Inl x1 ->
                                    Obj.magic
                                      (FStar_Pervasives.Inl
                                         (d1.export (left eff_dcs) x1))
                                | FStar_Pervasives.Inr x1 ->
                                    Obj.magic
                                      (FStar_Pervasives.Inr
                                         (d2.export (right eff_dcs) x1)))
                             uu___1 uu___)
                  }
let (exportable_arrow_with_no_pre_and_no_post :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) importable ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) exportable ->
                  (Obj.t ->
                     (Obj.t CommonUtils.resexn, unit, unit, unit) MIO.dm_gmio,
                    unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              fun t2 ->
                fun d2 ->
                  {
                    ityp = ();
                    c_ityp =
                      (Obj.magic
                         (Compiler_Languages.interm_arrow () () () ()
                            (Obj.magic
                               (interm_importable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (Compiler_Languages.interm_resexn () () () ()
                                  (Obj.magic
                                     (interm_exportable_super () () ()
                                        (right dcs) d2))))));
                    export =
                      (fun uu___1 ->
                         fun uu___ ->
                           (fun eff_dcs ->
                              fun f ->
                                Obj.magic
                                  (fun x ->
                                     match d1.import x (left eff_dcs) with
                                     | FStar_Pervasives.Inl x' ->
                                         MIO.dm_gmio_bind () () () () ()
                                           (Obj.magic (f x'))
                                           (fun uu___ ->
                                              match uu___ with
                                              | FStar_Pervasives.Inl x'' ->
                                                  MIO.lift_pure_dm_gmio () ()
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          Obj.magic
                                                            (FStar_Pervasives.Inl
                                                               (d2.export
                                                                  (right
                                                                    eff_dcs)
                                                                  x'')))
                                                         uu___1)
                                              | FStar_Pervasives.Inr err ->
                                                  MIO.lift_pure_dm_gmio () ()
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          Obj.magic
                                                            (FStar_Pervasives.Inr
                                                               err)) uu___1))
                                     | FStar_Pervasives.Inr err ->
                                         MIO.lift_pure_dm_gmio () ()
                                           (fun uu___ ->
                                              (fun uu___ ->
                                                 Obj.magic
                                                   (FStar_Pervasives.Inr err))
                                                uu___))) uu___1 uu___)
                  }
let (exportable_arrow_post_args :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) importable ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) exportable ->
                  unit ->
                    unit ->
                      (Obj.t ->
                         (Obj.t CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio,
                        unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              fun t2 ->
                fun d2 ->
                  fun post ->
                    fun c1 ->
                      {
                        ityp = ();
                        c_ityp =
                          (Obj.magic
                             (Compiler_Languages.interm_arrow () () () ()
                                (Obj.magic
                                   (interm_importable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (Compiler_Languages.interm_resexn () () ()
                                      ()
                                      (Obj.magic
                                         (interm_exportable_super () () ()
                                            (right dcs) d2))))));
                        export =
                          (fun eff_dcs ->
                             fun f ->
                               let f' = f in
                               (exportable_arrow_with_no_pre_and_no_post ()
                                  () () dcs () d1 () d2).export eff_dcs f')
                      }
let (exportable_arrow_post :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) importable ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) exportable ->
                  unit ->
                    unit ->
                      (Obj.t ->
                         (Obj.t CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio,
                        unit, Obj.t, unit, unit) exportable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              fun t2 ->
                fun d2 ->
                  fun post ->
                    fun c1 ->
                      exportable_arrow_post_args () () () dcs () d1 () d2 ()
                        ()
type ('a, 'b, 'mst, 'dc, 'post, 'x, 'h, 'r, 'lt) trivialize_new_post = unit
let enforce_pre :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            (unit, unit, unit) dc_typ ->
              (unit, unit, unit, unit, unit) eff_dc_typ ->
                unit ->
                  unit ->
                    unit ->
                      ('t1 ->
                         ('t2 CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio)
                        ->
                        't1 ->
                          ('t2 CommonUtils.resexn, unit, unit, unit)
                            MIO.dm_gmio
  =
  fun uu___10 ->
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
                             fun mst ->
                               fun pre ->
                                 fun dc ->
                                   fun eff_dc ->
                                     fun post ->
                                       fun c_pre ->
                                         fun c_post ->
                                           fun f ->
                                             fun x ->
                                               Obj.magic
                                                 (MIO.dm_gmio_bind () () ()
                                                    () ()
                                                    (Obj.magic (eff_dc ()))
                                                    (fun uu___ ->
                                                       match uu___ with
                                                       | Prims.Mkdtuple2
                                                           (s0, eff_dc') ->
                                                           MIO.dm_gmio_bind
                                                             () () () () ()
                                                             (Obj.magic
                                                                (eff_dc' ()))
                                                             (fun uu___1 ->
                                                                (fun uu___1
                                                                   ->
                                                                   match uu___1
                                                                   with
                                                                   | 
                                                                   (s1, b) ->
                                                                    if b
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (f x))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (MIO.lift_pure_dm_gmio
                                                                    () ()
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))
                                                                  uu___1))))
                          uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4
                          uu___3 uu___2 uu___1 uu___
let enforce_pre_args :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            (unit, 't1, unit) dc_typ ->
              (unit, unit, 't1, unit, unit) eff_dc_typ ->
                unit ->
                  unit ->
                    unit ->
                      ('t1 ->
                         ('t2 CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio)
                        ->
                        't1 ->
                          ('t2 CommonUtils.resexn, unit, unit, unit)
                            MIO.dm_gmio
  =
  fun uu___10 ->
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
                             fun mst ->
                               fun pre ->
                                 fun dc ->
                                   fun eff_dc ->
                                     fun post ->
                                       fun c_pre ->
                                         fun c_post ->
                                           fun f ->
                                             fun x ->
                                               Obj.magic
                                                 (MIO.dm_gmio_bind () () ()
                                                    () ()
                                                    (Obj.magic (eff_dc x))
                                                    (fun uu___ ->
                                                       match uu___ with
                                                       | Prims.Mkdtuple2
                                                           (uu___1, eff_dc')
                                                           ->
                                                           MIO.dm_gmio_bind
                                                             () () () () ()
                                                             (Obj.magic
                                                                (eff_dc' ()))
                                                             (fun uu___2 ->
                                                                (fun uu___2
                                                                   ->
                                                                   match uu___2
                                                                   with
                                                                   | 
                                                                   (uu___3,
                                                                    b) ->
                                                                    if b
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (f x))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (MIO.lift_pure_dm_gmio
                                                                    () ()
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))
                                                                  uu___2))))
                          uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4
                          uu___3 uu___2 uu___1 uu___
let (rityp_eff_dc :
  unit ->
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, Obj.t, Obj.t) dc_typ ->
                (unit, unit, Obj.t, Obj.t, unit) eff_dc_typ ->
                  (unit, unit, Obj.t, Obj.t, unit) eff_dc_typ)
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun mst ->
                     fun fl ->
                       fun a ->
                         fun b ->
                           fun c ->
                             fun d ->
                               fun dc ->
                                 fun eff_dc ->
                                   Obj.magic
                                     (fun x ->
                                        MIO.dm_gmio_bind () () () () ()
                                          (Obj.magic (eff_dc x))
                                          (fun uu___ ->
                                             MIO.lift_pure_dm_gmio () ()
                                               (fun uu___1 ->
                                                  match uu___ with
                                                  | Prims.Mkdtuple2
                                                      (s0, cont) ->
                                                      Prims.Mkdtuple2
                                                        ((),
                                                          ((fun y -> cont y)))))))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let exportable_arrow_pre_post_args :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('t1, unit, Obj.t, unit, unit) importable ->
              ('t2, unit, Obj.t, unit, unit) exportable ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        ('t1 ->
                           ('t2 CommonUtils.resexn, unit, unit, unit)
                             MIO.dm_gmio,
                          unit, Obj.t, unit, unit) exportable
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun d1 ->
            fun d2 ->
              fun pre ->
                fun post ->
                  fun c_pre ->
                    fun c_post ->
                      {
                        ityp = ();
                        c_ityp =
                          (Obj.magic
                             (Compiler_Languages.interm_arrow () () () ()
                                (Obj.magic
                                   (interm_importable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (Compiler_Languages.interm_resexn () () ()
                                      ()
                                      (Obj.magic
                                         (interm_exportable_super () () ()
                                            (right dcs) d2))))));
                        export =
                          (fun eff_dcs ->
                             fun f ->
                               let uu___ = root eff_dcs in
                               match uu___ with
                               | Prims.Mkdtuple2
                                   (FStar_Pervasives.Mkdtuple3 (a, b, dc),
                                    eff_dc)
                                   ->
                                   let eff_dc1 =
                                     Obj.magic
                                       (rityp_eff_dc () () () () () ()
                                          (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                             (FStar_Pervasives.Mkdtuple3
                                                ((), (), dc)))
                                          (Obj.magic eff_dc)) in
                                   let dcs' =
                                     EmptyNode ((left dcs), (right dcs)) in
                                   let d uu___1 =
                                     (Obj.magic
                                        (exportable_arrow_post_args () () ()
                                           dcs' () (Obj.magic d1) ()
                                           (Obj.magic d2) ())) uu___1 in
                                   let eff_dcs' =
                                     EmptyNode
                                       ((left eff_dcs), (right eff_dcs)) in
                                   let f' =
                                     enforce_pre_args () () () ()
                                       (Obj.magic dc) eff_dc1 () () () f in
                                   (d ()).export eff_dcs' f')
                      }
let exportable_arrow_pre_post :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            ('t1, unit, Obj.t, unit, unit) importable ->
              ('t2, unit, Obj.t, unit, unit) exportable ->
                unit ->
                  unit ->
                    unit ->
                      unit ->
                        ('t1 ->
                           ('t2 CommonUtils.resexn, unit, unit, unit)
                             MIO.dm_gmio,
                          unit, Obj.t, unit, unit) exportable
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun d1 ->
            fun d2 ->
              fun pre ->
                fun post ->
                  fun c_pre ->
                    fun c_post ->
                      {
                        ityp = ();
                        c_ityp =
                          (Obj.magic
                             (Compiler_Languages.interm_arrow () () () ()
                                (Obj.magic
                                   (interm_importable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (Compiler_Languages.interm_resexn () () ()
                                      ()
                                      (Obj.magic
                                         (interm_exportable_super () () ()
                                            (right dcs) d2))))));
                        export =
                          (fun eff_dcs ->
                             fun f ->
                               let uu___ = root eff_dcs in
                               match uu___ with
                               | Prims.Mkdtuple2
                                   (FStar_Pervasives.Mkdtuple3 (a, b, dc),
                                    eff_dc)
                                   ->
                                   let eff_dc1 =
                                     Obj.magic
                                       (rityp_eff_dc () () () () () ()
                                          (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                             (FStar_Pervasives.Mkdtuple3
                                                ((), (), dc)))
                                          (Obj.magic eff_dc)) in
                                   let dcs' =
                                     EmptyNode ((left dcs), (right dcs)) in
                                   let d uu___1 =
                                     (Obj.magic
                                        (exportable_arrow_post_args () () ()
                                           dcs' () (Obj.magic d1) ()
                                           (Obj.magic d2) ())) uu___1 in
                                   let eff_dcs' =
                                     EmptyNode
                                       ((left eff_dcs), (right eff_dcs)) in
                                   let f' =
                                     enforce_pre () () () () (Obj.magic dc)
                                       eff_dc1 () () () f in
                                   (d ()).export eff_dcs' f')
                      }
let (interm_is_safely_importable :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit) Compiler_Languages.interm ->
              (Obj.t, unit, Obj.t, unit, unit) safe_importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t ->
            fun d ->
              {
                ityp1 = ();
                c_ityp1 = d;
                safe_import =
                  (fun x -> fun uu___ -> match uu___ with | Leaf -> x)
              }
let (importable_unit :
  unit -> unit -> unit -> (unit, unit, Obj.t, unit, unit) importable) =
  fun fl ->
    fun pi ->
      fun mst ->
        {
          ityp2 = ();
          c_ityp2 = (Obj.magic (Compiler_Languages.interm_unit () () ()));
          import =
            (fun uu___1 ->
               fun uu___ ->
                 (fun uu___ ->
                    let uu___ = Obj.magic uu___ in
                    fun uu___1 ->
                      match uu___1 with
                      | Leaf -> Obj.magic (FStar_Pervasives.Inl ())) uu___1
                   uu___)
        }
let (importable_file_descr :
  unit ->
    unit ->
      unit -> (UnixTypes.file_descr, unit, Obj.t, unit, unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        {
          ityp2 = ();
          c_ityp2 = (Obj.magic (Compiler_Languages.interm_int () () ()));
          import =
            (fun uu___1 ->
               fun uu___ ->
                 (fun fd ->
                    let fd = Obj.magic fd in
                    fun uu___ ->
                      match uu___ with
                      | Leaf -> Obj.magic (FStar_Pervasives.Inl fd)) uu___1
                   uu___)
        }
let (importable_bytes :
  unit ->
    unit -> unit -> (FStar_Bytes.bytes, unit, Obj.t, unit, unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        {
          ityp2 = ();
          c_ityp2 = (Obj.magic (Compiler_Languages.interm_bytes () () ()));
          import =
            (fun uu___1 ->
               fun uu___ ->
                 (fun b ->
                    let b = Obj.magic b in
                    fun uu___ ->
                      match uu___ with
                      | Leaf -> Obj.magic (FStar_Pervasives.Inl b)) uu___1
                   uu___)
        }
let (safe_importable_is_importable :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) safe_importable ->
              (Obj.t, unit, Obj.t, unit, unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t ->
            fun d ->
              {
                ityp2 = ();
                c_ityp2 =
                  (Obj.magic (interm_safe_importable_super () () () dcs d));
                import =
                  (fun x ->
                     fun eff_dcs ->
                       FStar_Pervasives.Inl (d.safe_import x eff_dcs))
              }
let (importable_refinement :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) importable ->
              unit ->
                (Obj.t, Obj.t) TC_Checkable.checkable ->
                  (Obj.t, unit, Obj.t, unit, unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t ->
            fun d ->
              fun rp ->
                fun d1 ->
                  {
                    ityp2 = ();
                    c_ityp2 =
                      (Obj.magic (interm_importable_super () () () dcs d));
                    import =
                      (fun x ->
                         fun eff_dcs ->
                           match d.import x eff_dcs with
                           | FStar_Pervasives.Inl x1 ->
                               if d1.TC_Checkable.check x1
                               then FStar_Pervasives.Inl x1
                               else
                                 FStar_Pervasives.Inr
                                   CommonUtils.Contract_failure
                           | FStar_Pervasives.Inr err ->
                               FStar_Pervasives.Inr err)
                  }
let (importable_option :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) importable ->
              (Obj.t FStar_Pervasives_Native.option, unit, Obj.t, unit, 
                unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t ->
            fun d ->
              {
                ityp2 = ();
                c_ityp2 =
                  (Obj.magic
                     (Compiler_Languages.interm_option () () () ()
                        (Obj.magic (interm_importable_super () () () dcs d))));
                import =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun x ->
                          let x = Obj.magic x in
                          fun eff_dcs ->
                            match Obj.magic x with
                            | FStar_Pervasives_Native.Some x' ->
                                (match d.import x' eff_dcs with
                                 | FStar_Pervasives.Inl x'' ->
                                     Obj.magic
                                       (FStar_Pervasives.Inl
                                          (FStar_Pervasives_Native.Some x''))
                                 | FStar_Pervasives.Inr err ->
                                     Obj.magic (FStar_Pervasives.Inr err))
                            | FStar_Pervasives_Native.None ->
                                Obj.magic
                                  (FStar_Pervasives.Inr
                                     CommonUtils.Contract_failure)) uu___1
                         uu___)
              }
let (importable_pair :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            unit ->
              (Obj.t, unit, Obj.t, unit, unit) importable ->
                (Obj.t, unit, Obj.t, unit, unit) importable ->
                  ((Obj.t * Obj.t), unit, Obj.t, unit, unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun t2 ->
              fun d1 ->
                fun d2 ->
                  {
                    ityp2 = ();
                    c_ityp2 =
                      (Obj.magic
                         (Compiler_Languages.interm_pair () () () ()
                            (Obj.magic
                               (interm_importable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (interm_importable_super () () () (right dcs)
                                  d2))));
                    import =
                      (fun uu___1 ->
                         fun uu___ ->
                           (fun uu___ ->
                              let uu___ = Obj.magic uu___ in
                              fun eff_dcs ->
                                match Obj.magic uu___ with
                                | (x, y) ->
                                    (match ((d1.import x (left eff_dcs)),
                                             (d2.import y (right eff_dcs)))
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
let (importable_either :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            unit ->
              (Obj.t, unit, Obj.t, unit, unit) importable ->
                (Obj.t, unit, Obj.t, unit, unit) importable ->
                  ((Obj.t, Obj.t) FStar_Pervasives.either, unit, Obj.t, 
                    unit, unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun t2 ->
              fun d1 ->
                fun d2 ->
                  {
                    ityp2 = ();
                    c_ityp2 =
                      (Obj.magic
                         (Compiler_Languages.interm_either () () () ()
                            (Obj.magic
                               (interm_importable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (interm_importable_super () () () (right dcs)
                                  d2))));
                    import =
                      (fun uu___1 ->
                         fun uu___ ->
                           (fun x ->
                              let x = Obj.magic x in
                              fun eff_dcs ->
                                match Obj.magic x with
                                | FStar_Pervasives.Inl x' ->
                                    (match d1.import x' (left eff_dcs) with
                                     | FStar_Pervasives.Inl x'' ->
                                         Obj.magic
                                           (FStar_Pervasives.Inl
                                              (FStar_Pervasives.Inl x''))
                                     | FStar_Pervasives.Inr err ->
                                         Obj.magic (FStar_Pervasives.Inr err))
                                | FStar_Pervasives.Inr y ->
                                    (match d2.import y (right eff_dcs) with
                                     | FStar_Pervasives.Inl y' ->
                                         Obj.magic
                                           (FStar_Pervasives.Inl
                                              (FStar_Pervasives.Inr y'))
                                     | FStar_Pervasives.Inr err ->
                                         Obj.magic (FStar_Pervasives.Inr err)))
                             uu___1 uu___)
                  }
let (importable_dpair_refined :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            unit ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) importable ->
                  (Obj.t, unit, Obj.t, unit, unit) importable ->
                    (Obj.t, Obj.t, Obj.t) TC_Checkable.checkable2 ->
                      ((Obj.t, Obj.t) Prims.dtuple2, unit, Obj.t, unit, 
                        unit) importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun t2 ->
              fun p ->
                fun d1 ->
                  fun d2 ->
                    fun d3 ->
                      {
                        ityp2 = ();
                        c_ityp2 =
                          (Obj.magic
                             (Compiler_Languages.interm_pair () () () ()
                                (Obj.magic
                                   (interm_importable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (interm_importable_super () () ()
                                      (right dcs) d2))));
                        import =
                          (fun uu___1 ->
                             fun uu___ ->
                               (fun uu___ ->
                                  let uu___ = Obj.magic uu___ in
                                  fun eff_dcs ->
                                    match Obj.magic uu___ with
                                    | (x', y') ->
                                        (match ((d1.import x' (left eff_dcs)),
                                                 (d2.import y'
                                                    (right eff_dcs)))
                                         with
                                         | (FStar_Pervasives.Inl x,
                                            FStar_Pervasives.Inl y) ->
                                             if
                                               TC_Checkable.check2 () () d3 x
                                                 y
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
let (safe_importable_resexn :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) importable ->
              (Obj.t CommonUtils.resexn, unit, Obj.t, unit, unit)
                safe_importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              {
                ityp1 = ();
                c_ityp1 =
                  (Obj.magic
                     (Compiler_Languages.interm_resexn () () () ()
                        (Obj.magic (interm_importable_super () () () dcs d1))));
                safe_import =
                  (fun uu___1 ->
                     fun uu___ ->
                       (fun x ->
                          let x = Obj.magic x in
                          fun eff_dcs ->
                            match Obj.magic x with
                            | FStar_Pervasives.Inl x' ->
                                Obj.magic (d1.import x' eff_dcs)
                            | FStar_Pervasives.Inr y ->
                                Obj.magic (FStar_Pervasives.Inr y)) uu___1
                         uu___)
              }
let (safe_importable_arrow :
  unit ->
    unit ->
      unit ->
        unit pck_dc tree ->
          unit ->
            (Obj.t, unit, Obj.t, unit, unit) exportable ->
              unit ->
                (Obj.t, unit, Obj.t, unit, unit) importable ->
                  (Obj.t ->
                     (Obj.t CommonUtils.resexn, unit, unit, unit) MIO.dm_gmio,
                    unit, Obj.t, unit, unit) safe_importable)
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun t1 ->
            fun d1 ->
              fun t2 ->
                fun d2 ->
                  {
                    ityp1 = ();
                    c_ityp1 =
                      (Obj.magic
                         (Compiler_Languages.interm_arrow () () () ()
                            (Obj.magic
                               (interm_exportable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (Compiler_Languages.interm_resexn () () () ()
                                  (Obj.magic
                                     (interm_importable_super () () ()
                                        (right dcs) d2))))));
                    safe_import =
                      (fun uu___2 ->
                         fun uu___1 ->
                           fun uu___ ->
                             (fun f ->
                                let f = Obj.magic f in
                                fun eff_dcs ->
                                  fun x ->
                                    Obj.magic
                                      (MIO.dm_gmio_bind () () () () ()
                                         (MIO.lift_pure_dm_gmio () ()
                                            (fun uu___ ->
                                               d1.export (left eff_dcs) x))
                                         (fun x' ->
                                            MIO.dm_gmio_bind () () () () ()
                                              (Obj.magic (f x'))
                                              (fun y ->
                                                 MIO.lift_pure_dm_gmio () ()
                                                   (fun uu___ ->
                                                      (safe_importable_resexn
                                                         () () () (right dcs)
                                                         () d2).safe_import
                                                        (Obj.magic y)
                                                        (right eff_dcs))))))
                               uu___2 uu___1 uu___)
                  }
let enforce_post_args_res :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, 't1, 't2 CommonUtils.resexn) dc_typ ->
                (unit, unit, 't1, 't2 CommonUtils.resexn, unit) eff_dc_typ ->
                  unit ->
                    unit ->
                      ('t1 ->
                         ('t2 CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio)
                        ->
                        't1 ->
                          ('t2 CommonUtils.resexn, unit, unit, unit)
                            MIO.dm_gmio
  =
  fun uu___10 ->
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
                             fun mst ->
                               fun pre ->
                                 fun post ->
                                   fun dc ->
                                     fun eff_dc ->
                                       fun c1_post ->
                                         fun c2_post ->
                                           fun f ->
                                             fun x ->
                                               Obj.magic
                                                 (MIO.dm_gmio_bind () () ()
                                                    () ()
                                                    (Obj.magic (eff_dc x))
                                                    (fun uu___ ->
                                                       match uu___ with
                                                       | Prims.Mkdtuple2
                                                           (uu___1, eff_dc')
                                                           ->
                                                           MIO.dm_gmio_bind
                                                             () () () () ()
                                                             (Obj.magic (f x))
                                                             (fun r ->
                                                                MIO.dm_gmio_bind
                                                                  () () () ()
                                                                  ()
                                                                  (Obj.magic
                                                                    (eff_dc'
                                                                    r))
                                                                  (fun uu___2
                                                                    ->
                                                                    MIO.lift_pure_dm_gmio
                                                                    () ()
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (uu___4,
                                                                    b) ->
                                                                    if b
                                                                    then r
                                                                    else
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                          uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4
                          uu___3 uu___2 uu___1 uu___
let enforce_post_args :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, 't1, unit) dc_typ ->
                (unit, unit, 't1, unit, unit) eff_dc_typ ->
                  unit ->
                    unit ->
                      ('t1 ->
                         ('t2 CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio)
                        ->
                        't1 ->
                          ('t2 CommonUtils.resexn, unit, unit, unit)
                            MIO.dm_gmio
  =
  fun uu___10 ->
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
                             fun mst ->
                               fun pre ->
                                 fun post ->
                                   fun dc ->
                                     fun eff_dc ->
                                       fun c1_post ->
                                         fun c2_post ->
                                           fun f ->
                                             fun x ->
                                               Obj.magic
                                                 (MIO.dm_gmio_bind () () ()
                                                    () ()
                                                    (Obj.magic (eff_dc x))
                                                    (fun uu___ ->
                                                       match uu___ with
                                                       | Prims.Mkdtuple2
                                                           (uu___1, eff_dc')
                                                           ->
                                                           MIO.dm_gmio_bind
                                                             () () () () ()
                                                             (Obj.magic (f x))
                                                             (fun r ->
                                                                MIO.dm_gmio_bind
                                                                  () () () ()
                                                                  ()
                                                                  (Obj.magic
                                                                    (eff_dc'
                                                                    ()))
                                                                  (fun uu___2
                                                                    ->
                                                                    MIO.lift_pure_dm_gmio
                                                                    () ()
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (uu___4,
                                                                    b) ->
                                                                    if b
                                                                    then r
                                                                    else
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                          uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4
                          uu___3 uu___2 uu___1 uu___
let enforce_post_res :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, 't2 CommonUtils.resexn) dc_typ ->
                (unit, unit, unit, 't2 CommonUtils.resexn, unit) eff_dc_typ
                  ->
                  unit ->
                    unit ->
                      ('t1 ->
                         ('t2 CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio)
                        ->
                        't1 ->
                          ('t2 CommonUtils.resexn, unit, unit, unit)
                            MIO.dm_gmio
  =
  fun uu___10 ->
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
                             fun mst ->
                               fun pre ->
                                 fun post ->
                                   fun dc ->
                                     fun eff_dc ->
                                       fun c1_post ->
                                         fun c2_post ->
                                           fun f ->
                                             fun x ->
                                               Obj.magic
                                                 (MIO.dm_gmio_bind () () ()
                                                    () ()
                                                    (Obj.magic (eff_dc ()))
                                                    (fun uu___ ->
                                                       match uu___ with
                                                       | Prims.Mkdtuple2
                                                           (uu___1, eff_dc')
                                                           ->
                                                           MIO.dm_gmio_bind
                                                             () () () () ()
                                                             (Obj.magic (f x))
                                                             (fun r ->
                                                                MIO.dm_gmio_bind
                                                                  () () () ()
                                                                  ()
                                                                  (Obj.magic
                                                                    (eff_dc'
                                                                    r))
                                                                  (fun uu___2
                                                                    ->
                                                                    MIO.lift_pure_dm_gmio
                                                                    () ()
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (uu___4,
                                                                    b) ->
                                                                    if b
                                                                    then r
                                                                    else
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                          uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4
                          uu___3 uu___2 uu___1 uu___
let enforce_post :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit ->
            unit ->
              (unit, unit, unit) dc_typ ->
                (unit, unit, unit, unit, unit) eff_dc_typ ->
                  unit ->
                    unit ->
                      ('t1 ->
                         ('t2 CommonUtils.resexn, unit, unit, unit)
                           MIO.dm_gmio)
                        ->
                        't1 ->
                          ('t2 CommonUtils.resexn, unit, unit, unit)
                            MIO.dm_gmio
  =
  fun uu___10 ->
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
                             fun mst ->
                               fun pre ->
                                 fun post ->
                                   fun dc ->
                                     fun eff_dc ->
                                       fun c1_post ->
                                         fun c2_post ->
                                           fun f ->
                                             fun x ->
                                               Obj.magic
                                                 (MIO.dm_gmio_bind () () ()
                                                    () ()
                                                    (Obj.magic (eff_dc ()))
                                                    (fun uu___ ->
                                                       match uu___ with
                                                       | Prims.Mkdtuple2
                                                           (uu___1, eff_dc')
                                                           ->
                                                           MIO.dm_gmio_bind
                                                             () () () () ()
                                                             (Obj.magic (f x))
                                                             (fun r ->
                                                                MIO.dm_gmio_bind
                                                                  () () () ()
                                                                  ()
                                                                  (Obj.magic
                                                                    (eff_dc'
                                                                    ()))
                                                                  (fun uu___2
                                                                    ->
                                                                    MIO.lift_pure_dm_gmio
                                                                    () ()
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (uu___4,
                                                                    b) ->
                                                                    if b
                                                                    then r
                                                                    else
                                                                    FStar_Pervasives.Inr
                                                                    CommonUtils.Contract_failure))))))
                          uu___10 uu___9 uu___8 uu___7 uu___6 uu___5 uu___4
                          uu___3 uu___2 uu___1 uu___
let safe_importable_arrow_pre_post_args_res :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    ('t1, unit, Obj.t, unit, unit) exportable ->
                      ('t2, unit, Obj.t, unit, unit) importable ->
                        ('t1 ->
                           ('t2 CommonUtils.resexn, unit, unit, unit)
                             MIO.dm_gmio,
                          unit, Obj.t, unit, unit) safe_importable
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun pre ->
            fun post ->
              fun c1post ->
                fun c2post ->
                  fun d1 ->
                    fun d2 ->
                      {
                        ityp1 = ();
                        c_ityp1 =
                          (Obj.magic
                             (Compiler_Languages.interm_arrow () () () ()
                                (Obj.magic
                                   (interm_exportable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (Compiler_Languages.interm_resexn () () ()
                                      ()
                                      (Obj.magic
                                         (interm_importable_super () () ()
                                            (right dcs) d2))))));
                        safe_import =
                          (fun uu___2 ->
                             fun uu___1 ->
                               fun uu___ ->
                                 (fun f ->
                                    let f = Obj.magic f in
                                    fun eff_dcs ->
                                      let dcs' =
                                        EmptyNode ((left dcs), (right dcs)) in
                                      let eff_dcs' =
                                        EmptyNode
                                          ((left eff_dcs), (right eff_dcs)) in
                                      let f' =
                                        (Obj.magic
                                           (safe_importable_arrow () () ()
                                              dcs' () (Obj.magic d1) ()
                                              (Obj.magic d2))).safe_import
                                          (Obj.magic f) eff_dcs' in
                                      let uu___ = root eff_dcs in
                                      match uu___ with
                                      | Prims.Mkdtuple2 (dc_pck, eff_dc) ->
                                          Obj.magic
                                            (enforce_post_args_res () () ()
                                               () ()
                                               (Obj.magic
                                                  (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                     dc_pck))
                                               (Obj.magic
                                                  (rityp_eff_dc () () () ()
                                                     () ()
                                                     (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                        dc_pck)
                                                     (Obj.magic eff_dc))) ()
                                               () f')) uu___2 uu___1 uu___)
                      }
let safe_importable_arrow_pre_post_res :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    ('t1, unit, Obj.t, unit, unit) exportable ->
                      ('t2, unit, Obj.t, unit, unit) importable ->
                        ('t1 ->
                           ('t2 CommonUtils.resexn, unit, unit, unit)
                             MIO.dm_gmio,
                          unit, Obj.t, unit, unit) safe_importable
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun pre ->
            fun post ->
              fun c1post ->
                fun c2post ->
                  fun d1 ->
                    fun d2 ->
                      {
                        ityp1 = ();
                        c_ityp1 =
                          (Obj.magic
                             (Compiler_Languages.interm_arrow () () () ()
                                (Obj.magic
                                   (interm_exportable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (Compiler_Languages.interm_resexn () () ()
                                      ()
                                      (Obj.magic
                                         (interm_importable_super () () ()
                                            (right dcs) d2))))));
                        safe_import =
                          (fun uu___2 ->
                             fun uu___1 ->
                               fun uu___ ->
                                 (fun f ->
                                    let f = Obj.magic f in
                                    fun eff_dcs ->
                                      let dcs' =
                                        EmptyNode ((left dcs), (right dcs)) in
                                      let eff_dcs' =
                                        EmptyNode
                                          ((left eff_dcs), (right eff_dcs)) in
                                      let f' =
                                        (Obj.magic
                                           (safe_importable_arrow () () ()
                                              dcs' () (Obj.magic d1) ()
                                              (Obj.magic d2))).safe_import
                                          (Obj.magic f) eff_dcs' in
                                      let uu___ = root eff_dcs in
                                      match uu___ with
                                      | Prims.Mkdtuple2 (dc_pck, eff_dc) ->
                                          Obj.magic
                                            (enforce_post_res () () () () ()
                                               (Obj.magic
                                                  (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                     dc_pck))
                                               (Obj.magic
                                                  (rityp_eff_dc () () () ()
                                                     () ()
                                                     (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                        dc_pck)
                                                     (Obj.magic eff_dc))) ()
                                               () f')) uu___2 uu___1 uu___)
                      }
let safe_importable_arrow_pre_post_args :
  't1 't2 .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            unit ->
              unit ->
                unit ->
                  unit ->
                    ('t1, unit, Obj.t, unit, unit) exportable ->
                      ('t2, unit, Obj.t, unit, unit) importable ->
                        ('t1 ->
                           ('t2 CommonUtils.resexn, unit, unit, unit)
                             MIO.dm_gmio,
                          unit, Obj.t, unit, unit) safe_importable
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun pre ->
            fun post ->
              fun c1post ->
                fun c2post ->
                  fun d1 ->
                    fun d2 ->
                      {
                        ityp1 = ();
                        c_ityp1 =
                          (Obj.magic
                             (Compiler_Languages.interm_arrow () () () ()
                                (Obj.magic
                                   (interm_exportable_super () () ()
                                      (left dcs) d1)) ()
                                (Obj.magic
                                   (Compiler_Languages.interm_resexn () () ()
                                      ()
                                      (Obj.magic
                                         (interm_importable_super () () ()
                                            (right dcs) d2))))));
                        safe_import =
                          (fun uu___2 ->
                             fun uu___1 ->
                               fun uu___ ->
                                 (fun f ->
                                    let f = Obj.magic f in
                                    fun eff_dcs ->
                                      let dcs' =
                                        EmptyNode ((left dcs), (right dcs)) in
                                      let eff_dcs' =
                                        EmptyNode
                                          ((left eff_dcs), (right eff_dcs)) in
                                      let f' =
                                        (Obj.magic
                                           (safe_importable_arrow () () ()
                                              dcs' () (Obj.magic d1) ()
                                              (Obj.magic d2))).safe_import
                                          (Obj.magic f) eff_dcs' in
                                      let uu___ = root eff_dcs in
                                      match uu___ with
                                      | Prims.Mkdtuple2 (dc_pck, eff_dc) ->
                                          Obj.magic
                                            (enforce_post_args () () () () ()
                                               (Obj.magic
                                                  (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                     dc_pck))
                                               (Obj.magic
                                                  (rityp_eff_dc () () () ()
                                                     () ()
                                                     (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                        dc_pck)
                                                     (Obj.magic eff_dc))) ()
                                               () f')) uu___2 uu___1 uu___)
                      }
let safe_importable_arrow_pre_post :
  't1 't2 'pre 'post .
    unit ->
      unit ->
        unit ->
          unit pck_dc tree ->
            unit ->
              unit ->
                ('t1, unit, Obj.t, unit, unit) exportable ->
                  ('t2, unit, Obj.t, unit, unit) importable ->
                    ('t1 ->
                       ('t2 CommonUtils.resexn, unit, unit, unit) MIO.dm_gmio,
                      unit, Obj.t, unit, unit) safe_importable
  =
  fun fl ->
    fun pi ->
      fun mst ->
        fun dcs ->
          fun c1post ->
            fun c2post ->
              fun d1 ->
                fun d2 ->
                  {
                    ityp1 = ();
                    c_ityp1 =
                      (Obj.magic
                         (Compiler_Languages.interm_arrow () () () ()
                            (Obj.magic
                               (interm_exportable_super () () () (left dcs)
                                  d1)) ()
                            (Obj.magic
                               (Compiler_Languages.interm_resexn () () () ()
                                  (Obj.magic
                                     (interm_importable_super () () ()
                                        (right dcs) d2))))));
                    safe_import =
                      (fun uu___2 ->
                         fun uu___1 ->
                           fun uu___ ->
                             (fun f ->
                                let f = Obj.magic f in
                                fun eff_dcs ->
                                  let dcs' =
                                    EmptyNode ((left dcs), (right dcs)) in
                                  let eff_dcs' =
                                    EmptyNode
                                      ((left eff_dcs), (right eff_dcs)) in
                                  let f' =
                                    (Obj.magic
                                       (safe_importable_arrow () () () dcs'
                                          () (Obj.magic d1) () (Obj.magic d2))).safe_import
                                      (Obj.magic f) eff_dcs' in
                                  let uu___ = root eff_dcs in
                                  match uu___ with
                                  | Prims.Mkdtuple2 (dc_pck, eff_dc) ->
                                      Obj.magic
                                        (enforce_post () () () () ()
                                           (Obj.magic
                                              (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                 dc_pck))
                                           (Obj.magic
                                              (rityp_eff_dc () () () () () ()
                                                 (FStar_Pervasives.__proj__Mkdtuple3__item___3
                                                    dc_pck)
                                                 (Obj.magic eff_dc))) () ()
                                           f')) uu___2 uu___1 uu___)
                  }
