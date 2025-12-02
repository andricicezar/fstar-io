module QExp

open FStar.Tactics
open QTyp

open IO

(** These helper functions are necessary to help F* do unification
    in such a way no VC is generated **)

unfold
val helper_var0 :
  g:typ_env ->
  a:qType ->
  fs_oval (extend a g) a
let helper_var0 g a fsG = hd fsG

unfold
val helper_varS : g:typ_env ->
                  a:qType ->
                  b:qType ->
                  fs_oval g a ->
                  fs_oval (extend b g) a
let helper_varS g a b x fsG = x (tail fsG)

unfold
val helper_unit : g:typ_env -> fs_oval g qUnit
let helper_unit g _ = ()

unfold
val helper_app: #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oval g (a ^-> b) ->
                x :fs_oval g a ->
                fs_oval g b
let helper_app f x fsG = (f fsG) (x fsG)

unfold
val helper_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_oval (extend a g) b ->
                fs_oval g (a ^-> b)
let helper_lambda #_ #_ body fsG x = body (stack fsG x)

unfold
val helper_true : g:typ_env -> fs_oval g qBool
let helper_true g _ = true

unfold
val helper_false : g:typ_env -> fs_oval g qBool
let helper_false g _ = false

unfold
val helper_if : #g :typ_env ->
                #a  : qType ->
                c   : fs_oval g qBool ->
                t   : fs_oval g a ->
                e   : fs_oval g a ->
                fs_oval g a
let helper_if c t e fsG =
  if c fsG then t fsG else e fsG

unfold
val helper_pair : #g : typ_env ->
                  #a : qType ->
                  #b : qType ->
                  x : fs_oval g a ->
                  y : fs_oval g b ->
                  fs_oval g (a ^* b)
let helper_pair #_ #_ #_ x y fsG =
  (x fsG, y fsG)

unfold
val helper_fst : #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 p : fs_oval g (a ^* b) ->
                 fs_oval g a
let helper_fst p fsG = fst (p fsG)

unfold
val helper_snd : #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 p : fs_oval g (a ^* b) ->
                 fs_oval g b
let helper_snd p fsG = snd (p fsG)

unfold
val helper_inl : #g : typ_env ->
                 #a : qType ->
                 b : qType ->
                 p : fs_oval g a ->
                 fs_oval g (a ^+ b)
let helper_inl _ p fsG = Inl (p fsG)

unfold
val helper_inr : #g : typ_env ->
                 a : qType ->
                 #b : qType ->
                 p : fs_oval g b ->
                 fs_oval g (a ^+ b)
let helper_inr _ p fsG = Inr (p fsG)

unfold
val helper_case : #g :typ_env ->
                  #a  : qType ->
                  #b  : qType ->
                  #c  : qType ->
                  cond: fs_oval g (a ^+ b) ->
                  inlc: fs_oval (extend a g) c ->
                  inrc: fs_oval (extend b g) c ->
                  fs_oval g c
let helper_case cond inlc inrc fsG =
  match cond fsG with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

unfold
val helper_app_prod :
                #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oval g (a ^->!@ b) ->
                x :fs_oval g a ->
                fs_oprod g b
let helper_app_prod f x fsG =
  (f fsG) (x fsG)

unfold
val helper_lambda_prod : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                body :fs_oprod (extend a g) b ->
                fs_oval g (a ^->!@ b)
let helper_lambda_prod #_ #_ body fsG x = body (stack fsG x)

unfold
val helper_if_prod : #g :typ_env ->
                #a  : qType ->
                c   : fs_oval g qBool ->
                t   : fs_oprod g a ->
                e   : fs_oprod g a ->
                fs_oprod g a
let helper_if_prod c t e fsG =
  if c fsG then t fsG else e fsG

unfold
val helper_case_prod : #g :typ_env ->
                #a  : qType ->
                #b : qType ->
                #c : qType ->
                cond : fs_oval g (a ^+ b) ->
                inlc : fs_oprod (extend a g) c ->
                inrc : fs_oprod (extend b g) c ->
                fs_oprod g c
let helper_case_prod cond inlc inrc fsG =
  match cond fsG with
  | Inl x -> inlc (stack fsG x)
  | Inr x -> inrc (stack fsG x)

unfold
val helper_bind_prod : #g:typ_env ->
                     #a:qType ->
                     #b:qType ->
                     m:fs_oprod g a ->
                     k:fs_oval g (a ^->!@ b) ->
                     fs_oprod g b
let helper_bind_prod m k fsG =
  io_bind (m fsG) (k fsG)

unfold
val helper_return_prod :
        #g:typ_env ->
        #a:qType ->
        x:fs_oval g a ->
        fs_oprod g a
let helper_return_prod x fsG = return (x fsG)

(** Fine-grained call by value **)
[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type oval_quotation : #a:qType -> g:typ_env -> fs_oval g a -> Type =
| Qtt         : #g : typ_env -> oval_quotation g (helper_unit g)

| QVar0       : #g : typ_env ->
                #a : qType ->
                oval_quotation (extend a g) (helper_var0 g a)

| QVarS       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #x : fs_oval g a ->
                oval_quotation g x ->
                oval_quotation (extend b g) (helper_varS g a b x)

| QAppGhost   : #g : typ_env ->
                #a : qType ->
                #f : fs_oval g (a ^-> qUnit) -> (** This has to be Tot. If it is GTot unit, F* can treat it as Pure unit **)
                #x : fs_oval g a ->
                oval_quotation #qUnit g (helper_app #_ #_ #_ f x)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^-> b) ->
                #x : fs_oval g a ->
                oval_quotation g f ->
                oval_quotation g x ->
                oval_quotation g (helper_app #_ #_ #_ f x)

| QLambda     : #a : qType ->
                #b : qType ->
                #g : typ_env ->
                #body : fs_oval (extend a g) b ->
                oval_quotation (extend a g) body ->
                oval_quotation #(a ^-> b) g (helper_lambda body)

| QTrue       : #g : typ_env -> oval_quotation g (helper_true g)
| QFalse      : #g : typ_env -> oval_quotation g (helper_false g)
| QIf         : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                oval_quotation g c ->
                #t : fs_oval g a ->
                oval_quotation g t ->
                #e : fs_oval g a ->
                oval_quotation g e ->
                oval_quotation g (helper_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #x : fs_oval g a ->
              #y : fs_oval g b ->
              oval_quotation g x ->
              oval_quotation g y ->
              oval_quotation g (helper_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              oval_quotation g p ->
              oval_quotation g (helper_fst p)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              oval_quotation g p ->
              oval_quotation g (helper_snd p)
| QInl      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g a ->
              oval_quotation g p ->
              oval_quotation g (helper_inl b p)
| QInr      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g b ->
              oval_quotation g p ->
              oval_quotation g (helper_inr a p)
| QCase     : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              oval_quotation g cond ->
              #inlc : fs_oval (extend a g) c ->
              oval_quotation _ inlc ->
              #inrc : fs_oval (extend b g) c ->
              oval_quotation _ inrc ->
              oval_quotation g (helper_case cond inlc inrc)
| QLambdaProd : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #body : fs_oprod (extend a g) b ->
                oprod_quotation (extend a g) body ->
                oval_quotation g (helper_lambda_prod body)
| QRead :
        #g:typ_env ->
        oval_quotation #(qUnit ^->!@ qBool) g (fun _ -> read)

| QWrite :
        #g:typ_env ->
        oval_quotation #(qBool ^->!@ qUnit) g (fun _ -> write)
and oprod_quotation : #a:qType -> g:typ_env -> fs_oprod g a -> Type =
(** Return and Bind of the monad **)
| QReturn :
        #g:typ_env ->
        #a:qType ->
        #x:fs_oval g a ->
        oval_quotation g x ->
        oprod_quotation #a g (helper_return_prod x)

| QBindProd :
        #g:typ_env ->
        #a:qType ->
        #b:qType ->
        #m:fs_oprod g a ->
        #k:fs_oval g (a ^->!@ b) ->
        oprod_quotation g m ->
        oval_quotation g k ->
        oprod_quotation #b g (helper_bind_prod m k)

| QAppProd    : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^->!@ b) ->
                #x : fs_oval g a ->
                oval_quotation g f ->
                oval_quotation g x ->
                oprod_quotation g (helper_app_prod f x)
| QIfProd     : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                oval_quotation #qBool g c ->
                #t : fs_oprod g a ->
                oprod_quotation g t ->
                #e : fs_oprod g a ->
                oprod_quotation g e ->
                oprod_quotation g (helper_if_prod c t e)
| QCaseProd : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              oval_quotation g cond ->
              #inlc : fs_oprod (extend a g) c ->
              oprod_quotation _ inlc ->
              #inrc : fs_oprod (extend b g) c ->
              oprod_quotation _ inrc ->
              oprod_quotation g (helper_case_prod cond inlc inrc)

let (⊢) (#a:qType) (g:typ_env) (x:fs_oval g a) =
  oval_quotation g x

unfold
let helper_oval (#a:qType) (x:fs_val a) : fs_oval empty a = fun _ -> x

unfold
let helper_oprod (#a:qType) (x:fs_prod a) : fs_oprod empty a = fun _ -> x

let (⊩) (a:qType) (x:fs_val a) =
  oval_quotation #a empty (helper_oval x)

type prod_quotation (a:qType) (x:fs_prod a) =
  oprod_quotation #a empty (helper_oprod x)


(** Because of the fancy types, now one needs a preprocessing tactic to
    get rid of the qTypes **)

let l_to_r_fsG () : Tac unit =
   l_to_r [`lem_hd_stack; `tail_stack_inverse]

let simplify_qType (x:term) : Tac term =
  (** TODO: why is F* not doing this automatically anyway? **)
  norm_term_env (top_env ()) [
    delta_only [`%fs_oval; `%qUnit; `%qBool; `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Plus; `%get_rel; `%get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2];
    iota;
    simplify
  ] x

open Examples

#push-options "--no_smt"

let test_ut_unit
  : qUnit ⊩ ut_unit
  = Qtt

let test_ut_true
  : qBool ⊩ ut_true
  = QTrue

let test_ut_false
  : qBool ⊩ ut_false
  = QFalse

val var0 : fs_oval (extend qBool empty) qBool
let var0 fsG = hd fsG

val var1 : fs_oval (extend qBool (extend qBool empty)) qBool
let var1 fsG = hd (tail fsG)

let var2 : fs_oval (extend qBool (extend qBool (extend qBool empty))) qBool =
  fun fsG -> hd (tail (tail fsG))

let test_var0
  : (extend qBool empty) ⊢ var0
  = QVar0

let qVar1 #g #a #b : (extend b (extend a g)) ⊢ (fun fsG -> hd (tail fsG)) =
  QVarS QVar0

let qVar2 #g #a #b #c : (extend c (extend b (extend a g))) ⊢ (fun fsG -> hd (tail (tail fsG))) =
  QVarS qVar1

let test_var1
  : (extend qBool (extend qBool empty)) ⊢ var1
  = qVar1

let test_var2
  : (extend qBool (extend qBool (extend qBool empty))) ⊢ var2
  = qVar2

let test_constant
  : ((qBool ^-> qBool) ⊩ constant)
  = QLambda QTrue

let test_constant' (** TODO: why is this accepted. is it a problem? **)
  : ((qBool ^-> qBool) ⊩ constant)
  = QLambda (QVarS QTrue)

let test_identity
  : (qBool ^-> qBool) ⊩ identity
  = QLambda QVar0

let test_thunked_id
  : (qBool ^-> (qBool ^-> qBool)) ⊩ thunked_id
  = QLambda (QLambda QVar0)

let test_proj1
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj1
  = QLambda (QLambda (QLambda qVar2))

let test_proj2
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj2
  = QLambda (QLambda (QLambda qVar1))

let test_proj3
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj3
  = QLambda (QLambda (QLambda QVar0))

let test_apply_top_level_def
  : (qBool ^-> qBool) ⊩ apply_top_level_def
  = QLambda (QApp
              (QApp
                (QLambda (QLambda QVar0))
                QVar0)
              QTrue)

let test_apply_top_level_def'
  : (qBool ^-> qBool ^-> qBool) ⊩ apply_top_level_def'
  = QLambda (QLambda (QApp
                       (QApp
                          (QLambda (QLambda QVar0))
                          qVar1)
                       QVar0))

let test_papply__top_level_def
  : (qBool ^-> qBool ^-> qBool) ⊩ papply__top_level_def
  = QLambda (QApp
              (QLambda (QLambda QVar0))
              QVar0)

let test_apply_arg
  : ((qUnit ^-> qUnit) ^-> qUnit) ⊩ apply_arg
  = QLambda (QApp QVar0 Qtt)

let test_apply_arg2 ()
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool) ⊩ apply_arg2
  by (l_to_r_fsG (); trefl ())
  = QLambda (QApp (QApp QVar0 QTrue) QFalse)


[@expect_failure]
let test_proj2'
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj2
  = QLambda (QLambda (QLambda QVar0))

let test_anif
  : qBool ⊩ anif
  = QIf QTrue QFalse QTrue

let test_negb
  : (qBool ^-> qBool) ⊩ negb
  = QLambda (QIf QVar0 QFalse QTrue)

let test_negb_pred
  : ((qBool ^-> qBool) ^-> qBool ^-> qBool) ⊩ negb_pred
  = QLambda (QLambda (QIf (QApp qVar1 QVar0) QFalse QTrue))

let test_if2 ()
  : (qBool ^-> qBool ^-> qBool) ⊩ if2
  by (l_to_r_fsG (); trefl ())
  = QLambda (QLambda (QIf qVar1 QFalse QVar0))

let test_callback_return ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return
  by (l_to_r_fsG (); trefl ())
  = QLambda (QIf QVar0
                 (QLambda qVar1)
                 (QLambda QVar0))

let test_callback_return' ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return'
  by (l_to_r_fsG (); trefl ())
  = QLambda (QIf QVar0
                 (QLambda qVar1)
                 (QLambda QVar0)) // TODO: why does it not work to unfold identity here?

let test_make_pair
  : (qBool ^-> qBool ^-> (qBool ^* qBool)) ⊩ make_pair
  = QLambda (QLambda (QMkpair qVar1 QVar0))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions ()
  : Tot (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
                            ⊩ pair_of_functions)
  by (l_to_r_fsG (); trefl ())
  =  QMkpair
      (QLambda (QApp
                  (QLambda (QIf QVar0 QFalse QTrue))
                  QVar0))
      (QLambda (QLambda QVar0))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions2 ()
  : (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
    ⊩ pair_of_functions2)
  by (l_to_r_fsG (); trefl ())
  = QMkpair
      (QLambda (QIf QVar0 QFalse QTrue))
      (QLambda (QLambda (QIf qVar1 QFalse QVar0)))

let test_fst_pair
  : (qBool) ⊩ fst_pair
  = (QFst (QMkpair QTrue Qtt))

let test_wrap_fst
  : ((qBool ^* qBool) ^-> qBool) ⊩ wrap_fst
  = QLambda (QFst QVar0)

let test_wrap_fst_pa
  : ((qBool ^* qBool) ^-> qBool) ⊩ wrap_fst_pa
  = QLambda (QFst QVar0)

let test_snd_pair
  : (qUnit) ⊩ snd_pair
  = (QSnd (QMkpair QTrue Qtt))

let test_wrap_snd
  : ((qBool ^* qUnit) ^-> qUnit) ⊩ wrap_snd
  = QLambda (QSnd QVar0)

let test_wrap_snd_pa
  : ((qBool ^* qUnit) ^-> qUnit) ⊩ wrap_snd_pa
  = QLambda (QSnd QVar0)

let qLet #g (#a #b:qType) (#x:fs_oval g a) (#f:fs_oval (extend a g) b)
  (qx : oval_quotation g x) (qf : oval_quotation _ f) :
  oval_quotation g (fun fsG -> let y = x fsG in f (stack fsG y)) =
  QApp (QLambda qf) qx

let test_a_few_lets
  : (qBool ^-> qUnit) ⊩ a_few_lets
  = QLambda
     (qLet (QMkpair QVar0 QVar0)
     (qLet qVar1
     (qLet (QFst qVar1)
     (qLet (QMkpair qVar1 QVar0)
     Qtt))))

let test_inl_true
  : (qBool ^+ qUnit) ⊩ inl_true
  = QInl QTrue

let test_inr_unit
  : (qBool ^+ qUnit) ⊩ inr_unit
  = QInr Qtt

let test_return_either ()
  : (qBool ^-> (qUnit ^+ qUnit)) ⊩ return_either
  by (l_to_r_fsG (); trefl ())
  = QLambda (QIf QVar0 (QInl Qtt) (QInr Qtt))

let test_match_either ()
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either
  by (l_to_r_fsG (); trefl ())
  = QLambda (QCase QVar0 QVar0 QVar0)

[@expect_failure]
let test_match_either' ()
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either'
  by (l_to_r_fsG (); trefl ())
  = QLambda (QCase QVar0 QVar0 QVar0)

let test_match_either_arg ()
  : (((qBool ^+ qBool) ^-> qBool ^-> qBool) ⊩ match_either_arg)
  by (l_to_r_fsG (); trefl ())
  = QLambda (QLambda (
       QCase
         qVar1
         QVar0
         qVar1))

open ExamplesIO

let test_u_return
  : prod_quotation _ u_return
  = QReturn QTrue

let test_apply_io_return
  : (qBool ^->!@ qBool) ⊩ apply_io_return
  = QLambdaProd (QReturn QVar0)

let test_apply_read
  : prod_quotation _ apply_read
  = QAppProd QRead Qtt

let test_apply_write_const
  : prod_quotation _ apply_write_const
  = QAppProd QWrite QTrue

let test_apply_write
  : _ ⊩  apply_write
  = QLambdaProd (QAppProd QWrite QVar0)

let test_apply_io_bind_const
  : prod_quotation _ apply_io_bind_const
  = QBindProd
      (QReturn QTrue)
      (QLambdaProd (QReturn QVar0))

let test_apply_io_bind_identity
  : (qBool ^->!@ qBool) ⊩ apply_io_bind_identity
  = QLambdaProd
      (QBindProd
        (QReturn QVar0)
        (QLambdaProd (QReturn QVar0)))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_pure_if ()
  : Tot ((qBool ^->!@ qBool) ⊩ apply_io_bind_pure_if)
  by (l_to_r_fsG (); trefl ())
  = QLambdaProd
      (QBindProd
        (QReturn QVar0)
        (QLambdaProd
          (QIfProd QVar0
            (QReturn QFalse)
            (QReturn QTrue))))

let test_apply_io_bind_write
  : _ ⊩ apply_io_bind_write
  = QLambdaProd (
      QBindProd
         (QReturn QVar0)
         (QLambdaProd
           (QAppProd QWrite QVar0)))

let test_apply_io_bind_read_write
  : prod_quotation _ apply_io_bind_read_write
  = QBindProd
     (QAppProd QRead Qtt)
     (QLambdaProd
       (QAppProd QWrite QVar0))

let test_apply_io_bind_read_write'
  : prod_quotation _ apply_io_bind_read_write'
  = QBindProd (QAppProd QRead Qtt) QWrite

let test_apply_io_bind_read_if_write
  : prod_quotation _ apply_io_bind_read_if_write
  = QBindProd
      (QAppProd QRead Qtt)
      (QLambdaProd
        (QIfProd QVar0
          (QAppProd QWrite QFalse)
          (QAppProd QWrite QTrue)))

let qLetProd #g (#a #b:qType) (#x:fs_oval g a) (#f:fs_oprod (extend a g) b)
  (qx : oval_quotation g x) (qf : oprod_quotation _ f) :
  oprod_quotation g (fun fsG -> let y = x fsG in f (stack fsG y)) =
  QAppProd (QLambdaProd qf) qx

let test_sendError400 ()
  : _ ⊩ sendError400
  = QLambdaProd
      (qLetProd (QApp (QLambda QVar0) QTrue) (
      (qLetProd (QMkpair (QVarS QVar0) QVar0) (
      (QBindProd
        (QAppProd QWrite (QVarS (QVarS QVar0)))
        (QLambdaProd (QReturn Qtt)))))))
