module RQ.TypingRelation

open FStar.Tactics
open QTyp

open IOStar

(** Fine-grained call by value **)
[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type typing : #a:qType -> g:typ_env -> fs_oval g a -> Type =
| Qtt         : #g : typ_env -> typing g (fs_oval_return g qUnit ())
| QFd         : #g : typ_env -> fd:file_descr -> typing g (fs_oval_return g qFileDescr fd)

| QVar0       : #g : typ_env ->
                #a : qType ->
                typing (extend a g) (fs_oval_var0 g a)

| QVarS       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #x : fs_oval g a ->
                typing g x ->
                typing (extend b g) (fs_oval_varS b x)

| QAppGhost   : #g : typ_env ->
                #a : qType ->
                #f : fs_oval g (a ^-> qUnit) -> (** This has to be Tot. If it is GTot unit, F* can treat it as Pure unit **)
                #x : fs_oval g a ->
                typing #qUnit g (fs_oval_app #_ #_ #_ f x)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^-> b) ->
                #x : fs_oval g a ->
                typing g f ->
                typing g x ->
                typing g (fs_oval_app #_ #_ #_ f x)

| QLambda     : #a : qType ->
                #b : qType ->
                #g : typ_env ->
                #body : fs_oval (extend a g) b ->
                typing (extend a g) body ->
                typing #(a ^-> b) g (fs_oval_lambda body)

| QTrue       : #g : typ_env -> typing g (fs_oval_return g qBool true)
| QFalse      : #g : typ_env -> typing g (fs_oval_return g qBool false)
| QStringLit  : #g : typ_env -> s:string -> typing g (fs_oval_return g qString s)
| QStringEq   : #g : typ_env ->
                #s1 : fs_oval g qString ->
                typing g s1 ->
                #s2 : fs_oval g qString ->
                typing g s2 ->
                typing g (fs_oval_eq_string s1 s2)
| QIf         : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                typing g c ->
                #t : fs_oval g a ->
                typing g t ->
                #e : fs_oval g a ->
                typing g e ->
                typing g (fs_oval_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #x : fs_oval g a ->
              #y : fs_oval g b ->
              typing g x ->
              typing g y ->
              typing g (fs_oval_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              typing g p ->
              typing g (fs_oval_fmap p fst)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              typing g p ->
              typing g (fs_oval_fmap p snd)
| QInl      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g a ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inl)
| QInr      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g b ->
              typing g p ->
              typing #(a ^+ b) g (fs_oval_fmap p Inr)
| QCase     : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              typing g cond ->
              #inlc : fs_oval (extend a g) c ->
              typing _ inlc ->
              #inrc : fs_oval (extend b g) c ->
              typing _ inrc ->
              typing g (fs_oval_case cond inlc inrc)
| QLambdaProd : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #body : fs_oprod (extend a g) b ->
                typing_io (extend a g) body ->
                typing g (fs_oval_lambda_oprod body)
and typing_io : #a:qType -> g:typ_env -> fs_oprod g a -> Type =
| QCall :
        #g:typ_env ->
        o:io_ops ->
        #args:fs_oval g (q_io_args o) ->
        typing g args ->
        typing_io #(q_io_res o) g (fs_oprod_call_oval o args)

| QReturn :
        #g:typ_env ->
        #a:qType ->
        #x:fs_oval g a ->
        typing g x ->
        typing_io #a g (fs_oprod_return x)

| QBindProd :
        #g:typ_env ->
        #a:qType ->
        #b:qType ->
        #m:fs_oprod g a ->
        #k:fs_oprod (extend a g) b ->
        typing_io g m ->
        typing_io (extend a g) k ->
        typing_io #b g (fs_oprod_bind m k)

| QAppProd    : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^->!@ b) ->
                #x : fs_oval g a ->
                typing g f ->
                typing g x ->
                typing_io g (fs_oprod_app_oval_oval f x)
| QIfProd     : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                typing #qBool g c ->
                #t : fs_oprod g a ->
                typing_io g t ->
                #e : fs_oprod g a ->
                typing_io g e ->
                typing_io g (fs_oprod_if_oval c t e)
| QCaseProd : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              typing g cond ->
              #inlc : fs_oprod (extend a g) c ->
              typing_io _ inlc ->
              #inrc : fs_oprod (extend b g) c ->
              typing_io _ inrc ->
              typing_io g (fs_oprod_case_oval cond inlc inrc)

let (⊢) (#a:qType) (g:typ_env) (x:fs_oval g a) =
  typing g x

unfold
let helper_oval (#a:qType) (x:fs_val a) : fs_oval empty a = fun _ -> x

unfold
let helper_oval_g (#a:qType) (#g:typ_env) (x:fs_val a) : fs_oval g a = fun _ -> x

unfold
let helper_oprod (#a:qType) (x:fs_prod a) : fs_oprod empty a = fun _ -> x

let (⊩) (a:qType) (x:fs_val a) =
  typing #a empty (helper_oval x)

type prod_quotation (a:qType) (x:fs_prod a) =
  typing_io #a empty (helper_oprod x)


(** Because of the fancy types, now one needs a preprocessing tactic to
    get rid of the qTypes **)

let l_to_r_fsG () : Tac unit =
   l_to_r [`lem_hd_stack; `tail_stack_inverse]

let simplify_qType_g g (x:term) : Tac term =
  (** TODO: why is F* not doing this automatically anyway? **)
  norm_term_env g [
    delta_only [
      `%fs_oval; `%fs_val; `%qUnit; `%qBool; `%qString; `%qResexn;
      `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Plus;
      `%op_Hat_Subtraction_Greater_Bang_At;
      `%get_rel; `%get_Type;
      `%q_io_args; `%q_io_res;
      `%Mkdtuple2?._1;`%Mkdtuple2?._2];
    zeta;
    iota;
    simplify
  ] x

let simplify_qType  (x:term) : Tac term = simplify_qType_g (top_env ()) x

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

let test_constant'
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

let test_papply_arg2 ()
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool ^-> qBool) ⊩ papply_arg2
  by (l_to_r_fsG (); trefl ())
  = QLambda (QApp QVar0 QTrue)

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
  (qx : typing g x) (qf : typing _ f) :
  typing g (fun fsG -> let y = x fsG in f (stack fsG y)) =
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
  : (qUnit ^->!@ qBool) ⊩ u_return
  = QLambdaProd (QReturn QTrue)

let test_apply_io_return
  : (qBool ^->!@ qBool) ⊩ apply_io_return
  = QLambdaProd (QReturn QVar0)

let test_apply_read
  : (qUnit ^->!@ (qResexn qString)) ⊩ apply_read
  = QLambdaProd (QCall ORead (QFd 0))

let test_apply_write_const
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_write_const
  = QLambdaProd (QCall OWrite (QMkpair (QFd 2) (QStringLit "hello")))

let test_apply_write
  : _ ⊩  apply_write
  = QLambdaProd (QCall OWrite (QMkpair (QFd 1) QVar0))

let test_apply_io_bind_const
  : (qUnit ^->!@ qBool) ⊩ apply_io_bind_const
  = QLambdaProd (
      QBindProd
        (QReturn QTrue)
        (QReturn QVar0))

let test_apply_io_bind_identity
  : (qBool ^->!@ qBool) ⊩ apply_io_bind_identity
  = QLambdaProd
      (QBindProd
        (QReturn QVar0)
        (QReturn QVar0))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_pure_if ()
  : Tot ((qBool ^->!@ qBool) ⊩ apply_io_bind_pure_if)
  by (l_to_r_fsG (); trefl ())
  = QLambdaProd
      (QBindProd
        (QReturn QVar0)
        (QIfProd QVar0
           (QReturn QFalse)
           (QReturn QTrue)))

let test_apply_io_bind_write
  : _ ⊩ apply_io_bind_write
  = QLambdaProd (
      QBindProd
         (QReturn QVar0)
         (QCall OWrite (QMkpair (QFd 2) QVar0)))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_write ()
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_write
  by (l_to_r_fsG (); trefl ())
  = QLambdaProd (QBindProd (QCall ORead (QFd 4))
    (QCaseProd #_ #qString #qUnit QVar0
     (QCall OWrite (QMkpair (QFd 1) (QStringLit "data")))
     (QReturn (QInr QVar0))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_write' ()
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_write'
  by (l_to_r_fsG (); trefl ())
  = QLambdaProd (QBindProd (QCall ORead (QFd 9)) (
      QCaseProd #_ #qString #qUnit QVar0 (QCall OWrite (QMkpair (QFd 2) (QStringLit "data"))) (QReturn (QInr QVar0))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_if_write ()
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_if_write
  by (l_to_r_fsG (); trefl ())
  = QLambdaProd
      (QBindProd
        (QCall ORead (QFd 0))
        (QCaseProd #_ #qString #qUnit QVar0
          (QCall OWrite (QMkpair (QFd 7) (QStringLit "data")))
          (QReturn (QInr QVar0))))

let qLetProd #g (#a #b:qType) (#x:fs_oval g a) (#f:fs_oprod (extend a g) b)
  (qx : typing g x) (qf : typing_io _ f) :
  typing_io g (fun fsG -> let y = x fsG in f (stack fsG y)) =
  QAppProd (QLambdaProd qf) qx

let test_sendError400 ()
  : (qBool ^->!@ qUnit) ⊩ sendError400
  = QLambdaProd
      (QBindProd
        (QCall OWrite (QMkpair (QFd 9) (QStringLit "error400")))
        (QReturn Qtt))

let test_const_str
  : qString ⊩ const_str
  = QStringLit "constant"

let test_greeting
  : (qBool ^-> qString) ⊩ greeting
  = QLambda (QIf QVar0 (QStringLit "hello") (QStringLit "goodbye"))

#pop-options
