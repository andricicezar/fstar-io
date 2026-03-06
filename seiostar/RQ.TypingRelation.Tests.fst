module RQ.TypingRelation.Tests

open FStar.Tactics.V1
open Trace
open QTypes.Sem
open QTypes.HelperTactics
open RQ.TypingRelation

#push-options "--no_smt"

open Examples

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
