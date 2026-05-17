module RQ.TypingRelation.Tests

open FStar.Tactics.V1
open Trace
open RQ.TypingRelation
open QTypes.HelperTactics

let simplify_via_norm () : Tac unit =
  let _ = repeat forall_intro in
  or_else trivial trefl

let simplify_d () : Tac unit = norm [delta_only qType_defs_list; iota]

val var0 : fs_oval (extend qBool empty) qBool spec_env_axiom
let var0 fsG = hd fsG

// val var1 : fs_oval (extend qBool (extend qBool empty)) qBool
//   (spec_env_bind (spec_env_weaken) (spec_env_axiom))
// let var1 fsG = hd (tail fsG)

// let var2 : fs_oval (extend qBool (extend qBool (extend qBool empty))) qBool =
//   fun fsG -> hd (tail (tail fsG))

let test_var0
  : (extend qBool empty) ⊢ var0
  = QAxiom

let qVar1 #g #a #b : (extend b (extend a g)) ⊢ (fun fsG -> hd (tail fsG)) =
  QWeaken QAxiom

let qVar2 #g #a #b #c : (extend c (extend b (extend a g))) ⊢ (fun fsG -> hd (tail (tail fsG))) =
  QWeaken qVar1

// let test_var1
//   : (extend qBool (extend qBool empty)) ⊢ var1
//   = qVar1

// let test_var2
//   : (extend qBool (extend qBool (extend qBool empty))) ⊢ var2
//   = qVar2

#push-options "--no_smt"

open Examples

let test_ut_unit ()
  : qUnit ⊩ ut_unit
  by (simplify_via_norm ())
  = pack_turnstile Qtt

let test_ut_true ()
  : qBool ⊩ ut_true
  by (simplify_via_norm ())
  = pack_turnstile QTrue

let test_ut_false ()
  : qBool ⊩ ut_false
  by (simplify_via_norm ())
  = pack_turnstile QFalse

let test_constant ()
  : ((qBool ^-> qBool) ⊩ constant)
  by (simplify_via_norm ())
  = pack_turnstile (QLambda QTrue)

let test_constant' ()
  : ((qBool ^-> qBool) ⊩ constant)
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QWeaken QTrue))

let test_identity ()
  : (qBool ^-> qBool) ⊩ identity
  by (simplify_via_norm ())
  = pack_turnstile (QLambda QAxiom)

let test_thunked_id ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ thunked_id
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda QAxiom))

let test_proj1 ()
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj1
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QLambda qVar2)))

let test_proj2 ()
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj2
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QLambda qVar1)))

let test_proj3 ()
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj3
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QLambda QAxiom)))

let test_apply_top_level_def ()
  : (qBool ^-> qBool) ⊩ apply_top_level_def
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QApp
              (QApp
                (QLambda (QLambda QAxiom))
                QAxiom)
              QTrue))

let test_apply_top_level_def' ()
  : (qBool ^-> qBool ^-> qBool) ⊩ apply_top_level_def'
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QApp
                       (QApp
                          (QLambda (QLambda QAxiom))
                          qVar1)
                       QAxiom)))

let test_papply__top_level_def ()
  : (qBool ^-> qBool ^-> qBool) ⊩ papply__top_level_def
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QApp
              (QLambda (QLambda QAxiom))
              QAxiom))

let test_apply_arg ()
  : ((qUnit ^-> qUnit) ^-> qUnit) ⊩ apply_arg
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QApp QAxiom Qtt))

let test_apply_arg2 ()
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool) ⊩ apply_arg2
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QApp (QApp QAxiom QTrue) QFalse))

let test_papply_arg2 ()
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool ^-> qBool) ⊩ papply_arg2
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QApp QAxiom QTrue))

[@expect_failure]
let test_proj2'
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj2
  = pack_turnstile (QLambda (QLambda (QLambda QAxiom)))

let test_anif ()
  : qBool ⊩ anif
  by (simplify_via_norm ())
  = pack_turnstile (QIf QTrue QFalse QTrue)

let test_negb ()
  : (qBool ^-> qBool) ⊩ negb
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QIf QAxiom QFalse QTrue))

let test_negb_pred ()
  : ((qBool ^-> qBool) ^-> qBool ^-> qBool) ⊩ negb_pred
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QIf (QApp qVar1 QAxiom) QFalse QTrue)))

let test_if2 ()
  : (qBool ^-> qBool ^-> qBool) ⊩ if2
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QIf qVar1 QFalse QAxiom)))

let test_callback_return ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QIf QAxiom
                 (QLambda qVar1)
                 (QLambda QAxiom)))

let test_callback_return' ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return'
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QIf QAxiom
                 (QLambda qVar1)
                 (QLambda QAxiom)))

let test_make_pair ()
  : (qBool ^-> qBool ^-> (qBool ^* qBool)) ⊩ make_pair
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QMkpair qVar1 QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions ()
  : Tot (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
                            ⊩ pair_of_functions)
  by (simplify_via_norm ())
  = pack_turnstile (QMkpair
      (QLambda (QApp
                  (QLambda (QIf QAxiom QFalse QTrue))
                  QAxiom))
      (QLambda (QLambda QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions2 ()
  : (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
    ⊩ pair_of_functions2)
  by (simplify_via_norm ())
  = pack_turnstile (QMkpair
      (QLambda (QIf QAxiom QFalse QTrue))
      (QLambda (QLambda (QIf qVar1 QFalse QAxiom))))

let test_fst_pair ()
  : (qBool) ⊩ fst_pair
  by (simplify_via_norm ())
  = pack_turnstile (QFst (QMkpair QTrue Qtt))

let test_wrap_fst ()
  : ((qBool ^* qBool) ^-> qBool) ⊩ wrap_fst
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QFst QAxiom))

let test_wrap_fst_pa ()
  : ((qBool ^* qBool) ^-> qBool) ⊩ wrap_fst_pa
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QFst QAxiom))

let test_snd_pair ()
  : (qUnit) ⊩ snd_pair
  by (simplify_via_norm ())
  = pack_turnstile (QSnd (QMkpair QTrue Qtt))

let test_wrap_snd ()
  : ((qBool ^* qUnit) ^-> qUnit) ⊩ wrap_snd
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QSnd QAxiom))

let test_wrap_snd_pa ()
  : ((qBool ^* qUnit) ^-> qUnit) ⊩ wrap_snd_pa
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QSnd QAxiom))

let qLet #g (#a #b:qType) #wpx #wpf (#x:fs_oval g a wpx) (#f:fs_oval (extend a g) b wpf)
  (qx : typing g x) (qf : typing _ f)
  : typing g (fs_oval_app (fs_oval_lambda f) x)
  = QApp (QLambda qf) qx

let three_lets : bool -> unit =
  fun x -> let p = (x, x) in let _y = x in let _z = fst p in ()

 let test_three_lets ()
   : (qBool ^-> qUnit) ⊩ three_lets
   by (simplify_via_norm ())
   = pack_turnstile (QLambda
      (qLet (QMkpair QAxiom QAxiom)
      (qLet (QWeaken QAxiom)
      (qLet (QFst qVar1)
      Qtt))))

let test_inl_true ()
  : (qBool ^+ qUnit) ⊩ inl_true
   by (simplify_via_norm ())
  = pack_turnstile (QInl QTrue)

let test_inr_unit ()
  : (qBool ^+ qUnit) ⊩ inr_unit
   by (simplify_via_norm ())
  = pack_turnstile (QInr Qtt)

[@@ (preprocess_with simplify_qType)]
let test_return_either ()
  : (qBool ^-> (qUnit ^+ qUnit)) ⊩ return_either
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QIf QAxiom (QInl Qtt) (QInr Qtt)))

[@@ (preprocess_with simplify_qType)]
let test_match_either ()
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QCase QAxiom QAxiom QAxiom))

[@expect_failure]
let test_match_either'
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either'
  = pack_turnstile (QLambda (QCase QAxiom QAxiom QAxiom))

[@@ (preprocess_with simplify_qType)]
let test_match_either_arg ()
  : (((qBool ^+ qBool) ^-> qBool ^-> qBool) ⊩ match_either_arg)
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (
       QCase
         qVar1
         QAxiom
         qVar1)))
#pop-options

let d_test_constant () : _ ⊫ _ =
  mk_turniqet (test_constant ()) ()
let d_test_constant' () : _ ⊫ _ =
  mk_turniqet (test_constant' ()) ()
let d_test_identity () : _ ⊫ _ =
  mk_turniqet (test_identity ()) ()
let d_test_thunked_id () : _ ⊫ _ =
  mk_turniqet (test_thunked_id ()) ()
let d_test_proj1 () : _ ⊫ _ =
  mk_turniqet (test_proj1 ()) ()
let d_test_proj2 () : _ ⊫ _ =
  mk_turniqet (test_proj2 ()) ()
let d_test_proj3 () : _ ⊫ _ =
  mk_turniqet (test_proj3 ()) ()
let d_test_apply_top_level_def () : _ ⊫ _ =
  mk_turniqet (test_apply_top_level_def ()) ()
let d_test_apply_top_level_def' () : _ ⊫ _ =
  mk_turniqet (test_apply_top_level_def' ()) ()
let d_test_papply__top_level_def () : _ ⊫ _ =
  mk_turniqet (test_papply__top_level_def ()) ()
let d_test_apply_arg () : _ ⊫ _ =
  mk_turniqet (test_apply_arg ()) ()
let d_test_apply_arg2 () : _ ⊫ _ =
  mk_turniqet (test_apply_arg2 ()) ()
let d_test_papply_arg2 () : _ ⊫ _ =
  mk_turniqet (test_papply_arg2 ()) ()
let d_test_anif () : _ ⊫ _ =
  mk_turniqet (test_anif ()) ()
let d_test_negb () : _ ⊫ _ =
  mk_turniqet (test_negb ()) ()
let d_test_negb_pred () : _ ⊫ _ =
  mk_turniqet (test_negb_pred ()) ()
let d_test_if2 () : _ ⊫ _ =
  mk_turniqet (test_if2 ()) ()
let d_test_callback_return () : _ ⊫ _ =
  mk_turniqet (test_callback_return ()) ()
let d_test_callback_return' () : _ ⊫ _ =
  mk_turniqet (test_callback_return' ()) ()

#push-options "--no_smt"
open ExamplesIO

let test_u_return ()
  : (qUnit ^->!@ qBool) ⊩ u_return
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn QTrue))

let test_apply_io_return ()
  : (qBool ^->!@ qBool) ⊩ apply_io_return
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn QAxiom))

[@@ (preprocess_with simplify_qType)]
let test_apply_read ()
  : (qFileDescr ^->!@ (qResexn qString)) ⊩ apply_read
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QCall ORead QAxiom))

let test_apply_write_const ()
  : (qFileDescr ^->!@ (qResexn qUnit)) ⊩ apply_write_const
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QCall OWrite (QMkpair QAxiom (QStringLit "hello"))))

let test_apply_write ()
  : (qFileDescr ^-> qString ^->!@ (qResexn qUnit)) ⊩ apply_write
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambdaIO (QCall OWrite (QMkpair (QWeaken QAxiom) QAxiom))))

let test_apply_io_bind_const ()
  : (qUnit ^->!@ qBool) ⊩ apply_io_bind_const

  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
      QBind
        (QReturn QTrue)
        (QReturn QAxiom)))

let test_apply_io_bind_identity ()
  : (qBool ^->!@ qBool) ⊩ apply_io_bind_identity
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO
      (QBind
        (QReturn QAxiom)
        (QReturn QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_pure_if ()
  : Tot ((qBool ^->!@ qBool) ⊩ apply_io_bind_pure_if)
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO
      (QBind
        (QReturn QAxiom)
        (QIfIO QAxiom
           (QReturn QFalse)
           (QReturn QTrue))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_write ()
  : (qFileDescr ^-> qString ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_write
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambdaIO (
      QBind
         (QReturn QAxiom)
         (QCall OWrite (QMkpair (QWeaken (QWeaken QAxiom)) QAxiom)))))

#set-options "--print_implicits"

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_write ()
  : (qFileDescr ^-> qFileDescr ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_write
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambdaIO (QBind (QCall ORead (QWeaken QAxiom))
    (QCaseIO QAxiom
      (QCall OWrite (QMkpair (QWeaken (QWeaken QAxiom)) (QStringLit "data")))
      (QReturn (QInr QAxiom))))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_write' ()
   : (qFileDescr ^-> qFileDescr ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_write'
   by (simplify_via_norm ())
   = pack_turnstile (QLambda (QLambdaIO (
       QBind (QCall ORead (QWeaken QAxiom))
         (QCaseIO QAxiom
           (QCall OWrite (QMkpair (QWeaken (QWeaken QAxiom)) (QStringLit "data")))
           (QReturn (QInr QAxiom))))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_if_write ()
  : (qFileDescr ^-> qFileDescr ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_if_write
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambdaIO
      (QBind
        (QCall ORead (QWeaken QAxiom))
         (QCaseIO QAxiom
           (QCall OWrite (QMkpair (QWeaken (QWeaken QAxiom)) (QStringLit "data")))
           (QReturn (QInr QAxiom))))))

let test_sendError400 ()
  : (qFileDescr ^->!@ qUnit) ⊩ sendError400
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO
      (QBind
        (QCall OWrite (QMkpair QAxiom (QStringLit "error400")))
        (QReturn Qtt)))

let test_const_str ()
  : qString ⊩ const_str
  by (simplify_via_norm ())
  = pack_turnstile (QStringLit "constant")

let test_greeting ()
  : (qBool ^-> qString) ⊩ greeting
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QIf QAxiom (QStringLit "hello") (QStringLit "goodbye")))

let test_nat_zero ()
  : qNat ⊩ nat_zero
  by (simplify_via_norm ())
  = pack_turnstile (QZero)

let test_nat_one ()
  : qNat ⊩ nat_one
  by (simplify_via_norm ())
  = pack_turnstile (QSucc QZero)

let test_nat_two ()
  : qNat ⊩ nat_two
  by (simplify_via_norm ())
  = pack_turnstile (QSucc (QSucc QZero))

let test_nat_succ_fn ()
  : (qNat ^-> qNat) ⊩ nat_succ_fn
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QSucc QAxiom))

let test_nat_nrec_base ()
  : qNat ⊩ nat_two
  by (simplify_via_norm ())
  = pack_turnstile (QNRec QZero (QSucc (QSucc QZero)) (QLambda (QSucc QAxiom)))

let test_nat_add2 ()
  : (qNat ^-> qNat) ⊩ nat_add2
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QNRec (QSucc (QSucc QZero)) QAxiom (QLambda (QSucc QAxiom))))

let test_nat_nrec_two_plus_three1 ()
  : qNat ⊩ nat_five1
  by (simplify_via_norm ())
  = pack_turnstile (QNRec (QSucc (QSucc (QSucc QZero))) (QSucc (QSucc QZero)) (QLambda (QSucc QAxiom)))

let test_nat_nrec_two_plus_three2 ()
  : qNat ⊩ nat_five2
  by (simplify_via_norm ())
  = pack_turnstile (QNRec (QSucc (QSucc (QSucc QZero))) (QSucc (QSucc QZero)) (QLambda (QSucc QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_nat_fact_five ()
  : qNat ⊩ fact_five
  by (simplify_via_norm ())
  = pack_turnstile (QSnd (
      QNRec
        (QSucc (QSucc (QSucc (QSucc (QSucc QZero)))))
        (QMkpair QZero (QSucc QZero))
        (QLambda
          (QMkpair
            (QSucc (QFst QAxiom))
            (QNRec
              (QSucc (QFst QAxiom))
              QZero
              (QLambda
                (QNRec
                  (QSnd (QWeaken QAxiom))
                  QAxiom
                  (QLambda (QSucc QAxiom)))))))))

#pop-options

let d_test_u_return () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_u_return ()) ()
let d_test_apply_io_return () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_return ()) ()
let d_test_apply_read () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_read ()) ()
let d_test_apply_write_const () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_write_const ()) ()
let d_test_apply_write () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_write ()) ()
let d_test_apply_io_bind_const () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_const ()) ()
let d_test_apply_io_bind_identity () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_identity ()) ()
let d_test_apply_io_bind_pure_if () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_pure_if ()) ()
let d_test_apply_io_bind_write () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_write ()) ()
let d_test_apply_io_bind_read_write () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_read_write ()) ()
let d_test_apply_io_bind_read_write' () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_read_write' ()) ()
let d_test_apply_io_bind_read_if_write () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_apply_io_bind_read_if_write ()) ()
let d_test_sendError400 () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_sendError400 ()) ()
let d_test_const_str () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_const_str ()) ()
let d_test_greeting () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_greeting ()) ()
let d_test_nat_zero () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_zero ()) ()
let d_test_nat_one () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_one ()) ()
let d_test_nat_two () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_two ()) ()
let d_test_nat_succ_fn () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_succ_fn ()) ()
let d_test_nat_nrec_base () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_nrec_base ()) ()
let d_test_nat_add2 () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_add2 ()) ()
let d_test_nat_nrec_two_plus_three1 () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_nrec_two_plus_three1 ()) ()
let d_test_nat_nrec_two_plus_three2 () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_nrec_two_plus_three2 ()) ()
let d_test_nat_fact_five () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_nat_fact_five ()) (_ by (norm [delta; iota]))


#push-options "--no_smt"
open ExamplesRefs

let test_refbool ()
  : qBoolR (fun t -> t == true) ⊩ refbool
  by (simplify_via_norm ())
  = pack_turnstile (QRef QTrue)

(* The refinement inferred for [QRef] need not be the one from [refbool]'s
   original F* type. The same derivation also checks at a different, weaker
   refinement that is nowhere mentioned by the source term. *)
let test_refbool_infers_weaker_refinement ()
  : qBoolR (fun t -> t == true \/ t == false) ⊩ refbool
  by (simplify_via_norm ())
  = pack_turnstile (QRef QTrue)

let test_falsepre ()
  : (qBoolR (fun _ -> False) ^-> qBool) ⊩ falsepre
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QRef QAxiom))

let test_just_true ()
  : (qBool ^-> qBoolR (fun x -> x == true)) ⊩ just_true
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QRef QTrue))

let test_moving_ref ()
  : (qBoolR (fun _ -> some_ref) ^-> qUnitR (fun _ -> some_ref)) ⊩ moving_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QRef Qtt))

[@@ (preprocess_with simplify_qType)]
let test_always_false ()
  : (qBool ^-> qBoolR (fun y -> y == false)) ⊩ always_false
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QRef (QIf QAxiom QFalse QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_always_false_complex ()
  : (qBool ^-> qBoolR (fun y -> y == false)) ⊩ always_false_complex
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QRef (QIf QAxiom (QIf QAxiom QFalse QTrue) QFalse)))

let test_always_false_ho ()
  : ((qUnit ^-> qBoolR (fun x -> x == true)) ^-> qBoolR (fun y -> y == false))
    ⊩ always_false_ho
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QRef (QIf (QRef (QApp QAxiom Qtt)) QFalse QTrue)))

[@@ (preprocess_with simplify_qType)]
let test_if_x ()
  : ((qBoolR (fun x -> x == true) ^-> qBool) ^-> qBool ^-> qBool) ⊩ if_x
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (QIf QAxiom
      (QApp qVar1 (QRef QAxiom)) QFalse)))

let test_seq_basic ()
  : ((qUnit ^-> qUnit) ^-> qUnit) ⊩ seq_basic
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (qLet (QApp QAxiom Qtt) Qtt))

let test_seq_qref ()
  : ((qUnit ^-> qUnitR (fun _ -> q_ref)) ^-> qUnitR (fun _ -> q_ref)) ⊩ seq_qref
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (qLet (QApp QAxiom Qtt) (QRef Qtt)))

let test_seq_p_implies_q ()
  : ((qBoolR p_ref ^-> qUnitR (fun _ -> q_ref)) ^-> qBoolR p_ref ^-> qBoolR (fun _ -> q_ref))
    ⊩ seq_p_implies_q
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda
      (qLet (QApp qVar1 QAxiom) (QRef qVar1))))

[@@ (preprocess_with simplify_qType)]
let test_if_seq ()
  : ((qBoolR (fun x -> x == true) ^-> qUnitR (fun _ -> q_ref)) ^-> qBool ^-> qBoolR (fun r -> r == true ==> q_ref))
    ⊩ if_seq
  by (simplify_via_norm ())
  = pack_turnstile (
    QLambda (QLambda (
      QIf QAxiom
        (qLet
          (QApp qVar1 (QRef QAxiom))
          (QRef qVar1))
        (QRef QAxiom))))

[@@ (preprocess_with simplify_qType)]
let test_context ()
  : (qBool ^-> (qBoolR (fun x -> x == true) ^-> qBool ^-> qBool) ^-> qBool ^-> qBool)
    ⊩ context
  by (simplify_via_norm ())
  = pack_turnstile (QLambda (QLambda (
    QIf qVar1
      (QApp QAxiom (QRef qVar1))
      (QLambda QAxiom))))

// let test_pure_fun ()
//  : (qArrR (qBoolR (fun b -> b == true)) qBool (fun b r -> r == b)) ⊩ pure_fun
//   by (simplify_via_norm ())
//   = pack_turnstile (QRetype (QLambda #(qBoolR (fun b -> b == true)) QTrue))

#pop-options

let d_test_refbool () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_refbool ()) ()

let d_test_refbool_infers_weaker_refinement () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_refbool_infers_weaker_refinement ()) ()

let d_test_falsepre () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_falsepre ()) ()
let d_test_just_true () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_just_true ()) ()
let d_test_moving_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_moving_ref ()) ()
let d_test_always_false () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_always_false ()) ()
let d_test_always_false_complex () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_always_false_complex ()) ()
let d_test_always_false_ho () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_always_false_ho ()) (())
let d_test_if_x () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_if_x ()) ()
let d_test_seq_basic () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_seq_basic ()) ()
let d_test_seq_qref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_seq_qref ()) ()
let d_test_seq_p_implies_q () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_seq_p_implies_q ()) ()
let d_test_if_seq () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_if_seq ()) ()
let d_test_context () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_context ()) ()
// let d_test_pure_fun () : _ ⊫ _
//   by (simplify_d ())
//   = mk_turniqet (test_pure_fun ()) (_ by (norm [delta; iota]))

#push-options "--no_smt"
open ExamplesIORefinements



(** Example 1: Erase refinement in IO *)
let test_ior_simple_erase_ref ()
  : (qBoolR (fun t -> t == true) ^->!@ qBool) ⊩ simple_erase_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QRef QAxiom)))

(** Example 2: Preserve refinement in IO *)
let test_ior_simple_ref_id ()
  : (qBoolR (fun t -> t == true) ^->!@ qBoolR (fun t -> t == true)) ⊩ simple_ref_id
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn QAxiom))

(** Example 3: Weaken refinement in IO *)
let test_ior_simple_reref_id ()
  : (qBoolR (fun t -> t == true) ^->!@ qBoolR (fun t -> t == true \/ t == false)) ⊩ simple_reref_id
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QRef QAxiom)))

(** Example 4: Bind with IO call, then return refined *)
[@@ (preprocess_with simplify_qType)]
let test_ior_simple_ref_bind ()
  : (qBoolR (fun t -> t == true) ^->!@ qBoolR (fun t -> t == true \/ t == false)) ⊩ simple_ref_bind
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
    QBind
      (QCall OOpen (QStringLit "./string"))
      (QReturn (QRef (QWeaken QAxiom)))))

(** Example 6: Return refined true constant *)
let test_ior_io_ret_ref_true ()
  : (qUnit ^->!@ qBoolR (fun x -> x == true)) ⊩ io_ret_ref_true
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QRef QTrue)))

(** Example 7: Return refined false constant *)
let test_ior_io_ret_ref_false ()
  : (qUnit ^->!@ qBoolR (fun x -> x == false)) ⊩ io_ret_ref_false
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QRef QFalse)))

(** Example 8: Negate refined input in IO *)

// [@@ (preprocess_with simplify_qType)]
let test_ior_io_negate_ref ()
  : (qBoolR (fun x -> x == true) ^->!@ qBoolR (fun y -> y == false)) ⊩ io_negate_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (
      QRef (QIf (QRef QAxiom) QFalse QTrue))))

(** Example 9: If-then-else with both branches false *)
let test_ior_io_if_both_false ()
  : (qBool ^->!@ qBoolR (fun y -> y == false)) ⊩ io_if_both_false
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QRef (QIf QAxiom QFalse QFalse))))

(** Example 10: Bind with unit, then return refined *)
let test_ior_io_bind_ret_ref ()
  : (qUnit ^->!@ qBoolR (fun x -> x == true)) ⊩ io_bind_ret_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
    QBind
      (QReturn Qtt)
      (QReturn (QRef QTrue))))

(** Example 11: IO call then return refined *)
let test_ior_io_call_ret_ref ()
  : (qUnit ^->!@ qBoolR (fun y -> y == true)) ⊩ io_call_ret_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
      QBind
        (QCall OOpen (QStringLit "./file"))
        (QReturn (QRef QTrue))))

(** Example 12: Two IO calls then return refined *)
let test_ior_io_two_calls_ref ()
  : (qUnit ^->!@ qBoolR (fun y -> y == true)) ⊩ io_two_calls_ref
  by (simplify_via_norm ())
  = pack_turnstile (
    QLambdaIO (
      QBind
        (QCall OOpen (QStringLit "./a"))
        (QBind
          (QCall OOpen (QStringLit "./b"))
          (QReturn (QRef QTrue)))))

(** Example 13: Inject Inl with refined input in IO *)
let test_ior_io_inl_ref ()
  : (qBoolR (fun x -> x == true) ^->!@ qResexn qBool) ⊩ io_inl_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QInl (QRef QAxiom))))

(** Example 14: Inject Inr (error) in IO *)
let test_ior_io_inr_ref ()
  : (qUnit ^->!@ qResexn qBool) ⊩ io_inr_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QInr Qtt)))

(** Example 15: Return pair with refined input in IO *)
let test_ior_io_pair_ref ()
  : (qBoolR (fun x -> x == true) ^->!@ (qBool ^* qUnit)) ⊩ io_pair_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (QReturn (QMkpair (QRef QAxiom) Qtt)))

(** Example 16: Case analysis returning refined in IO *)
[@@ (preprocess_with simplify_qType)]
let test_ior_io_case_ref ()
  : ((qBool ^+ qUnit) ^->!@ qBoolR (fun y -> y == false)) ⊩ io_case_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
      QCaseIO QAxiom
        (QReturn (QRef QFalse))
        (QReturn (QRef QFalse))))

(** Example 17: if!@ with refined result *)
[@@ (preprocess_with simplify_qType)]
let test_ior_io_ifbang_ref ()
  : (qBool ^->!@ qBoolR (fun y -> y == true)) ⊩ io_ifbang_ref
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
      QBind
        (QReturn QAxiom)
        (QIfIO QAxiom
          (QReturn (QRef QTrue))
          (QReturn (QRef QTrue)))))

(** Example 18: match!@ on IO call with refined result *)
[@@ (preprocess_with simplify_qType)]
let test_ior_io_matchbang_ref ()
  : (qUnit ^->!@ qBoolR (fun y -> y == true \/ y == false)) ⊩ io_matchbang_ref
  by (simplify_via_norm ())
  = pack_turnstile (
    QLambdaIO (
      QBind
        (QCall OOpen (QStringLit "./file"))
        (QCaseIO QAxiom
          (QReturn (QRef QTrue))
          (QReturn (QRef QFalse)))))

(** Example 19: Ghost sequencing before IO return *)
let test_ior_io_ghost_seq ()
  : ((qUnit ^-> qUnitR (fun _ -> ExamplesIORefinements.q_ref)) ^->!@ qUnitR (fun _ -> ExamplesIORefinements.q_ref)) ⊩ io_ghost_seq
  by (simplify_via_norm ())
  = pack_turnstile (QLambdaIO (
    QReturn (qLet (QApp QAxiom Qtt) (QRef Qtt))))

(** Example 20: Apply refined callback in IO *)
let test_ior_io_apply_callback ()
  : ((qBoolR (fun x -> x == true) ^-> qBool) ^->!@ qBool) ⊩ io_apply_callback
  by (simplify_via_norm ())
  = pack_turnstile (
    QLambdaIO (QReturn (QApp QAxiom (QRef QTrue))))

(** Example 21: Validate with refined callback in IO *)

(**
[@@ (preprocess_with simplify_qType)]
let test_ior_pure_validate ()
  : (qString ^-> (qArrR qString qBool (fun x y -> y ==> valid x)) ^-> qResexn (qStringR (fun x -> valid x))) ⊩ pure_validate
 by (simplify_via_norm ())
  = pack_turnstile (
      QLambda (QLambda (
        (QIf (QApp QAxiom (QWeaken QAxiom))
            (QInl (QRetype (QWeaken QAxiom)))
            (QInr Qtt)))))

[@@ (preprocess_with simplify_qType)]
let test_ior_io_validate_simp ()
  : (qString ^-> (qArrR qString qBool (fun x y -> y ==> valid x)) ^->!@ qResexn (qStringR (fun x -> valid x))) ⊩ io_validate_simp
 by (simplify_via_norm ())
  = pack_turnstile (
      QLambda (QLambdaIO (
        (QReturn
          (QIf (QApp QAxiom (QWeaken QAxiom))
              (QInl (QRetype (QWeaken QAxiom)))
              (QInr Qtt))))))
**)

// [@@ (preprocess_with simplify_qType)]
// let test_ior_io_validate ()
//   : ((qArrR qString qBool (fun x y -> y ==> valid x)) ^->!@ qResexn (qStringR (fun x -> valid x))) ⊩ io_validate
//   by (simplify_via_norm ())
//   = pack_turnstile (
//     QLambdaIO (
//       QBind (QCall OOpen (QStringLit "./file"))
//         (QCaseIO QAxiom
//           (QBind (QCall ORead QAxiom)
//             (QCaseIO QAxiom
//               (QReturn
//                 (QIf (QApp (QWeaken (QWeaken (QWeaken (QWeaken QAxiom)))) QAxiom)
//                     (QInl (QRetype QAxiom))
//                     (QInr Qtt)))
//               (QReturn (QInr QAxiom))))
//           (QReturn (QInr QAxiom)))))

#pop-options


let d_test_ior_simple_erase_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_simple_erase_ref ()) ()
let d_test_ior_simple_ref_id () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_simple_ref_id ()) ()
let d_test_ior_simple_reref_id () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_simple_reref_id ()) ()
let d_test_ior_simple_ref_bind () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_simple_ref_bind ()) ()
let d_test_ior_io_ret_ref_true () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_ret_ref_true ()) ()
let d_test_ior_io_ret_ref_false () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_ret_ref_false ()) ()
let d_test_ior_io_negate_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_negate_ref ()) ()
let d_test_ior_io_if_both_false () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_if_both_false ()) ()
let d_test_ior_io_bind_ret_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_bind_ret_ref ()) ()
let d_test_ior_io_call_ret_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_call_ret_ref ()) ()
let d_test_ior_io_two_calls_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_two_calls_ref ()) ()
let d_test_ior_io_inl_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_inl_ref ()) ()
let d_test_ior_io_inr_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_inr_ref ()) ()
let d_test_ior_io_pair_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_pair_ref ()) ()
let d_test_ior_io_case_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_case_ref ()) ()
let d_test_ior_io_ifbang_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_ifbang_ref ()) ()
let d_test_ior_io_matchbang_ref () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_matchbang_ref ()) ()
//let d_test_ior_io_ghost_seq () : _ ⊫ _
//  by (simplify_d ())
//  = mk_turniqet (test_ior_io_ghost_seq ()) ()
let d_test_ior_io_apply_callback () : _ ⊫ _
  by (simplify_d ())
  = mk_turniqet (test_ior_io_apply_callback ()) ()
// let d_test_ior_pure_validate () : _ ⊫ _
//   by (simplify_d ())
//   = mk_turniqet (test_ior_pure_validate ()) (_ by (norm [delta; iota]))
//let d_test_ior_io_validate_simp () : _ ⊫ _
//  by (simplify_d ())
//  = mk_turniqet (test_ior_io_validate_simp ()) (_ by (norm [delta; iota]))
// let d_test_ior_io_validate () : _ ⊫ _
//   by (simplify_d ())
//   = mk_turniqet (test_ior_io_validate ()) (_ by (norm [delta; iota]))

(* Counterexample: on a refinable base type, QRef can make the top-level precondition unsatisfiable. *)
let test_qref_false_pre_on_bool ()
  : qBool ⊩ true
  by (simplify_via_norm ())
  = pack_turnstile (QRef (QRef QTrue #(fun _ -> False)) #(fun _ -> True))

let test_qref_false_pre_on_bool_unsat ()
  : Lemma (~((dfst (test_qref_false_pre_on_bool ())) empty_eval))
  = ()
