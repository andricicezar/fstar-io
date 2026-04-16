module RQ.TypingRelation.Tests

open FStar.Tactics.V1
open Trace
open RQ.TypingRelation
open QTypes.HelperTactics

let simplify_via_norm () : Tac unit =
  let _ = repeat forall_intro in
  or_else trivial trefl

let simplify_d () : Tac unit = norm [delta_only [
      `%fs_oval; `%fs_val; `%qUnit; `%qBool; `%qString; `%qResexn; `%qFileDescr;
      `%qUnitR;`%qBoolR;`%qFileDescrR;`%qStringR;
      `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Plus;
      `%op_Hat_Subtraction_Greater_Bang_At;
      `%get_rel; `%get_Type;
      `%q_io_args; `%q_io_res;
      `%Mkdtuple2?._1;`%Mkdtuple2?._2];
    iota]

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

let test_ut_unit
  : qUnit ⊩ ut_unit
  = mk_dturniqet (fun _ -> Qtt)

let test_ut_true
  : qBool ⊩ ut_true
  = mk_dturniqet (fun _ -> QTrue)

let test_ut_false
  : qBool ⊩ ut_false
  = mk_dturniqet (fun _ -> QFalse)

let test_constant ()
  : ((qBool ^-> qBool) ⊩ constant)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda QTrue)

let test_constant' ()
  : ((qBool ^-> qBool) ⊩ constant)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QWeaken QTrue))

let test_identity ()
  : (qBool ^-> qBool) ⊩ identity
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda QAxiom)

let test_thunked_id ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ thunked_id
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda QAxiom))

let test_proj1 ()
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj1
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QLambda qVar2)))

let test_proj2 ()
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj2
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QLambda qVar1)))

let test_proj3 ()
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj3
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QLambda QAxiom)))

let test_apply_top_level_def ()
  : (qBool ^-> qBool) ⊩ apply_top_level_def
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QApp
              (QApp
                (QLambda (QLambda QAxiom))
                QAxiom)
              QTrue))

let test_apply_top_level_def' ()
  : (qBool ^-> qBool ^-> qBool) ⊩ apply_top_level_def'
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QApp
                       (QApp
                          (QLambda (QLambda QAxiom))
                          qVar1)
                       QAxiom)))

let test_papply__top_level_def ()
  : (qBool ^-> qBool ^-> qBool) ⊩ papply__top_level_def
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QApp
              (QLambda (QLambda QAxiom))
              QAxiom))

let test_apply_arg ()
  : ((qUnit ^-> qUnit) ^-> qUnit) ⊩ apply_arg
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QApp QAxiom Qtt))

let test_apply_arg2 ()
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool) ⊩ apply_arg2
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QApp (QApp QAxiom QTrue) QFalse))

let test_papply_arg2 ()
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool ^-> qBool) ⊩ papply_arg2
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QApp QAxiom QTrue))

[@expect_failure]
let test_proj2'
  : (qBool ^-> qBool ^-> qBool ^-> qBool) ⊩ proj2
  = mk_dturniqet (fun _ -> QLambda (QLambda (QLambda QAxiom)))

let test_anif ()
  : qBool ⊩ anif
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QIf QTrue QFalse QTrue)

let test_negb ()
  : (qBool ^-> qBool) ⊩ negb
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QIf QAxiom QFalse QTrue))

let test_negb_pred ()
  : ((qBool ^-> qBool) ^-> qBool ^-> qBool) ⊩ negb_pred
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QIf (QApp qVar1 QAxiom) QFalse QTrue)))

let test_if2 ()
  : (qBool ^-> qBool ^-> qBool) ⊩ if2
  by (simplify_stack_ops (); simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QIf qVar1 QFalse QAxiom)))

let test_callback_return ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QIf QAxiom
                 (QLambda qVar1)
                 (QLambda QAxiom)))

let test_callback_return' ()
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return'
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QIf QAxiom
                 (QLambda qVar1)
                 (QLambda QAxiom)))

let test_make_pair ()
  : (qBool ^-> qBool ^-> (qBool ^* qBool)) ⊩ make_pair
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QMkpair qVar1 QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions ()
  : Tot (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
                            ⊩ pair_of_functions)
  by (simplify_stack_ops (); simplify_via_norm ())
  = mk_dturniqet (fun _ ->  QMkpair
      (QLambda (QApp
                  (QLambda (QIf QAxiom QFalse QTrue))
                  QAxiom))
      (QLambda (QLambda QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions2 ()
  : (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
    ⊩ pair_of_functions2)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QMkpair
      (QLambda (QIf QAxiom QFalse QTrue))
      (QLambda (QLambda (QIf qVar1 QFalse QAxiom))))

let test_fst_pair ()
  : (qBool) ⊩ fst_pair
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> (QFst (QMkpair QTrue Qtt)))

let test_wrap_fst ()
  : ((qBool ^* qBool) ^-> qBool) ⊩ wrap_fst
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QFst QAxiom))

let test_wrap_fst_pa ()
  : ((qBool ^* qBool) ^-> qBool) ⊩ wrap_fst_pa
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QFst QAxiom))

let test_snd_pair ()
  : (qUnit) ⊩ snd_pair
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> (QSnd (QMkpair QTrue Qtt)))

let test_wrap_snd ()
  : ((qBool ^* qUnit) ^-> qUnit) ⊩ wrap_snd
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QSnd QAxiom))

let test_wrap_snd_pa ()
  : ((qBool ^* qUnit) ^-> qUnit) ⊩ wrap_snd_pa
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QSnd QAxiom))

let qLet #g (#a #b:qType) #wpx #wpf (#x:fs_oval g a wpx) (#f:fs_oval (extend a g) b wpf)
  (qx : typing g x) (qf : typing _ f)
  : typing g (fs_oval_app (fs_oval_lambda f) x)
  = QApp (QLambda qf) qx

let three_lets : bool -> unit =
  fun x -> let p = (x, x) in let _y = x in let _z = fst p in ()

 let test_three_lets ()
   : (qBool ^-> qUnit) ⊩ three_lets
   by (simplify_via_norm ())
   = mk_dturniqet (fun _ -> QLambda
      (qLet (QMkpair QAxiom QAxiom)
      (qLet (QWeaken QAxiom)
      (qLet (QFst qVar1)
      Qtt))))

let test_inl_true ()
  : (qBool ^+ qUnit) ⊩ inl_true
   by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QInl QTrue)

let test_inr_unit ()
  : (qBool ^+ qUnit) ⊩ inr_unit
   by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QInr Qtt)

[@@ (preprocess_with simplify_qType)]
let test_return_either ()
  : (qBool ^-> (qUnit ^+ qUnit)) ⊩ return_either
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QIf QAxiom (QInl Qtt) (QInr Qtt)))

[@@ (preprocess_with simplify_qType)]
let test_match_either ()
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QCase QAxiom QAxiom QAxiom))

[@expect_failure]
let test_match_either'
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either'
  = mk_dturniqet (fun _ -> QLambda (QCase QAxiom QAxiom QAxiom))

[@@ (preprocess_with simplify_qType)]
let test_match_either_arg ()
  : (((qBool ^+ qBool) ^-> qBool ^-> qBool) ⊩ match_either_arg)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (
       QCase
         qVar1
         QAxiom
         qVar1)))
#pop-options

let d_test_constant () : typing _ _ =
  get_derivation (test_constant ()) ()
let d_test_constant' () : typing _ _ =
  get_derivation (test_constant' ()) ()
let d_test_identity () : typing _ _ =
  get_derivation (test_identity ()) ()
let d_test_thunked_id () : typing _ _ =
  get_derivation (test_thunked_id ()) ()
let d_test_proj1 () : typing _ _ =
  get_derivation (test_proj1 ()) ()
let d_test_proj2 () : typing _ _ =
  get_derivation (test_proj2 ()) ()
let d_test_proj3 () : typing _ _ =
  get_derivation (test_proj3 ()) ()
let d_test_apply_top_level_def () : typing _ _ =
  get_derivation (test_apply_top_level_def ()) ()
let d_test_apply_top_level_def' () : typing _ _ =
  get_derivation (test_apply_top_level_def' ()) ()
let d_test_papply__top_level_def () : typing _ _ =
  get_derivation (test_papply__top_level_def ()) ()
let d_test_apply_arg () : typing _ _ =
  get_derivation (test_apply_arg ()) ()
let d_test_apply_arg2 () : typing _ _ =
  get_derivation (test_apply_arg2 ()) ()
let d_test_papply_arg2 () : typing _ _ =
  get_derivation (test_papply_arg2 ()) ()
let d_test_anif () : typing _ _ =
  get_derivation (test_anif ()) ()
let d_test_negb () : typing _ _ =
  get_derivation (test_negb ()) ()
let d_test_negb_pred () : typing _ _ =
  get_derivation (test_negb_pred ()) ()
let d_test_if2 () : typing _ _ =
  get_derivation (test_if2 ()) ()
let d_test_callback_return () : typing _ _ =
  get_derivation (test_callback_return ()) ()
let d_test_callback_return' () : typing _ _ =
  get_derivation (test_callback_return' ()) ()

#push-options "--no_smt"
open ExamplesIO

let test_u_return ()
  : (qUnit ^->!@ qBool) ⊩ u_return
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn QTrue))

let test_apply_io_return ()
  : (qBool ^->!@ qBool) ⊩ apply_io_return
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn QAxiom))

[@@ (preprocess_with simplify_qType)]
let test_apply_read ()
  : (qUnit ^->!@ (qResexn qString)) ⊩ apply_read
  by (simplify_stack_ops (); norm [delta_only [`%fs_oval_helper;`%apply_read];iota]; simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QCall ORead (QFd 0)))

let test_apply_write_const ()
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_write_const
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QCall OWrite (QMkpair (QFd 2) (QStringLit "hello"))))

let test_apply_write ()
  : _ ⊩  apply_write
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QCall OWrite (QMkpair (QFd 1) QAxiom)))

let test_apply_io_bind_const ()
  : (qUnit ^->!@ qBool) ⊩ apply_io_bind_const

  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (
      QBind
        (QReturn QTrue)
        (QReturn QAxiom)))

let test_apply_io_bind_identity ()
  : (qBool ^->!@ qBool) ⊩ apply_io_bind_identity
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO
      (QBind
        (QReturn QAxiom)
        (QReturn QAxiom)))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_pure_if ()
  : Tot ((qBool ^->!@ qBool) ⊩ apply_io_bind_pure_if)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO
      (QBind
        (QReturn QAxiom)
        (QIfIO QAxiom
           (QReturn QFalse)
           (QReturn QTrue))))

let test_apply_io_bind_write ()
  : _ ⊩ apply_io_bind_write
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (
      QBind
         (QReturn QAxiom)
         (QCall OWrite (QMkpair (QFd 2) QAxiom))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_write ()
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_write
  by ( simplify_stack_ops (); simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QCall ORead (QFd 4))
    (QCaseIO QAxiom
      (QCall OWrite (QMkpair (QFd 1) (QStringLit "data")))
      (QReturn (QInr QAxiom)))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_write' ()
   : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_write'
   by (simplify_via_norm ())
   = mk_dturniqet (fun _ -> QLambdaIO (QBind (QCall ORead (QFd 9)) (
       QCaseIO QAxiom (QCall OWrite (QMkpair (QFd 2) (QStringLit "data"))) (QReturn (QInr QAxiom)))))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_read_if_write ()
  : (qUnit ^->!@ (qResexn qUnit)) ⊩ apply_io_bind_read_if_write
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO
      (QBind
        (QCall ORead (QFd 0))
         (QCaseIO QAxiom
           (QCall OWrite (QMkpair (QFd 7) (QStringLit "data")))
           (QReturn (QInr QAxiom)))))

let test_sendError400 ()
  : (qBool ^->!@ qUnit) ⊩ sendError400
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO
      (QBind
        (QCall OWrite (QMkpair (QFd 9) (QStringLit "error400")))
        (QReturn Qtt)))

let test_const_str
  : qString ⊩ const_str
  = mk_dturniqet (fun _ -> QStringLit "constant")

let test_greeting ()
  : (qBool ^-> qString) ⊩ greeting
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QIf QAxiom (QStringLit "hello") (QStringLit "goodbye")))

#pop-options

let d_test_u_return () : typing _ _
  by (simplify_d ())
  = get_derivation (test_u_return ()) ()
let d_test_apply_io_return () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_return ()) ()
let d_test_apply_read () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_read ()) ()
let d_test_apply_write_const () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_write_const ()) ()
let d_test_apply_write () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_write ()) ()
let d_test_apply_io_bind_const () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_const ()) ()
let d_test_apply_io_bind_identity () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_identity ()) ()
let d_test_apply_io_bind_pure_if () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_pure_if ()) ()
let d_test_apply_io_bind_write () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_write ()) ()
let d_test_apply_io_bind_read_write () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_read_write ()) ()
let d_test_apply_io_bind_read_write' () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_read_write' ()) ()
let d_test_apply_io_bind_read_if_write () : typing _ _
  by (simplify_d ())
  = get_derivation (test_apply_io_bind_read_if_write ()) ()
let d_test_sendError400 () : typing _ _
  by (simplify_d ())
  = get_derivation (test_sendError400 ()) ()
let d_test_const_str () : typing _ _
  by (simplify_d ())
  = get_derivation test_const_str ()
let d_test_greeting () : typing _ _
  by (simplify_d ())
  = get_derivation (test_greeting ()) ()

#push-options "--no_smt"
open ExamplesRefs

let test_refbool ()
  : qBoolR (fun t -> t == true) ⊩ refbool
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QRetype QTrue)

let test_falsepre ()
  : (qBoolR (fun _ -> False) ^-> qBool) ⊩ falsepre
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype QAxiom))

let test_just_true ()
  : (qBool ^-> qBoolR (fun x -> x == true)) ⊩ just_true
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype QTrue))

let test_moving_ref ()
  : (qBoolR (fun _ -> some_ref) ^-> qUnitR (fun _ -> some_ref)) ⊩ moving_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype Qtt))

let test_always_false ()
  : (qBool ^-> qBoolR (fun y -> y == false)) ⊩ always_false
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype (QIf QAxiom QFalse QAxiom)))

let test_always_false_complex ()
  : (qBool ^-> qBoolR (fun y -> y == false)) ⊩ always_false_complex
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype (QIf QAxiom (QIf QAxiom QFalse QTrue) QFalse)))

let test_always_false_ho ()
  : ((qUnit ^-> qBoolR (fun x -> x == true)) ^-> qBoolR (fun y -> y == false))
    ⊩ always_false_ho
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype
      (QIf (QRetype (QApp QAxiom Qtt)) QFalse QTrue)))

let test_if_x ()
  : ((qBoolR (fun x -> x == true) ^-> qBool) ^-> qBool ^-> qBool) ⊩ if_x
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QIf QAxiom
      (QApp qVar1 (QRetype QAxiom)) QFalse)))

let test_seq_basic ()
  : ((qUnit ^-> qUnit) ^-> qUnit) ⊩ seq_basic
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QSeqGhost True (QRetype (QApp QAxiom Qtt)) Qtt))

let test_seq_qref ()
  : ((qUnit ^-> qUnitR (fun _ -> q_ref)) ^-> qUnitR (fun _ -> q_ref)) ⊩ seq_qref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QSeqGhost q_ref (QApp QAxiom Qtt) (QRetype Qtt)))

let test_seq_p_implies_q ()
  : ((qBoolR p_ref ^-> qUnitR (fun _ -> q_ref)) ^-> qBoolR p_ref ^-> qBoolR (fun _ -> q_ref))
    ⊩ seq_p_implies_q
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda
      (QSeqGhost q_ref (QApp qVar1 QAxiom) (QRetype QAxiom))))

let test_if_seq ()
  : ((qBoolR (fun x -> x == true) ^-> qUnitR (fun _ -> q_ref)) ^-> qBool ^-> qBoolR (fun r -> r == true ==> q_ref))
    ⊩ if_seq
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ ->
    QLambda (QLambda (QIf QAxiom
      (QSeqGhost q_ref
        (QApp qVar1 (QRetype QAxiom))
        (QRetype QAxiom))
      (QRetype QAxiom))))

let test_context ()
  : (qBool ^-> (qBoolR (fun x -> x == true) ^-> qBool ^-> qBool) ^-> qBool ^-> qBool)
    ⊩ context
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QLambda (QIf qVar1
      (QApp QAxiom (QRetype qVar1))
      (QLambda QAxiom))))

[@@expect_failure]
// [@@ (preprocess_with simplify_qType)]
let test_pure_fun ()
 : (qArrR (qBoolR (fun b -> b == true)) qBool (fun b r -> r == b)) ⊩ pure_fun
  by (simplify_stack_ops (); dump "H"; simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambda (QRetype QTrue))


#pop-options

let d_test_refbool () : typing _ _
  by (simplify_d ())
  = get_derivation (test_refbool ()) (_ by (norm [delta; iota]))

let d_test_falsepre () : typing _ _
  by (simplify_d ())
  = get_derivation (test_falsepre ()) ()
let d_test_just_true () : typing _ _
  by (simplify_d ())
  = get_derivation (test_just_true ()) ()
let d_test_moving_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_moving_ref ()) ()
let d_test_always_false () : typing _ _
  by (simplify_d ())
  = get_derivation (test_always_false ()) ()
let d_test_always_false_complex () : typing _ _
  by (simplify_d ())
  = get_derivation (test_always_false_complex ()) ()
let d_test_always_false_ho () : typing _ _
  by (simplify_d ())
  = get_derivation (test_always_false_ho ()) (())
let d_test_if_x () : typing _ _
  by (simplify_d ())
  = get_derivation (test_if_x ()) ()
let d_test_seq_basic () : typing _ _
  by (simplify_d ())
  = get_derivation (test_seq_basic ()) ()
let d_test_seq_qref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_seq_qref ()) ()
let d_test_seq_p_implies_q () : typing _ _
  by (simplify_d ())
  = get_derivation (test_seq_p_implies_q ()) ()
let d_test_if_seq () : typing _ _
  by (simplify_d ())
  = get_derivation (test_if_seq ()) ()
let d_test_context () : typing _ _
  by (simplify_d ())
  = get_derivation (test_context ()) ()

#push-options "--no_smt"
open ExamplesIORefinements

(** Example 1: Erase refinement in IO *)
let test_ior_simple_erase_ref ()
  : (qBoolR (fun t -> t == true) ^->!@ qBool) ⊩ simple_erase_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QRetype QAxiom)))

(** Example 2: Preserve refinement in IO *)
let test_ior_simple_ref_id ()
  : (qBoolR (fun t -> t == true) ^->!@ qBoolR (fun t -> t == true)) ⊩ simple_ref_id
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn QAxiom))

(** Example 3: Weaken refinement in IO *)
let test_ior_simple_reref_id ()
  : (qBoolR (fun t -> t == true) ^->!@ qBoolR (fun t -> t == true \/ t == false)) ⊩ simple_reref_id
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QRetype QAxiom)))

(** Example 4: Bind with IO call, then return refined *)
let test_ior_simple_ref_bind ()
  : (qBoolR (fun t -> t == true) ^->!@ qBoolR (fun t -> t == true \/ t == false)) ⊩ simple_ref_bind
  by (simplify_stack_ops (); simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QCall OOpen (QStringLit "./string")) (QReturn (QRetype (QWeaken QAxiom)))))

(** Example 6: Return refined true constant *)
let test_ior_io_ret_ref_true ()
  : (qUnit ^->!@ qBoolR (fun x -> x == true)) ⊩ io_ret_ref_true
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QRetype QTrue)))

(** Example 7: Return refined false constant *)
let test_ior_io_ret_ref_false ()
  : (qUnit ^->!@ qBoolR (fun x -> x == false)) ⊩ io_ret_ref_false
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QRetype QFalse)))

(** Example 8: Negate refined input in IO *)
let test_ior_io_negate_ref ()
  : (qBoolR (fun x -> x == true) ^->!@ qBoolR (fun y -> y == false)) ⊩ io_negate_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QRetype (QIf (QRetype QAxiom) QFalse QTrue))))

(** Example 9: If-then-else with both branches false *)
let test_ior_io_if_both_false ()
  : (qBool ^->!@ qBoolR (fun y -> y == false)) ⊩ io_if_both_false
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QRetype (QIf QAxiom QFalse QFalse))))

(** Example 10: Bind with unit, then return refined *)
let test_ior_io_bind_ret_ref ()
  : (qUnit ^->!@ qBoolR (fun x -> x == true)) ⊩ io_bind_ret_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QReturn Qtt) (QReturn (QRetype QTrue))))

(** Example 11: IO call then return refined *)
let test_ior_io_call_ret_ref ()
  : (qUnit ^->!@ qBoolR (fun y -> y == true)) ⊩ io_call_ret_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QCall OOpen (QStringLit "./file")) (QReturn (QRetype QTrue))))

(** Example 12: Two IO calls then return refined *)
let test_ior_io_two_calls_ref ()
  : (qUnit ^->!@ qBoolR (fun y -> y == true)) ⊩ io_two_calls_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QCall OOpen (QStringLit "./a")) (QBind (QCall OOpen (QStringLit "./b")) (QReturn (QRetype QTrue)))))

(** Example 13: Inject Inl with refined input in IO *)
let test_ior_io_inl_ref ()
  : (qBoolR (fun x -> x == true) ^->!@ qResexn qBool) ⊩ io_inl_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QInl (QRetype QAxiom))))

(** Example 14: Inject Inr (error) in IO *)
let test_ior_io_inr_ref ()
  : (qUnit ^->!@ qResexn qBool) ⊩ io_inr_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QInr Qtt)))

(** Example 15: Return pair with refined input in IO *)
let test_ior_io_pair_ref ()
  : (qBoolR (fun x -> x == true) ^->!@ (qBool ^* qUnit)) ⊩ io_pair_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QMkpair (QRetype QAxiom) Qtt)))

(** Example 16: Case analysis returning refined in IO *)
[@@ (preprocess_with simplify_qType)]
let test_ior_io_case_ref ()
  : ((qBool ^+ qUnit) ^->!@ qBoolR (fun y -> y == false)) ⊩ io_case_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QCaseIO QAxiom (QReturn (QRetype QFalse)) (QReturn (QRetype QFalse))))

(** Example 17: if!@ with refined result *)
[@@ (preprocess_with simplify_qType)]
let test_ior_io_ifbang_ref ()
  : (qBool ^->!@ qBoolR (fun y -> y == true)) ⊩ io_ifbang_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QReturn QAxiom) (QIfIO QAxiom (QReturn (QRetype QTrue)) (QReturn (QRetype QTrue)))))

(** Example 18: match!@ on IO call with refined result *)
[@@ (preprocess_with simplify_qType)]
let test_ior_io_matchbang_ref ()
  : (qUnit ^->!@ qBoolR (fun y -> y == true \/ y == false)) ⊩ io_matchbang_ref
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QBind (QCall OOpen (QStringLit "./file")) (QCaseIO QAxiom (QReturn (QRetype QTrue)) (QReturn (QRetype QFalse)))))

(** Example 19: Ghost sequencing before IO return *)
let test_ior_io_ghost_seq ()
  : ((qUnit ^-> qUnitR (fun _ -> ExamplesIORefinements.q_ref)) ^->!@ qUnitR (fun _ -> ExamplesIORefinements.q_ref)) ⊩ io_ghost_seq
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QSeqGhost ExamplesIORefinements.q_ref (QApp QAxiom Qtt) (QRetype Qtt))))

(** Example 20: Apply refined callback in IO *)
let test_ior_io_apply_callback ()
  : ((qBoolR (fun x -> x == true) ^-> qBool) ^->!@ qBool) ⊩ io_apply_callback
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaIO (QReturn (QApp QAxiom (QRetype QTrue))))

(** Example 21: Validate with refined callback in IO *)

[@@ (preprocess_with simplify_qType)]
let test_ior_pure_validate ()
  : (qString ^-> (qArrR qString qBool (fun x y -> y ==> valid x)) ^-> qResexn (qStringR (fun x -> valid x))) ⊩ pure_validate
 by (simplify_via_norm ())
  = mk_dturniqet (fun _ ->
      QLambda (QLambda (
        (QIf (QApp QAxiom (QWeaken QAxiom))
            (QInl (QRetype (QWeaken QAxiom)))
            (QInr Qtt)))))

[@@ (preprocess_with simplify_qType)]
let test_ior_io_validate_simp ()
  : (qString ^-> (qArrR qString qBool (fun x y -> y ==> valid x)) ^->!@ qResexn (qStringR (fun x -> valid x))) ⊩ io_validate_simp
 by (simplify_via_norm ())
  = mk_dturniqet (fun _ ->
      QLambda (QLambdaIO (
        (QReturn
          (QIf (QApp QAxiom (QWeaken QAxiom))
              (QInl (QRetype (QWeaken QAxiom)))
              (QInr Qtt))))))

// [@@ (preprocess_with simplify_qType)]
// let test_ior_io_validate ()
//   : ((qArrR qString qBool (fun x y -> y ==> valid x)) ^->!@ qResexn (qStringR (fun x -> valid x))) ⊩ io_validate
//   by (simplify_stack_ops (); simplify_via_norm ())
//   = mk_dturniqet (fun _ ->
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


let d_test_ior_simple_erase_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_simple_erase_ref ()) ()
let d_test_ior_simple_ref_id () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_simple_ref_id ()) ()
let d_test_ior_simple_reref_id () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_simple_reref_id ()) ()
let d_test_ior_simple_ref_bind () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_simple_ref_bind ()) ()
let d_test_ior_io_ret_ref_true () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_ret_ref_true ()) ()
let d_test_ior_io_ret_ref_false () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_ret_ref_false ()) ()
let d_test_ior_io_negate_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_negate_ref ()) ()
let d_test_ior_io_if_both_false () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_if_both_false ()) ()
let d_test_ior_io_bind_ret_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_bind_ret_ref ()) ()
let d_test_ior_io_call_ret_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_call_ret_ref ()) ()
let d_test_ior_io_two_calls_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_two_calls_ref ()) ()
let d_test_ior_io_inl_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_inl_ref ()) ()
let d_test_ior_io_inr_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_inr_ref ()) ()
let d_test_ior_io_pair_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_pair_ref ()) ()
let d_test_ior_io_case_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_case_ref ()) (_ by (norm [delta; iota]))
let d_test_ior_io_ifbang_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_ifbang_ref ()) ()
let d_test_ior_io_matchbang_ref () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_matchbang_ref ()) (_ by (norm [delta; iota]))
let d_test_ior_io_ghost_seq () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_ghost_seq ()) ()
let d_test_ior_io_apply_callback () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_apply_callback ()) ()
let d_test_ior_pure_validate () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_pure_validate ()) (_ by (norm [delta; iota]))
let d_test_ior_io_validate_simp () : typing _ _
  by (simplify_d ())
  = get_derivation (test_ior_io_validate_simp ()) (_ by (norm [delta; iota]))
// let d_test_ior_io_validate () : typing _ _
//   by (simplify_d ())
//   = get_derivation (test_ior_io_validate ()) (_ by (norm [delta; iota]))
