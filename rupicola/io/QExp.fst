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
  fs_oexp (extend a g) a
let helper_var0 g a fsG = hd fsG

unfold
val helper_varS : g:typ_env ->
                  a:qType ->
                  b:qType ->
                  fs_oexp g a ->
                  fs_oexp (extend b g) a
let helper_varS g a b x fsG = x (tail fsG)

unfold
val helper_unit : g:typ_env -> fs_oexp g qUnit
let helper_unit g _ = ()

unfold
val helper_app: #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oexp g (a ^-> b) ->
                x :fs_oexp g a ->
                fs_oexp g b
let helper_app f x fsG =
  (f fsG) (x fsG)

unfold
val helper_app_io :
                #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oexp g (a ^->!@ b) ->
                x :fs_oexp g a ->
                io_oexp g b
let helper_app_io f x fsG =
  (f fsG) (x fsG)

unfold
val helper_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                f :fs_oexp g (a ^-> b) ->
                fs_oexp (extend a g) b
let helper_lambda #_ #_ f fsG = f (tail fsG) (hd fsG)

unfold
val helper_lambda_io : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                f :fs_oexp g (a ^->!@ b) ->
                io_oexp (extend a g) b
let helper_lambda_io #_ #_ f fsG = f (tail fsG) (hd fsG)

unfold
val helper_true : g:typ_env -> fs_oexp g qBool
let helper_true g _ = true

unfold
val helper_false : g:typ_env -> fs_oexp g qBool
let helper_false g _ = false

unfold
val helper_if : #g :typ_env ->
                #a  : qType ->
                c   : fs_oexp g qBool ->
                t   : fs_oexp g a ->
                e   : fs_oexp g a ->
                fs_oexp g a
let helper_if c t e fsG =
  if c fsG then t fsG else e fsG

unfold
val helper_if_io : #g :typ_env ->
                #a  : qType ->
                c   : fs_oexp g qBool ->
                t   : io_oexp g a ->
                e   : io_oexp g a ->
                io_oexp g a
let helper_if_io c t e fsG =
  if c fsG then t fsG else e fsG

unfold
val helper_pair : #g : typ_env ->
                  #a : qType ->
                  #b : qType ->
                  x : fs_oexp g a ->
                  y : fs_oexp g b ->
                  fs_oexp g (a ^* b)
let helper_pair #_ #_ #_ x y fsG =
  (x fsG, y fsG)

unfold
val helper_fst : #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 p : fs_oexp g (a ^* b) ->
                 fs_oexp g a
let helper_fst #_ #_ #_ p fsG = fst (p fsG)

unfold
val helper_snd : #g : typ_env ->
                 #a : qType ->
                 #b : qType ->
                 p : fs_oexp g (a ^* b) ->
                 fs_oexp g b
let helper_snd #_ #_ #_ p fsG = snd (p fsG)

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type exp_quotation : #a:qType -> g:typ_env -> fs_oexp g a -> Type =
| Qtt         : #g : typ_env -> exp_quotation g (helper_unit g)

| QVar0       : #g : typ_env ->
                #a : qType ->
                exp_quotation _ (helper_var0 g a)

| QVarS       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #x : fs_oexp g a ->
                exp_quotation g x ->
                exp_quotation _ (helper_varS g a b x)

(** we need a case for each deBrujin variable **)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oexp g (a ^-> b) ->
                #x : fs_oexp g a ->
                exp_quotation g f ->
                exp_quotation g x ->
                exp_quotation g (helper_app f x)

| QLambda     : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oexp g (a ^-> b) ->
                exp_quotation (extend a g) (helper_lambda f) ->
                exp_quotation g f

| QLambdaIO   : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oexp g (a ^->!@ b) ->
                io_quotation (extend a g) (helper_lambda_io f) ->
                exp_quotation g f

| QTrue       : #g : typ_env -> exp_quotation g (helper_true g)
| QFalse      : #g : typ_env -> exp_quotation g (helper_false g)
| QIf         : #g : typ_env ->
                #a : qType ->
                #c : fs_oexp g qBool ->
                exp_quotation #qBool g c ->
                #t : fs_oexp g a ->
                exp_quotation g t ->
                #e : fs_oexp g a ->
                exp_quotation g e ->
                exp_quotation g (helper_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #x : fs_oexp g a ->
              #y : fs_oexp g b ->
              exp_quotation g x ->
              exp_quotation g y ->
              exp_quotation g (helper_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oexp g (a ^* b) ->
              exp_quotation g p ->
              exp_quotation g (helper_fst p)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oexp g (a ^* b) ->
              exp_quotation g p ->
              exp_quotation g (helper_snd p)
| QRead :
        #g:typ_env ->
        exp_quotation #(qUnit ^->!@ qBool) g (fun _ -> read)

| QWrite :
        #g:typ_env ->
        exp_quotation #(qBool ^->!@ qUnit) g (fun _ -> write)
and io_quotation : #a:qType -> g:typ_env -> io_oexp g a -> Type =
(** Return and Bind of the monad **)
| QReturn :
        #g:typ_env ->
        #a:qType ->
        #x:fs_oexp g a ->
        exp_quotation g x ->
        io_quotation #a g (fun fsG -> return (x fsG))

| QBind :
        #g:typ_env ->
        #a:qType ->
        #b:qType ->
        #m:io_oexp g a ->
        #k:fs_oexp g (a ^->!@ b) ->
        io_quotation g m ->
        exp_quotation g k ->
        io_quotation #b g (fun fsG -> io_bind (m fsG) (k fsG))

| QAppIO      : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oexp g (a ^->!@ b) ->
                #x : fs_oexp g a ->
                exp_quotation g f ->
                exp_quotation g x ->
                io_quotation g (helper_app_io f x)
| QIfIO       : #g : typ_env ->
                #a : qType ->
                #c : fs_oexp g qBool ->
                exp_quotation #qBool g c ->
                #t : io_oexp g a ->
                io_quotation g t ->
                #e : io_oexp g a ->
                io_quotation g e ->
                io_quotation g (helper_if_io c t e)

unfold
let helper_oexp (#a:qType) (x:get_Type a) : fs_oexp empty a = fun _ -> x

unfold
let helper_io_oexp (#a:qType) (x:io (get_Type a)) : io_oexp empty a = fun _ -> x

type closed_exp_quotation (a:qType) (x:get_Type a) =
  exp_quotation #a empty (helper_oexp x)

type closed_io_exp_quotation (a:qType) (x:io (get_Type a)) =
  io_quotation #a empty (helper_io_oexp x)

open Examples

#push-options "--no_smt"

let test_ut_unit
  : closed_exp_quotation qUnit ut_unit
  = Qtt

let test_ut_true
  : closed_exp_quotation qBool ut_true
  = QTrue

let test_ut_false
  : closed_exp_quotation qBool ut_false
  = QFalse

val var0 : fs_oexp (extend qBool empty) qBool
let var0 fsG = hd fsG

val var1 : fs_oexp (extend qBool (extend qBool empty)) qBool
let var1 fsG = hd (tail fsG)

let var2 : fs_oexp (extend qBool (extend qBool (extend qBool empty))) qBool =
  fun fsG -> hd (tail (tail fsG))

let test_var0
  : exp_quotation #qBool (extend qBool empty) var0
  = QVar0

let test_var1
  : exp_quotation #qBool (extend qBool (extend qBool empty)) var1
  = QVarS QVar0

let test_var2
  : exp_quotation #qBool (extend qBool (extend qBool (extend qBool empty))) var2
  = QVarS (QVarS QVar0)

let test_constant
  : closed_exp_quotation (qBool ^-> qBool) constant
  = QLambda QTrue

let test_identity
  : closed_exp_quotation (qBool ^-> qBool) identity
  = QLambda QVar0

let test_thunked_id
  : closed_exp_quotation (qBool ^-> (qBool ^-> qBool)) thunked_id
  = QLambda (QLambda QVar0)

let test_proj1
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj1
  = QLambda (QLambda (QLambda (QVarS (QVarS QVar0))))

let test_proj2
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj2
  = QLambda (QLambda (QLambda (QVarS QVar0)))

let test_proj3
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj3
  = QLambda (QLambda (QLambda QVar0))

let test_apply_top_level_def
  : closed_exp_quotation (qBool ^-> qBool) apply_top_level_def
  = QLambda (QApp
              (QApp #_ #_ #_ #(fun _ x y -> y) // TODO: why cannot it infer this? is it difficult to unfold thunked_id?
                (QLambda (QLambda QVar0))
                QVar0)
              QTrue)

let test_apply_top_level_def'
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool) apply_top_level_def'
  = QLambda (QLambda (QApp
                      (QApp #_ #_ #_ #(fun _ x y -> y)
                        (QLambda (QLambda QVar0))
                        (QVarS QVar0))
                      QVar0))

let test_papply__top_level_def
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool) papply__top_level_def
  = QLambda (QApp #_ #_ #_ #(fun _ x y -> y)
              (QLambda (QLambda QVar0))
              QVar0)

let test_apply_arg
  : closed_exp_quotation ((qUnit ^-> qUnit) ^-> qUnit) apply_arg
  = QLambda (QApp QVar0 Qtt)

let test_apply_arg2
  : closed_exp_quotation ((qBool ^-> qBool ^-> qBool) ^-> qBool) apply_arg2
  = QLambda (QApp (QApp QVar0 QTrue) QFalse)


[@expect_failure]
let test_proj2'
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj2
  = QLambda (QLambda (QLambda QVar0))

let test_anif
  : closed_exp_quotation qBool anif
  = QIf QTrue QFalse QTrue

let test_negb
  : closed_exp_quotation (qBool ^-> qBool) negb
  = QLambda (QIf QVar0 QFalse QTrue)

let test_negb_pred
  : closed_exp_quotation ((qBool ^-> qBool) ^-> qBool ^-> qBool) negb_pred
  = QLambda (QLambda (QIf (QApp (QVarS QVar0) QVar0) QFalse QTrue))

let test_if2
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool) if2
  = QLambda (QLambda (QIf (QVarS QVar0) QFalse QVar0))

(** Because of the fancy types, now one needs a preprocessing tactic to
    get rid of the qTypes **)

let simplify_qType (x:term) : Tac term =
  (** TODO: why is F* not doing this automatically anyway? **)
  norm_term_env (top_env ()) [delta_only [`%fs_oexp;`%io_oexp; `%qUnit; `%qBool; `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Subtraction_Greater_Bang_At; `%get_rel; `%get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2];iota] x

[@@ (preprocess_with simplify_qType)]
let test_callback_return
  : closed_exp_quotation (qBool ^-> (qBool ^-> qBool)) callback_return
  = QLambda (QIf QVar0
                       (QLambda #_ #_ #_ #(fun fsG y -> hd fsG) (QVarS QVar0)) // TODO: why cannot it infer myf?
                       (QLambda #_ #_ #_ #(fun fsG z -> z) QVar0))

[@@ (preprocess_with simplify_qType)]
let test_callback_return'
  : closed_exp_quotation (qBool ^-> (qBool ^-> qBool)) callback_return'
  = QLambda (QIf QVar0
                       (QLambda #_ #_ #_ #(fun fsG y -> hd fsG) (QVarS QVar0))
                       (QLambda #_ #_ #_ #(fun fsG -> identity) QVar0)) // TODO: why does it not work to unfold identity here?

let test_make_pair
  : closed_exp_quotation (qBool ^-> qBool ^-> (qBool ^* qBool)) make_pair
  = QLambda (QLambda (QMkpair (QVarS QVar0) QVar0))

// TODO: why does this fail?
[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions ()
  : Tot (closed_exp_quotation ((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
                              pair_of_functions)
  by (norm [delta_only [`%pair_of_functions]];
      norm [delta_only [`%fs_oexp; `%qUnit; `%qBool; `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Subtraction_Greater_Bang_At; `%get_rel; `%get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2];iota];
     // trefl (); //this fails
     tadmit ())
  =  QMkpair
      (QLambda (QApp #_ #_ #_ #(fun _ x -> if x then false else true)
                  (QLambda (QIf QVar0 QFalse QTrue))
                  QVar0))
      (QLambda (QLambda QVar0))

let test_pair_of_functions2
  : closed_exp_quotation
    ((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
    pair_of_functions2
  = admit (); QMkpair // TODO
      (QLambda (QIf QVar0 QFalse QTrue))
      (QLambda (QLambda (QIf (QVarS QVar0) QFalse QVar0)))

let test_fst_pair
  : closed_exp_quotation (qBool) fst_pair
  = (QFst (QMkpair QTrue Qtt))

let test_wrap_fst
  : closed_exp_quotation ((qBool ^* qBool) ^-> qBool) wrap_fst
  = QLambda (QFst QVar0)

let test_wrap_fst_pa
  : closed_exp_quotation ((qBool ^* qBool) ^-> qBool) wrap_fst_pa
  = QLambda (QFst QVar0)

let test_snd_pair
  : closed_exp_quotation (qUnit) snd_pair
  = (QSnd (QMkpair QTrue Qtt))

let test_wrap_snd
  : closed_exp_quotation ((qBool ^* qUnit) ^-> qUnit) wrap_snd
  = QLambda (QSnd QVar0)

let test_wrap_snd_pa
  : closed_exp_quotation ((qBool ^* qUnit) ^-> qUnit) wrap_snd_pa
  = QLambda (QSnd QVar0)

open ExamplesIO

let test_u_return
  : closed_io_exp_quotation _ u_return
  = QReturn QTrue

let test_apply_io_return
  : closed_exp_quotation (qBool ^->!@ qBool) apply_io_return
  = QLambdaIO (QReturn QVar0)

let test_apply_read
  : closed_io_exp_quotation _ apply_read
  = QAppIO QRead Qtt

let test_apply_write_const
  : closed_io_exp_quotation _ apply_write_const
  = QAppIO QWrite QTrue

let test_apply_write
  : closed_exp_quotation _ apply_write
  = QLambdaIO (QAppIO QWrite QVar0)

let test_apply_io_bind_const
  : closed_io_exp_quotation _ apply_io_bind_const
  = QBind
      (QReturn QTrue)
      (QLambdaIO (QReturn QVar0))

let test_apply_io_bind_identity
  : closed_exp_quotation (qBool ^->!@ qBool) apply_io_bind_identity
  = QLambdaIO
      (QBind
        (QReturn QVar0)
        (QLambdaIO #_ #_ #_ #(fun fsG y -> return y) (QReturn QVar0)))

[@@ (preprocess_with simplify_qType)]
let test_apply_io_bind_pure_if ()
  : Tot (closed_exp_quotation (qBool ^->!@ qBool) apply_io_bind_pure_if)
    by (
      // TODO: why?
      norm [delta_only [`%apply_io_bind_pure_if]];
      norm [delta_only [`%op_Hat_Subtraction_Greater_Bang_At]];
      set_guard_policy Goal;
      split (); trefl ();
      explode (); trefl ();
      explode (); trefl ())
  = QLambdaIO
      (QBind
        (QReturn QVar0)
        (QLambdaIO #_ #_ #_ #(fun fsG y -> if y then return false else return true)
          (QIfIO QVar0
            (QReturn QFalse)
            (QReturn QTrue))))

let test_apply_io_bind_write
  : closed_exp_quotation _ apply_io_bind_write
  = QLambdaIO (
      QBind
         (QReturn QVar0)
         (QLambdaIO #_ #_ #_ #(fun fsG y -> write y)
           (QAppIO QWrite QVar0)))

let test_apply_io_bind_read_write
  : closed_io_exp_quotation _ apply_io_bind_read_write
  = QBind
     (QAppIO QRead Qtt)
     (QLambdaIO
       (QAppIO QWrite QVar0))

let test_apply_io_bind_read_write' ()
  : Tot (closed_io_exp_quotation _ apply_io_bind_read_write')
  = QBind (QAppIO QRead Qtt) QWrite

let test_apply_io_bind_read_if_write
  : closed_io_exp_quotation _ apply_io_bind_read_if_write
  = QBind
      (QAppIO QRead Qtt)
      (QLambdaIO
        (QIfIO QVar0
          (QAppIO QWrite QFalse)
          (QAppIO QWrite QTrue)))
