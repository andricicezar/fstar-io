module QExp

open QTyp

(** These helper functions are necessary to help F* do unification
    in such a way no VC is generated **)

unfold
val helper_var0 :
  g:typ_env ->
  a:qType ->
  fs_oexp (extend a g) a
let helper_var0 g a fsG = hd fsG

unfold
val helper_var1 : g:typ_env ->
                  a:qType ->
                  b:qType ->
                  fs_oexp (extend b (extend a g)) a
let helper_var1 g a b fsG = hd (tail fsG)
unfold
val helper_var2 : g:typ_env ->
                  a:qType ->
                  b:qType ->
                  c:qType ->
                  fs_oexp (extend c (extend b (extend a g))) a
let helper_var2 g a b c fsG = hd (tail (tail fsG))

unfold
val helper_unit : g:typ_env -> fs_oexp g qUnit
let helper_unit g _ = ()

unfold
val helper_true : g:typ_env -> fs_oexp g qBool
let helper_true g _ = true

unfold
val helper_false : g:typ_env -> fs_oexp g qBool
let helper_false g _ = false

unfold
val helper_app: #g : typ_env ->
                #a : qType ->
                #b : qType ->
                f :fs_oexp g (a ^-> b) ->
                x :fs_oexp g a ->
                fs_oexp g b
let helper_app f x fsG = (f fsG) (x fsG)

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
val helper_lambda : #g :typ_env ->
                #a :qType ->
                #b :qType ->
                f :fs_oexp g (a ^-> b) ->
                fs_oexp (extend a g) b
let helper_lambda #_ #_ f fsG = f (tail fsG) (hd fsG)

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type exp_quotation : #a:qType -> g:typ_env -> fs_oexp g a -> Type =
| Qtt         : #g : typ_env -> exp_quotation g (helper_unit g)
| QTrue       : #g : typ_env -> exp_quotation g (helper_true g)
| QFalse      : #g : typ_env -> exp_quotation g (helper_false g)

| QVar0       : #g : typ_env ->
                #a : qType ->
                exp_quotation _ (helper_var0 g a)

| QVar1       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                exp_quotation _ (helper_var1 g a b)
| QVar2       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #c : qType ->
                exp_quotation _ (helper_var2 g a b c)
(** we need a case for each deBrujin variable **)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oexp g (a ^-> b) ->
                #x : fs_oexp g a ->
                exp_quotation g f ->
                exp_quotation g x ->
                exp_quotation g (helper_app #_ #_ #_ f x)

| QIf         : #g : typ_env ->
                #a : qType ->
                #c : fs_oexp g qBool ->
                exp_quotation #qBool g c ->
                #t : fs_oexp g a ->
                exp_quotation g t ->
                #e : fs_oexp g a ->
                exp_quotation g e ->
                exp_quotation g (helper_if c t e)

| QLambda     : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oexp g (a ^-> b) ->
                exp_quotation (extend a g) (helper_lambda f) ->
                exp_quotation g f

unfold
let helper_oexp (#a:qType) (x:get_Type a) : fs_oexp empty a = fun _ -> x

type closed_exp_quotation (a:qType) (x:get_Type a) =
  exp_quotation #a empty (helper_oexp x)

open Examples

#push-options "--no_smt"

let test_identity
  : closed_exp_quotation (qBool ^-> qBool) identity
  = QLambda QVar0

let test_thunked_id
  : closed_exp_quotation (qBool ^-> (qBool ^-> qBool)) thunked_id
  = QLambda (QLambda QVar0)

let test_call_arg
  : closed_exp_quotation ((qUnit ^-> qUnit) ^-> qUnit) call_arg
  = QLambda (QApp QVar0 Qtt)

let test_call_arg2
  : closed_exp_quotation ((qBool ^-> qBool ^-> qBool) ^-> qBool) call_arg2
  = QLambda (QApp (QApp QVar0 QTrue) QFalse)

let test_proj1
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj1
  = QLambda (QLambda (QLambda QVar2))

let test_proj2
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj2
  = QLambda (QLambda (QLambda QVar1))

let test_proj3
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool ^-> qBool) proj3
  = QLambda (QLambda (QLambda QVar0))

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

let test_if2
  : closed_exp_quotation (qBool ^-> qBool ^-> qBool) if2
  = QLambda (QLambda (QIf QVar1 QFalse QVar0))

let test_negb_pred
  : closed_exp_quotation ((qBool ^-> qBool) ^-> qBool ^-> qBool) negb_pred
  = QLambda (QLambda (QIf (QApp QVar1 QVar0) QFalse QTrue))

open FStar.Tactics

(** Because of the fancy types, now one needs a preprocessing tactic to
    get rid of the qTypes **)

let simplify_qType (x:term) : Tac term =
  (** TODO: why is F* not doing this automatically anyway? **)
  norm_term_env (top_env ()) [delta_only [`%qUnit; `%qBool; `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%get_rel; `%get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2];iota] x

[@@ (preprocess_with simplify_qType)]
let test_callback_return
  : closed_exp_quotation (qBool ^-> (qBool ^-> qBool)) callback_return
  = QLambda (QIf QVar0
                       (QLambda #_ #_ #_ #(fun fsG y -> hd fsG) QVar1) // TODO: why cannot it infer myf?
                       (QLambda #_ #_ #_ #(fun fsG z -> z) QVar0))

[@@ (preprocess_with simplify_qType)]
let test_callback_return'
  : closed_exp_quotation (qBool ^-> (qBool ^-> qBool)) callback_return'
  = QLambda (QIf QVar0
                       (QLambda #_ #_ #_ #(fun fsG y -> hd fsG) QVar1)
                       (QLambda #_ #_ #_ #(fun fsG -> identity) QVar0)) // TODO: why does it not work to unfold identity here?

(**
let project_equiv #g #a (qa:typ_quotation a) (s:fs_oexp g a) (qs:exp_quotation g s) :
  Lemma (s `equiv qa` (project_exp q)) = ()

  match qs with
  | Qtt -> equiv_qUnit g
  | QApp #_ #a #b #f qf #x qx ->
      project_equiv (QArr ? qa) f qf;
      project_equiv ? x qx;
      equiv_app g ? qa f (project_exp f) x (project_exp x)
**)
