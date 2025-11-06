module QExp

open QTyp

(** typ_env is a typing environment: variables to F* types **)
type typ_env = nat -> option Type
val empty : typ_env
val extend (t:Type) (g:typ_env) : typ_env

(** eval_env is an evaluation environment: variables to F* values **)
val eval_env (g:typ_env) : Type u#0
val hd : #t:Type -> #g:_ -> eval_env (extend t g) -> t
val stack : #g:_ -> fsG:eval_env g -> #t:Type -> t -> eval_env (extend t g)
val tail : #t:Type -> #g:_ -> eval_env (extend t g) -> eval_env g

type fs_oexp (g:typ_env) (a:Type) =
  eval_env g -> a

(** These helper functions are necessary to help F* do unification
    in such a way no VC is generated **)

unfold
let helper_var0 :
  g:typ_env ->
  a:Type ->
  fs_oexp (extend a g) a
= fun g a fsG -> hd fsG

unfold
let helper_var1 : g:typ_env ->
                  a:Type ->
                  b:Type ->
                  fs_oexp (extend b (extend a g)) a
= fun g a b fsG -> hd (tail #b fsG)

unfold
let helper_var2 : g:typ_env ->
                  a:Type ->
                  b:Type ->
                  c:Type ->
                  fs_oexp (extend c (extend b (extend a g))) a
= fun g a b c fsG -> hd (tail #b (tail #c fsG))

unfold
let helper_unit : g:typ_env -> fs_oexp g unit
= fun g _ -> ()

unfold
let helper_true : g:typ_env -> fs_oexp g bool
= fun g _ -> true

unfold
let helper_false : g:typ_env -> fs_oexp g bool
= fun g _ -> false

unfold
let helper_app: #g : typ_env ->
                #a : Type ->
                #b : Type ->
                f :fs_oexp g (a -> b) ->
                x :fs_oexp g a ->
                fs_oexp g b
= fun f x fsG -> (f fsG) (x fsG)

unfold
let helper_if : #g :typ_env ->
                #a :Type ->
                c   : fs_oexp g bool ->
                t   : fs_oexp g a ->
                e   : fs_oexp g a ->
                fs_oexp g a
= fun c t e fsG ->
    if c fsG then t fsG else e fsG

unfold
let helper_lambda : #g :typ_env ->
                #a :Type ->
                #b :Type ->
                f :fs_oexp g (a -> b) ->
                fs_oexp (extend a g) b
= fun #_ #a f fsG -> f (tail #a fsG) (hd fsG)

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type exp_quotation : #a:Type -> type_quotation a -> g:typ_env -> fs_oexp g a -> Type =
| Qtt         : #g : typ_env -> exp_quotation #_ QUnit g (helper_unit g)
| QTrue       : #g : typ_env -> exp_quotation #_ QBool g (helper_true g)
| QFalse      : #g : typ_env -> exp_quotation #_ QBool g (helper_false g)

| QVar0       : #g : typ_env ->
                #a : Type ->
                #qa : type_quotation a ->
                exp_quotation #a qa _ (helper_var0 g a)

| QVar1       : #g : typ_env ->
                #a : Type ->
                #qa : type_quotation a ->
                #b : Type ->
                exp_quotation #a qa _ (helper_var1 g a b)
| QVar2       : #g : typ_env ->
                #a : Type ->
                #qa : type_quotation a ->
                #b : Type ->
                #c : Type ->
                exp_quotation #a qa _ (helper_var2 g a b c)
(** we need a case for each deBrujin variable **)

| QApp        : #g : typ_env ->
                #a : Type ->
                #qa : type_quotation a ->
                #b : Type ->
                #qb : type_quotation b ->
                #f : fs_oexp g (a -> b) ->
                exp_quotation #_ (qa ^-> qb) g f ->
                #x : fs_oexp g a ->
                exp_quotation #_ qa g x ->
                exp_quotation #b qb g (helper_app #_ #_ #_ f x)

| QIf         : #g : typ_env ->
                #a : Type ->
                #qa : type_quotation a ->
                #c : fs_oexp g bool ->
                exp_quotation #_ QBool g c ->
                #t : fs_oexp g a ->
                exp_quotation #_ qa g t ->
                #e : fs_oexp g a ->
                exp_quotation #_ qa g e ->
                exp_quotation #_ qa g (helper_if c t e)

| QLambda     : #g : typ_env ->
                #a : Type ->
                #b : Type ->
                #qa : type_quotation a ->
                #qb : type_quotation b ->
                #f : fs_oexp g (a -> b) ->
                exp_quotation #b qb (extend a g) (helper_lambda f) ->
                exp_quotation #_ (qa ^-> qb) g f

unfold
let helper_oexp (x:'a) : fs_oexp empty 'a = fun _ -> x

type closed_exp_quotation #a (qa:type_quotation a) (x:a) =
  exp_quotation qa empty (helper_oexp x)

open Examples

#push-options "--no_smt"

let test_identity
  : closed_exp_quotation (QBool ^-> QBool) identity
  = QLambda QVar0

let test_thunked_id
  : closed_exp_quotation (QBool ^-> (QBool ^-> QBool)) thunked_id
  = QLambda (QLambda QVar0)

let test_call_arg
  : closed_exp_quotation ((QUnit ^-> QUnit) ^-> QUnit) call_arg
  = QLambda (QApp QVar0 Qtt)

let test_call_arg2
  : closed_exp_quotation ((QBool ^-> QBool ^-> QBool) ^-> QBool) call_arg2
  = QLambda (QApp (QApp QVar0 QTrue) QFalse)

let test_proj1
  : closed_exp_quotation (QBool ^-> QBool ^-> QBool ^-> QBool) proj1
  = QLambda (QLambda (QLambda QVar2))

let test_proj2
  : closed_exp_quotation (QBool ^-> QBool ^-> QBool ^-> QBool) proj2
  = QLambda (QLambda (QLambda QVar1))

let test_proj3
  : closed_exp_quotation (QBool ^-> QBool ^-> QBool ^-> QBool) proj3
  = QLambda (QLambda (QLambda QVar0))

[@expect_failure]
let test_proj2'
  : closed_exp_quotation (QBool ^-> QBool ^-> QBool ^-> QBool) proj2
  = QLambda (QLambda (QLambda QVar0))

let test_anif
  : closed_exp_quotation QBool anif
  = QIf QTrue QFalse QTrue

let test_negb
  : closed_exp_quotation (QBool ^-> QBool) negb
  = QLambda (QIf QVar0 QFalse QTrue)

let test_if2
  : closed_exp_quotation (QBool ^-> QBool ^-> QBool) if2
  = QLambda (QLambda (QIf QVar1 QFalse QVar0))

let test_negb_pred
  : closed_exp_quotation ((QBool ^-> QBool) ^-> QBool ^-> QBool) negb_pred
  = QLambda (QLambda (QIf (QApp QVar1 (QVar0 #_ #_ #QBool)) QFalse QTrue)) // TODO: why does one have to pass QBool?

let test_callback_return
  : closed_exp_quotation (QBool ^-> (QBool ^-> QBool)) callback_return
  = QLambda (QIf QVar0
                       (QLambda #_ #_ #_ #_ #_ #(fun fsG y -> hd fsG) QVar1) // TODO: why cannot it infer myf?
                       (QLambda #_ #_ #_ #_ #_ #(fun fsG z -> z) QVar0))

let test_callback_return'
  : closed_exp_quotation (QBool ^-> (QBool ^-> QBool)) callback_return'
  = QLambda (QIf QVar0
                       (QLambda #_ #_ #_ #_ #_ #(fun fsG y -> hd fsG) QVar1)
                       (QLambda #_ #_ #_ #_ #_ #(fun fsG -> identity) QVar0)) // TODO: why does it not work to unfold identity here?

(**
let project_equiv #g #a (qa:typ_quotation a) (s:fs_oexp g a) (qs:exp_quotation g s) :
  Lemma (s `equiv qa` (project_exp q)) = ()

  match qs with
  | Qtt -> equiv_QUnit g
  | QApp #_ #a #b #f qf #x qx ->
      project_equiv (QArr ? qa) f qf;
      project_equiv ? x qx;
      equiv_app g ? qa f (project_exp f) x (project_exp x)
**)
