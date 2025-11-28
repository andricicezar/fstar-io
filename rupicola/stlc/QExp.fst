module QExp

open FStar.Tactics
open QTyp

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
                f :fs_oval g (a ^-> b) ->
                fs_oval (extend a g) b
let helper_lambda #_ #_ f fsG = f (tail fsG) (hd fsG)

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

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type value_quotation : #a:qType -> g:typ_env -> fs_oval g a -> Type =
| Qtt         : #g : typ_env -> value_quotation g (helper_unit g)

| QVar0       : #g : typ_env ->
                #a : qType ->
                value_quotation (extend a g) (helper_var0 g a)

| QVarS       : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #x : fs_oval g a ->
                value_quotation g x ->
                value_quotation (extend b g) (helper_varS g a b x)

| QAppGhost   : #g : typ_env ->
                #a : qType ->
                #f : fs_oval g (a ^-> qUnit) -> (** This has to be Tot. If it is GTot unit, F* can treat it as Pure unit **)
                #x : fs_oval g a ->
                value_quotation #qUnit g (helper_app #_ #_ #_ f x)

| QApp        : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^-> b) ->
                #x : fs_oval g a ->
                value_quotation g f ->
                value_quotation g x ->
                value_quotation g (helper_app #_ #_ #_ f x)

| QLambda     : #g : typ_env ->
                #a : qType ->
                #b : qType ->
                #f : fs_oval g (a ^-> b) ->
                value_quotation (extend a g) (helper_lambda f) ->
                value_quotation g f

| QTrue       : #g : typ_env -> value_quotation g (helper_true g)
| QFalse      : #g : typ_env -> value_quotation g (helper_false g)
| QIf         : #g : typ_env ->
                #a : qType ->
                #c : fs_oval g qBool ->
                value_quotation g c ->
                #t : fs_oval g a ->
                value_quotation g t ->
                #e : fs_oval g a ->
                value_quotation g e ->
                value_quotation g (helper_if c t e)

| QMkpair   : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #x : fs_oval g a ->
              #y : fs_oval g b ->
              value_quotation g x ->
              value_quotation g y ->
              value_quotation g (helper_pair x y)
| QFst      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              value_quotation g p ->
              value_quotation g (helper_fst p)
| QSnd      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g (a ^* b) ->
              value_quotation g p ->
              value_quotation g (helper_snd p)
| QInl      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g a ->
              value_quotation g p ->
              value_quotation g (helper_inl b p)
| QInr      : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #p : fs_oval g b ->
              value_quotation g p ->
              value_quotation g (helper_inr a p)
| QCase     : #g : typ_env ->
              #a : qType ->
              #b : qType ->
              #c : qType ->
              #cond : fs_oval g (a ^+ b) ->
              value_quotation g cond ->
              #inlc : fs_oval (extend a g) c ->
              value_quotation _ inlc ->
              #inrc : fs_oval (extend b g) c ->
              value_quotation _ inrc ->
              value_quotation g (helper_case cond inlc inrc)

let (⊢) (#a:qType) (g:typ_env) (x:fs_oval g a) =
  value_quotation g x

unfold
let helper_oexp (#a:qType) (x:get_Type a) : fs_oval empty a = fun _ -> x

let (⊩) (a:qType) (x:get_Type a) =
  value_quotation #a empty (helper_oexp x)

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

let test_var3
  : (extend qBool (extend qBool (extend qBool (extend qBool empty)))) ⊢ var3
  = QVarS (qVar2)

let test_constant
  : (qBool ^-> qBool) ⊩ constant
  = QLambda QTrue

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
                (QLambda #_ #_ #_ #(fun _ x y -> y) (QLambda QVar0))
                QVar0)
              QTrue)

let test_apply_top_level_def'
  : (qBool ^-> qBool ^-> qBool) ⊩ apply_top_level_def'
  = QLambda (QLambda (QApp
                       (QApp
                          (QLambda (QLambda #_ #_ #_ #(fun _ y -> y) QVar0))
 //                       (QLambda #_ #_ #_ #(fun _ x y -> y) (QLambda QVar0))
                          qVar1)
                       QVar0))

let test_papply__top_level_def
  : (qBool ^-> qBool ^-> qBool) ⊩ papply__top_level_def
  = QLambda (QApp
              (QLambda #_ #_ #_ #(fun _ x y -> y) (QLambda QVar0))
              QVar0)

let test_apply_arg
  : ((qUnit ^-> qUnit) ^-> qUnit) ⊩ apply_arg
  = QLambda (QApp QVar0 Qtt)

let test_apply_arg2
  : ((qBool ^-> qBool ^-> qBool) ^-> qBool) ⊩ apply_arg2
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

let test_if2
  : (qBool ^-> qBool ^-> qBool) ⊩ if2
  = QLambda (QLambda (QIf qVar1 QFalse QVar0))

(** Because of the fancy types, now one needs a preprocessing tactic to
    get rid of the qTypes **)

let l_to_r_fsG () : Tac unit = // TODO: merge this in simplify_qType
   l_to_r [`lem_stack_hd; `lem_stack_index; `lem_stack_tail_hd; `tail_stack_inverse]

let simplify_qType (x:term) : Tac term =
  (** TODO: why is F* not doing this automatically anyway? **)
  norm_term_env (top_env ()) [delta_only [`%fs_oval; `%qUnit; `%qBool; `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%op_Hat_Plus; `%get_rel; `%get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2];iota;simplify] x

[@@ (preprocess_with simplify_qType)]
let test_callback_return
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return
  = QLambda (QIf QVar0
                 (QLambda #_ #_ #_ #(fun fsG y -> hd fsG) qVar1)
                 (QLambda #_ #_ #_ #(fun fsG z -> z) QVar0))

[@@ (preprocess_with simplify_qType)]
let test_callback_return'
  : (qBool ^-> (qBool ^-> qBool)) ⊩ callback_return'
  = QLambda (QIf QVar0
                 (QLambda #_ #_ #_ #(fun fsG y -> hd fsG) qVar1)
                 (QLambda #_ #_ #_ #(fun fsG -> identity) QVar0)) // TODO: why does it not work to unfold identity here?

let test_make_pair
  : (qBool ^-> qBool ^-> (qBool ^* qBool)) ⊩ make_pair
  = QLambda (QLambda (QMkpair qVar1 QVar0))

[@@ (preprocess_with simplify_qType)]
let test_pair_of_functions ()
  : Tot (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
                            ⊩ pair_of_functions)
  by (norm [delta_only [`%pair_of_functions]];
      norm [delta_only [`%fs_oval; `%qUnit; `%qBool; `%op_Hat_Subtraction_Greater; `%op_Hat_Star; `%get_rel; `%get_Type; `%Mkdtuple2?._1;`%Mkdtuple2?._2];iota];
     // trefl (); //TODO: why does this fail?
     tadmit ())
  =  QMkpair
      (QLambda (QApp
                  (QLambda #_ #_ #_ #(fun _ x -> if x then false else true) (QIf QVar0 QFalse QTrue))
                  QVar0))
      (QLambda (QLambda #_ #_ #_ #(fun _ y -> y) QVar0))

let test_pair_of_functions2
  : (((qBool ^-> qBool) ^* (qBool ^-> qBool ^-> qBool))
    ⊩ pair_of_functions2)
  = admit (); QMkpair // TODO
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

let qLet #g (#a #b:qType) (#x:fs_oval g a) (#f:fs_oval g (a ^-> b))
  (qx : value_quotation g x) (qf : value_quotation g f) :
  value_quotation g (fun fsG -> let y = x fsG in f fsG y) =
  QApp qf qx

let test_a_few_lets
  : (qBool ^-> qUnit) ⊩ a_few_lets
  = QLambda
     (qLet (QMkpair QVar0 QVar0) (QLambda
     (qLet qVar1 (QLambda
     (qLet (QFst qVar1) (QLambda
     (qLet (QMkpair qVar1 QVar0) (QLambda
     Qtt))))))))

let test_inl_true
  : (qBool ^+ qUnit) ⊩ inl_true
  = QInl QTrue

let test_inr_unit
  : (qBool ^+ qUnit) ⊩ inr_unit
  = QInr Qtt

[@@ (preprocess_with simplify_qType)]
let test_return_either ()
  : (qBool ^-> (qUnit ^+ qUnit)) ⊩ return_either
  by (norm [delta_only [`%get_Type;`%Mkdtuple2?._1; `%return_either]; iota];
     // trefl (); -- TODO: this fails even if it is an equality.
     tadmit ())
  = QLambda (QIf QVar0 (QInl Qtt) (QInr Qtt))

let test_match_either ()
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either
  by (l_to_r_fsG (); norm [delta_only [`%match_either]])
  = QLambda (QCase QVar0 QVar0 QVar0)

[@@ (preprocess_with simplify_qType)]
let test_match_either' ()
  : ((qBool ^+ qBool) ^-> qBool) ⊩ match_either'
  by (norm [delta_only [`%get_Type;`%Mkdtuple2?._1; `%match_either']; iota];
      l_to_r_fsG ();
     tadmit ()) // TODO: expected failure. any way to sort the cases?
  = QLambda (QCase QVar0 QVar0 QVar0)

let test_match_either_arg ()
  : (((qBool ^+ qBool) ^-> qBool ^-> qBool) ⊩ match_either_arg)
  by (l_to_r_fsG (); norm [delta_only [`%match_either_arg]]; dump "H")
  = QLambda (QLambda (
       QCase
         qVar1
         QVar0
         qVar1))
