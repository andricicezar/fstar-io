module QExp

open FStar.Tactics.V2

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

(* Local helper to convert pure_wp' to pure_wp by proving monotonicity *)
private unfold
let mk_pure_wp #a (wp:pure_wp' a{M.is_monotonic wp}) : pure_wp a =
  M.intro_pure_wp_monotonicity wp; wp

(** Typing environment **)
type env = var -> option Type0
let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:Type0) (g:env)
  : env
  = fun y -> if y = 0 then Some t
          else g (y-1)

(** F* evaluation environment **)
module FE = FStar.FunctionalExtensionality

type fs_env g =
  FE.restricted_t (x:var{Some? (g x)}) (fun x -> Some?.v (g x))

unfold
val fs_hd : #g:_ -> #t:Type -> fs_env (extend t g) -> t
let fs_hd  fsG = fsG 0

unfold
val fs_stack : #g:_ -> fsG:fs_env g -> #t:Type -> t -> fs_env (extend t g)
let fs_stack #g fsG #t fs_v =
  FE.on_dom
    (x:var{Some? ((extend t g) x)})
    #(fun x -> (Some?.v ((extend t g) x)))
    (fun y ->
      if y = 0 then fs_v else fsG (y-1))

val fs_tail : #t:Type -> #g:_ -> fs_env (extend t g) -> fs_env g
let fs_tail #t #g fsG =
  FE.on_dom
    (x:var{Some? (g x)})
    #(fun x -> Some?.v (g x))
    (fun y -> fsG (y+1))

val lem_hd_stack #t #g (fsG:fs_env g) (v:t)
  : Lemma (
 // (fs_hd fsG == fs_hd (fs_tail (fs_stack fsG v))) /\
   fs_hd (fs_stack fsG v) == v)
  [SMTPat (fs_hd (fs_stack fsG v))]
let lem_hd_stack fsG v = ()


val lem_tail_stack_inverse #g (fsG:fs_env g) #t (x:t)
  : Lemma (fs_tail (fs_stack fsG x) == fsG)
  [SMTPat (fs_tail (fs_stack fsG x))]
let lem_tail_stack_inverse #g fsG #t v = admit ()

type spec_env (g:env) =
  fs_env g -> pure_pre

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (pre:spec_env g) =
  fsG:fs_env g -> Pure a (requires (pre fsG)) (ensures (fun _ -> True))

val helper_weaken : #g:env ->
                    #a:Type u#a ->
                    b:Type0 ->
                    preX:spec_env g ->
                    x:fs_oexp g a preX ->
                    fs_oexp (extend b g) a (fun fsG -> preX (fs_tail fsG))
let helper_weaken #g #a b preX x fsG =
  x (fs_tail fsG)

unfold
val helper_var0 : g:env ->
                 a:Type ->
                 fs_oexp (extend a g) a (fun _ -> True)
let helper_var0 g a fsG =
  fs_hd fsG

unfold
val helper_unit : g:env -> fs_oexp g unit (fun _ -> True)
let helper_unit g = fun _ -> ()

unfold
val helper_true : g:env -> fs_oexp g bool (fun _ -> True)
let helper_true g = fun _ -> true

unfold
val helper_false : g:env -> fs_oexp g bool (fun _ -> True)
let helper_false g = fun _ -> false

val pre_app:     #g :env ->
                preF : spec_env g ->
                preX : spec_env g ->
                spec_env g
let pre_app #_ preF preX =
  (fun fsG -> preF fsG /\ preX fsG)

unfold
val helper_app: #g :env ->
                #a :Type ->
                #b :Type ->
                #preF : spec_env g ->
                f :fs_oexp g (a -> b) preF ->
                #preX : spec_env g ->
                x :fs_oexp g a preX ->
                fs_oexp g b (pre_app preF preX)

let helper_app #_ #_ #_ #preF f #preX x =
  fun fsG ->
    (f fsG) (x fsG)

val pre_if : #g :env ->
                #preC : spec_env g ->
                c   : fs_oexp g bool preC ->
                preT : spec_env g ->
                preE : spec_env g ->
                spec_env g
let pre_if #_ #preC c preT preE =
  (fun fsG -> preC fsG /\ (c fsG ==> preT fsG) /\ ((~(c fsG)) ==> preE fsG))

unfold
val helper_if : #g :env ->
                #a :Type ->
                #preC : spec_env g ->
                c   : fs_oexp g bool preC ->
                #preT : spec_env g ->
                t   : fs_oexp g a preT ->
                #preE : spec_env g ->
                e   : fs_oexp g a preE ->
                fs_oexp g a (pre_if c preT preE)
let helper_if #_ #_ #preC c #preT t #preE e =
  fun fsG ->
    if c fsG then t fsG else e fsG

unfold
val pre_lambda_tot : #g :env ->
                #a :Type ->
                preBody:spec_env (extend a g) ->
                spec_env g

let pre_lambda_tot #g #a preBody fsG : pure_pre =
  forall x. preBody (fs_stack fsG x)

val helper_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                #preBody:spec_env (extend a g) ->
                body :fs_oexp (extend a g) b preBody ->
                fs_oexp g (a -> b) (pre_lambda_tot preBody)
let helper_lambda #g #a #b #preBody body fsG =
  (fun x -> body (fs_stack fsG x))

type eff_fun (#a:Type) (#b:Type) (preFun: a -> pure_pre) (postFun: a -> pure_post b) = x:a -> Pure b (requires (preFun x)) (ensures (postFun x))

unfold
val pre_lambda_wp :
  #g :env ->
  #a :Type ->
  #b :Type ->
  #preBody : spec_env (extend a g) ->
  fs_oexp (extend a g) b preBody ->
  preFun : (a -> pure_pre) ->
  postFun : (a -> pure_post b) ->
  spec_env g

let pre_lambda_wp #g #a #b #preBody body preFun postFun fsG : pure_pre =
  (forall (x: a).
    preBody (fs_stack fsG x) /\
    preFun x /\
    (forall (r: b). postFun x r))

val helper_lambda_wp :
  #g : env ->
  #a : Type ->
  #b : Type ->
  #preBody : spec_env (extend a g) ->
  body : fs_oexp (extend a g) b preBody ->
  preFun : (a -> pure_pre) ->
  postFun : (a -> pure_post b) ->
  fs_oexp g (eff_fun preFun postFun) (pre_lambda_wp body preFun postFun)

let helper_lambda_wp #g #a #b #preBody body preFun postFun fsG =
  fun (x: a) -> body (fs_stack fsG x)

unfold
val helper_refv: #g:env ->
                #a:Type ->
                #ref1:(a -> Type0) ->
                ref2:(a -> Type0) ->
                preV:spec_env g ->
                v:fs_oexp g (x:a{ref1 x}) preV ->
                fs_oexp g (x:a{ref2 x}) (fun fsG -> preV fsG /\ ref2 (v fsG))
let helper_refv ref2 preV v =
  fun fsG -> v fsG

unfold
val helper_seq :#g:env ->
                #ref1:Type0 ->
                preV:spec_env g ->
                v:fs_oexp g (_:unit{ref1}) preV ->
                #a:Type ->
                preK:spec_env g ->
                k:fs_oexp g a preK ->
                fs_oexp g a
                  (fun fsG -> preV fsG /\ (ref1 ==> preK fsG))
let helper_seq preV v preK k =
  fun fsG ->
    v fsG ; k fsG

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type typing : #a:Type -> g:env -> pre:spec_env g -> fs_oexp g a pre -> Type =
| Qtt       : #g:env ->  typing g _ (helper_unit g)
| QTrue       : #g:env ->  typing g _ (helper_true g)
| QFalse      : #g:env ->  typing g _ (helper_false g)

| QAxiom      : #g : env ->
                #a : Type ->
                typing (extend a g) _ (helper_var0 g a)

| QWeaken      : #g : env ->
                #a : Type ->
                #b : Type ->
                #preX : spec_env g ->
                #x : fs_oexp g a preX ->
                typing g preX x ->
                typing (extend b g) _ (helper_weaken b preX x)

| QApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #preF : spec_env g ->
                #f :fs_oexp g (a -> b) preF ->
                cf:typing g preF f ->
                #preX : spec_env g ->
                #x :fs_oexp g a preX ->
                cx:typing g preX x ->
                typing #b g _ (helper_app #_ #_ #_ #preF f x)

| QIf         : #g :env ->
                #a :Type ->
                #preC : spec_env g ->
                #c   : fs_oexp g bool preC ->
                cc   : typing g preC c ->
                #preT : spec_env g ->
                #t   : fs_oexp g a preT ->
                ct   : typing g preT t ->
                #preE : spec_env g ->
                #e   : fs_oexp g a preE ->
                ce   : typing g preE e ->
                typing g _ (helper_if c t e)

| QLambdaTot  : #g :env ->
                #a :Type ->
                #b :Type ->
                #preBody:spec_env (extend a g) ->
                #body :fs_oexp (extend a g) b preBody ->
                cf:typing #b (extend a g) preBody body ->
                typing g (pre_lambda_tot #g #a preBody) (helper_lambda body)

| QLambdaWP :
  #g : env ->
  #a : Type ->
  #b : Type ->
  #preBody : spec_env (extend a g) ->
  #body : fs_oexp (extend a g) b preBody ->
  typing #b (extend a g) preBody body ->
  preFun : (a -> pure_pre) ->
  postFun : (a -> pure_post b) ->
  typing g (pre_lambda_wp body preFun postFun) (helper_lambda_wp body preFun postFun)

| QRefinement : #g:env ->
                #a:Type ->
                #ref1:(a -> Type0) ->
                ref2:(a -> Type0) ->
                #preV:spec_env g ->
                #v:fs_oexp g (x:a{ref1 x}) preV ->
                typing #(x:a{ref1 x}) g preV v ->
                typing #(x:a{ref2 x}) g _ (helper_refv ref2 preV v)

| QSeq        : #g:env ->
                ref1:Type0 ->
                #preV:spec_env g ->
                #v:fs_oexp g (_:unit{ref1}) preV ->
                typing #(_:unit{ref1}) g preV v ->

                #a:Type ->
                #preK:spec_env g ->
                #k:fs_oexp g a preK ->
                typing #a g preK k ->
                typing #a g _ (helper_seq preV v preK k)

// val qLambdaTot: #g :env ->
//                 #a :Type ->
//                 #b :Type ->
//                 #preBody:spec_env (extend a g) ->
//                 #body :fs_oexp (extend a g) b preBody ->
//                 cf:typing #b (extend a g) preBody body ->
//                 typing g (pre_lambda_tot preBody) (helper_lambda body)

// let qLambdaTot #g #a #b #wpBody #body cf =
//   QLambdaWP cf (fun _ -> True) (fun _ _ -> True)

// DO NOT MARK WITH UNFOLD
let helper_oexp (x:'a) (#pre:spec_env empty) (#_:squash (forall fsG. pre fsG))
  : fs_oexp empty 'a pre
  = fun _ -> x

type typing_closed #a (#pre:spec_env empty) (x:a) =
  proof:squash (forall fsG. pre fsG) -> typing empty pre (helper_oexp x #pre #proof)

type typing_debug #a (pre:spec_env empty) (x:a) =
  typing_closed #a #pre x

let (⊢) (#a:Type)(g:env) (#pre:spec_env g) (x:fs_oexp g a pre) =
  typing g pre x

let (⊩) (a:Type) (x:a) =
  pre:spec_env empty & (proof:squash (forall fsG. pre fsG) -> typing #a empty pre (helper_oexp x #pre #proof))

let mk_dturniqet #a #x (#pre:spec_env empty) (thk_dv:(proof:squash (forall fsG. pre fsG) -> typing #a empty pre (helper_oexp x #pre #proof))) : a ⊩ x =
  (| _, thk_dv |)


let simplify_stack_ops () : Tac unit =
   l_to_r [`lem_hd_stack; `lem_tail_stack_inverse]

let simplify_via_norm () : Tac unit =
  norm [delta_only [`%helper_lambda; `%helper_lambda_wp; `%helper_oexp; 
                    `%helper_app; `%helper_if; `%helper_seq; `%helper_weaken;
                    `%helper_var0; `%helper_refv; 
                    `%pre_app; `%pre_if; `%pre_lambda_tot; `%pre_lambda_wp;
                    `%fs_stack; `%fs_hd; `%fs_tail;
                    `%mk_pure_wp;
                    `%FE.on_dom; `%pure_return; `%pure_return0];
        zeta_full; // TODO: what recursive function is unfolded using this? is it something opaque?
        unascribe // TODO: why is this necessary?
        ];
  let _ = repeat forall_intro in
  or_else trivial trefl // TODO: why is it not always trefl?


let qVar1 #g #a #b : typing #a (extend b (extend a g)) _ _ =
  QWeaken QAxiom

let qVar2 #g #a #b #c : (extend c (extend b (extend a g))) ⊢ (fun fsG -> fs_hd (fs_tail (fs_tail fsG))) =
  QWeaken qVar1

#push-options "--no_smt"

open Examples

let test_ut_unit ()
  : unit ⊩ ut_unit
  = mk_dturniqet (fun _ -> Qtt)

let test_ut_true
  : bool ⊩ ut_true
  = mk_dturniqet (fun _ -> QTrue)

let test_ut_false
  : bool ⊩ ut_false
  = mk_dturniqet (fun _ -> QFalse)

// val var0 : fs_oexp (extend bool empty) bool 
// let var0 fsG = fun _ -> hd fsG

// val var1 : fs_oexp (extend bool (extend bool empty)) bool
// let var1 fsG = hd (tail fsG)

// let var2 : fs_oexp (extend bool (extend bool (extend bool empty))) bool =
//   fun fsG -> hd (tail (tail fsG))

// let test_var0
//   : (extend bool empty) ⊢ var0
//   = QAxiom

// let test_var1
//   : (extend bool (extend bool empty)) ⊢ var1
//   = qVar1

// let test_var2
//   : (extend bool (extend bool (extend bool empty))) ⊢ var2
//   = qVar2

let test_constant
  : ((bool -> bool) ⊩ constant)
  = mk_dturniqet (fun _ -> QLambdaTot QTrue)

let test_constant'
  : ((bool -> bool) ⊩ constant)
  = mk_dturniqet (fun _ -> QLambdaTot (QWeaken QTrue))

let test_identity
  : (bool -> bool) ⊩ identity
  = mk_dturniqet (fun _ -> QLambdaTot QAxiom)

let test_thunked_id
  : (bool -> (bool -> bool)) ⊩ thunked_id
  = mk_dturniqet (fun _ -> QLambdaTot (QLambdaTot QAxiom))

let test_proj1 ()
  : Tot ((bool -> bool -> bool -> bool) ⊩ proj1)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaTot (QLambdaTot (QLambdaTot qVar2)))

let test_proj2 ()
  : Tot ((bool -> bool -> bool -> bool) ⊩ proj2)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaTot (QLambdaTot (QLambdaTot qVar1)))

let test_proj3
  : (bool -> bool -> bool -> bool) ⊩ proj3
  = mk_dturniqet (fun _ -> QLambdaTot (QLambdaTot (QLambdaTot QAxiom)))

let test_apply_top_level_def ()
  : Tot ((bool -> bool) ⊩ apply_top_level_def)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #apply_top_level_def (
      fun _ -> QLambdaTot (QApp
              (QApp
                (QLambdaTot (QLambdaTot QAxiom))
                QAxiom)
              QTrue))

let test_apply_top_level_def' ()
  : Tot ((bool -> bool -> bool) ⊩ apply_top_level_def')
  by (simplify_via_norm ())
  = mk_dturniqet #_ #apply_top_level_def' (
      fun _ -> QLambdaTot (QLambdaTot (QApp
                       (QApp
                          (QLambdaTot (QLambdaTot QAxiom))
                          qVar1)
                       QAxiom)))

let test_papply__top_level_def ()
  : Tot ((bool -> bool -> bool) ⊩ papply__top_level_def)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #papply__top_level_def (
      fun _ -> QLambdaTot (QApp
              (QLambdaTot (QLambdaTot QAxiom))
              QAxiom))

let test_apply_arg
  : ((unit -> unit) -> unit) ⊩ apply_arg
  = mk_dturniqet (fun _ -> QLambdaTot (QApp QAxiom Qtt))

let test_apply_arg2 ()
  : Tot (((bool -> bool -> bool) -> bool) ⊩ apply_arg2)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaTot (QApp (QApp QAxiom QTrue) QFalse))

let test_papply_arg2 ()
  : Tot (((bool -> bool -> bool) -> bool -> bool) ⊩ papply_arg2)
  by (simplify_via_norm ())
  = mk_dturniqet (fun _ -> QLambdaTot (QApp QAxiom QTrue))

[@expect_failure]
let test_proj2'
  : (bool -> bool -> bool -> bool) ⊩ proj2
  = mk_dturniqet (fun _ -> QLambdaTot (QLambdaTot (QLambdaTot QAxiom)))

let test_anif
  : bool ⊩ anif
  = mk_dturniqet (fun _ -> QIf QTrue QFalse QTrue)

let test_negb
  : (bool -> bool) ⊩ negb
  = mk_dturniqet (fun _ -> QLambdaTot (QIf QAxiom QFalse QTrue))

let test_negb_pred ()
  : Tot (((bool -> bool) -> bool -> bool) ⊩ negb_pred)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #negb_pred
    (fun _ -> QLambdaTot (QLambdaTot (QIf (QApp qVar1 QAxiom) QFalse QTrue)))

let test_if2 ()
  : Tot ((bool -> bool -> bool) ⊩ if2)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #if2 (fun _ -> QLambdaTot (QLambdaTot (QIf qVar1 QFalse QAxiom)))

let test_callback_return ()
  : Tot ((bool -> (bool -> bool)) ⊩ callback_return)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #callback_return (
      fun _ -> QLambdaTot (QIf QAxiom
                 (QLambdaTot qVar1)
                 (QLambdaTot QAxiom)))

let test_callback_return' ()
  : Tot ((bool -> (bool -> bool)) ⊩ callback_return')
  by (simplify_via_norm ())
  = mk_dturniqet #_ #callback_return' (
      fun _ -> QLambdaTot (QIf QAxiom
                 (QLambdaTot qVar1)
                 (QLambdaTot QAxiom)))

open ExamplesRefs

let test_refbool
  : (t:bool{t == true}) ⊩ refbool
  = mk_dturniqet #_ #refbool (fun _ -> QRefinement (fun t -> t == true) QTrue)

let test_falsepre ()
  : Tot ((x:bool{False} -> bool) ⊩ falsepre)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #falsepre (fun _ -> QLambdaTot (QRefinement _ QAxiom))

let test_just_true ()
  : Tot ((bool -> (x:bool{x == true})) ⊩ just_true)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #just_true (fun _ -> QLambdaTot (QRefinement (fun x -> x == true) QTrue))

let test_moving_ref ()
  : Tot ((_:bool{some_ref} -> _:unit{some_ref}) ⊩ moving_ref)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #moving_ref (fun _ -> QLambdaTot (QRefinement (fun _ -> some_ref) Qtt))

let test_always_false ()
  : Tot ((bool -> y:bool{y == false}) ⊩ always_false)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #always_false (fun _ -> QLambdaTot (QRefinement (fun y -> y == false) (QIf QAxiom QFalse QAxiom)))

let test_always_false_complex ()
  : Tot ((bool -> y:bool{y == false}) ⊩ always_false_complex)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #always_false_complex (fun _ -> QLambdaTot (QRefinement (fun y -> y == false) (QIf QAxiom (QIf QAxiom QFalse QTrue) QFalse)))

let test_always_false_ho ()
  : Tot (((f:(unit -> x:bool{x == true})) -> y:bool{y == false}) ⊩ always_false_ho)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #always_false_ho (fun _ -> QLambdaTot (QRefinement (fun y -> y == false) (QIf (QRefinement _ (QApp QAxiom Qtt)) QFalse QTrue)))

let test_if_x ()
  : Tot (((f:(x:bool{x == true}) -> bool) -> bool -> bool) ⊩ if_x)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #if_x (fun _ ->
      QLambdaTot (QLambdaTot (QIf QAxiom (QApp qVar1 (QRefinement _ QAxiom)) QFalse)))

let test_seq_basic ()
  : Tot (((f: (unit -> unit)) -> unit) ⊩ seq_basic)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #seq_basic (fun _ -> QLambdaTot (QSeq True (QApp QAxiom Qtt) Qtt))

let test_seq_qref ()
  : Tot (((f: (unit -> _:unit{q_ref})) -> (_:unit{q_ref})) ⊩ seq_qref)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #seq_qref (fun _ -> QLambdaTot (QSeq q_ref (QApp QAxiom Qtt) (QRefinement _ Qtt)))

let test_seq_p_implies_q ()
  : Tot (((f: (x:bool{p_ref x} -> _:unit{q_ref})) -> (x:bool{p_ref x}) -> (x:bool{q_ref})) ⊩ seq_p_implies_q)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #seq_p_implies_q (fun _ ->
      QLambdaTot (QLambdaTot (QSeq q_ref (QApp qVar1 QAxiom) (QRefinement _ QAxiom))))

let test_if_seq ()
  : Tot (((f: (x:bool{x == true} -> _:unit{q_ref})) -> (x:bool) -> (r:bool{r == true ==> q_ref})) ⊩ if_seq)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #if_seq (fun _ ->
      QLambdaTot (QLambdaTot (QIf QAxiom
        (QSeq q_ref
          (QApp qVar1 (QRefinement _ QAxiom))
          (QRefinement (fun r -> r == true ==> q_ref) QAxiom))
        (QRefinement _ QAxiom))))

let test_context ()
  : Tot (((x:bool) -> (f:(x:bool{x == true}) -> bool -> bool) -> bool -> bool) ⊩ context)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #context (fun _ ->
      QLambdaTot
        (QLambdaTot
          (QIf qVar1
            (QApp QAxiom (QRefinement _ qVar1))
            (QLambdaTot QAxiom))))

// let test_wrap_fst_pa
//   : ((bool * bool) -> bool) ⊩ wrap_fst_pa
//   =  fun _ -> QLambdaTot (QFst QAxiom)

#pop-options

let squash_wp () : Tac unit =
  norm [primops; iota; delta; zeta; simplify; unmeta; unascribe];
  or_else trivial (fun () ->
    let _ = repeat forall_intro in
    or_else trivial smt
  )

let get_derivation #a #x (thk_deriv:a ⊩ x) (proof:squash (forall fsG. (dfst thk_deriv) fsG)) : typing empty (dfst thk_deriv) (helper_oexp x) =
  (dsnd thk_deriv) proof

let d_test_constant () : typing _ _ _ =
  get_derivation test_constant ()
let d_test_constant' () : typing _ _ _ =
  get_derivation test_constant' ()
let d_test_identity () : typing _ _ _ =
  get_derivation test_identity ()
let d_test_thunked_id () : typing _ _ _ =
  get_derivation test_thunked_id ()
let d_test_proj1 () : typing _ _ _ =
  get_derivation (test_proj1 ()) ()
let d_test_proj2 () : typing _ _ _ =
  get_derivation (test_proj2 ()) ()
let d_test_proj3 () : typing _ _ _ =
  get_derivation test_proj3 ()
let d_test_apply_top_level_def () : typing _ _ _ =
  get_derivation (test_apply_top_level_def ()) ()
let d_test_apply_top_level_def' () : typing _ _ _ =
  get_derivation (test_apply_top_level_def' ()) ()
let d_test_papply__top_level_def () : typing _ _ _ =
  get_derivation (test_papply__top_level_def ()) ()
let d_test_apply_arg () : typing _ _ _ =
  get_derivation test_apply_arg ()
let d_test_apply_arg2 () : typing _ _ _ =
  get_derivation (test_apply_arg2 ()) ()
let d_test_papply_arg2 () : typing _ _ _ =
  get_derivation (test_papply_arg2 ()) () 
let d_test_anif () : typing _ _ _ =
  get_derivation test_anif ()
let d_test_negb () : typing _ _ _ =
  get_derivation test_negb ()
let d_test_negb_pred () : typing _ _ _ =
  get_derivation (test_negb_pred ()) ()
let d_test_if2 () : typing _ _ _ =
  get_derivation (test_if2 ()) ()
let d_test_callback_return () : typing _ _ _ =
  get_derivation (test_callback_return ()) ()
let d_test_callback_return' () : typing _ _ _ =
  get_derivation (test_callback_return' ()) ()

// d_test_* for ExamplesRefs
let d_test_refbool () : typing _ _ _ =
  get_derivation test_refbool ()
let d_test_falsepre () : typing _ _ _ =
  get_derivation (test_falsepre ()) ()
let d_test_just_true () : typing _ _ _ =
  get_derivation (test_just_true ()) ()
let d_test_moving_ref () : typing _ _ _ =
  get_derivation (test_moving_ref ()) ()
let d_test_always_false () : typing _ _ _ =
  get_derivation (test_always_false ()) ()
let d_test_always_false_complex () : typing _ _ _ =
  get_derivation (test_always_false_complex ()) ()
let d_test_always_false_ho () : typing _ _ _ =
  get_derivation (test_always_false_ho ()) (synth_by_tactic squash_wp)
let d_test_if_x () : typing _ _ _ =
  get_derivation (test_if_x ()) ()
let d_test_seq_basic () : typing _ _ _ =
  get_derivation (test_seq_basic ()) ()
let d_test_seq_qref () : typing _ _ _ =
  get_derivation (test_seq_qref ()) ()
let d_test_seq_p_implies_q () : typing _ _ _ =
  get_derivation (test_seq_p_implies_q ()) ()

// d_test_if_seq and d_test_context need --admit_smt_queries true due to
// incomplete quantifiers over function types in QRefinement's subtyping checks
let d_test_if_seq () : typing _ _ _ =
  get_derivation (test_if_seq ()) ()
let d_test_context () : typing _ _ _ =
  get_derivation (test_context ()) ()
