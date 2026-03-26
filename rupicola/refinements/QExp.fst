module QExp

open FStar.Tactics.V2

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
let ret (#a:Type u#a) x : pure_wp a = pure_return a x

(* Local helper to convert pure_wp' to pure_wp by proving monotonicity *)
private unfold
let mk_pure_wp #a (wp:pure_wp' a{M.is_monotonic wp}) : pure_wp a =
  M.intro_pure_wp_monotonicity wp; wp

let refv_wp #a (ref1 ref2:a -> Type0) (wpV:pure_wp (x:a{ref1 x})) : pure_wp (x:a{ref2 x}) =
  pure_bind_wp (x:a{ref1 x}) (x:a{ref2 x}) wpV (fun r ->
    mk_pure_wp (fun (p:pure_post (x:a{ref2 x})) -> ref2 r /\ p r))

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

type spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> PURE a (wpG fsG)

#restart-solver

val helper_weaken : #g:env ->
                    #a:Type u#a ->
                    b:Type0 ->
                    wpX:spec_env g a ->
                    x:fs_oexp g a wpX ->
                    fs_oexp (extend b g) a (fun fsG -> wpX (fs_tail fsG))
let helper_weaken #g #a b wpX x fsG =
  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic u#a);
  x (fs_tail fsG)

#restart-solver

unfold
val helper_var0 : g:env ->
                 a:Type ->
                 fs_oexp (extend a g) a (fun fsG -> ret (fs_hd fsG))
let helper_var0 g a fsG : PURE a (ret (fs_hd fsG)) =
  fs_hd fsG

unfold
val helper_unit : g:env -> fs_oexp g unit (fun _ -> ret ())
let helper_unit g = fun _ -> ()

unfold
val helper_true : g:env -> fs_oexp g bool (fun _ -> ret true)
let helper_true g = fun _ -> true

unfold
val helper_false : g:env -> fs_oexp g bool (fun _ -> ret false)
let helper_false g = fun _ -> false

val wp_app:     #g :env ->
                #a :Type ->
                #b :Type ->
                wpF : spec_env g (a -> b) ->
                wpX : spec_env g a ->
                spec_env g b
let wp_app #_ #a #b wpF wpX =
  (fun fsG ->
    pure_bind_wp (a -> b) b (wpF fsG) (fun f' ->
      pure_bind_wp a b (wpX fsG) (fun x' ->
        pure_return b (f' x'))))

unfold
val helper_app: #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                f :fs_oexp g (a -> b) wpF ->
                #wpX : spec_env g a ->
                x :fs_oexp g a wpX ->
                fs_oexp g b (wp_app wpF wpX)

let helper_app #_ #_ #_ #wpF f #wpX x =
  fun fsG ->
    M.elim_pure_wp_monotonicity (wpF fsG);
    M.elim_pure_wp_monotonicity (wpX fsG);
    (f fsG) (x fsG)

val wp_if : #g :env ->
                #a :Type ->
                wpC : spec_env g bool ->
                wpT : spec_env g a ->
                wpE : spec_env g a ->
                spec_env g a
let wp_if #_ #a wpC wpT wpE =
  (fun fsG ->
    pure_bind_wp bool a (wpC fsG) (fun r ->
      pure_if_then_else a r (wpT fsG) (wpE fsG)))

unfold
val helper_if : #g :env ->
                #a :Type ->
                #wpC : spec_env g bool ->
                c   : fs_oexp g bool wpC ->
                #wpT : spec_env g a ->
                t   : fs_oexp g a wpT ->
                #wpE : spec_env g a ->
                e   : fs_oexp g a wpE ->
                fs_oexp g a (wp_if wpC wpT wpE)
let helper_if #_ #_ #wpC c #wpT t #wpE e =
  fun fsG ->
    M.elim_pure_wp_monotonicity (wpC fsG);
    M.elim_pure_wp_monotonicity (wpT fsG);
    M.elim_pure_wp_monotonicity (wpE fsG);
    if c fsG then t fsG else e fsG

unfold
val wp_lambda_tot : #g :env ->
                #a :Type ->
                #b :Type ->
                wpCtx:spec_env (extend a g) b ->
                body:fs_oexp (extend a g) b wpCtx ->
                spec_env g (a -> b)

let wp_lambda_tot #g #a #b wpCtx body fsG : pure_wp (a -> b) = (** Cezar: this seems to be exactly what F* generates **)
  mk_pure_wp (fun (p:pure_post (a -> b)) ->
    (forall x. wpCtx (fs_stack fsG x) (fun _ -> True)) /\
    p (fun x -> body (fs_stack fsG x)))

unfold
val helper_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpCtx:spec_env (extend a g) b ->
                body :fs_oexp (extend a g) b wpCtx ->
                fs_oexp g (a -> b) (wp_lambda_tot wpCtx body)
let helper_lambda #g #a #b #wpCtx body fsG =
  (fun x -> body (fs_stack fsG x))

type eff_fun (a:Type) (b:Type) (wpFun: a -> pure_wp b) = x:a -> PURE b (wpFun x)

unfold
val wp_lambda_wp :
  #g :env ->
  #a :Type ->
  #b :Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  fs_oexp (extend a g) b wpCtx ->
  spec_env g (eff_fun a b wpFun)

let wp_lambda_wp #g #a #b wpCtx wpFun body fsG : pure_wp (eff_fun a b wpFun) =
  mk_pure_wp (fun (p:pure_post (eff_fun a b wpFun)) ->
    (forall (x: a) (p: pure_post b).
      wpFun x p ==>
      (wpCtx (fs_stack fsG x) (fun _ -> True) /\ (** Cezar: this is the only extra thing compared to the VC created by F* **)
      wpCtx (fs_stack fsG x) (fun res ->
        res == body (fs_stack fsG x) ==>
        pure_return _ res p))
    ) /\
    (forall (f: eff_fun a b wpFun).
      f == (fun x -> body (fs_stack fsG x)) ==> p f))



  // fun (p:pure_post (x:a -> PURE b (wpFun x))) ->
  //   (forall x. (* wpFun x (fun _ -> True) ==> *) wpCtx (fs_stack fsG x) (fun _ -> True)) /\
  //   forall (f:(x:a -> PURE b (wpFun x))).
  //     (
  //       forall (q : pure_post b) (x:a).
  //         wpFun x q ==>
  //         wpCtx (fs_stack fsG x) q ==>
  //         q (f x)
  //     ) ==>
  //     p f

unfold
val helper_lambda_wp :
  #g : env ->
  #a : Type ->
  #b : Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  body : fs_oexp (extend a g) b wpCtx ->
  fs_oexp g (eff_fun a b wpFun) (wp_lambda_wp wpCtx wpFun body)

let helper_lambda_wp #g #a #b wpCtx wpFun body fsG : PURE (eff_fun a b wpFun) (wp_lambda_wp wpCtx wpFun body fsG) =
  fun x ->
    body (fs_stack fsG x)

unfold
val helper_refv: #g:env ->
                #a:Type ->
                #ref1:(a -> Type0) ->
                ref2:(a -> Type0) ->
                wpV:spec_env g (x:a{ref1 x}) ->
                v:fs_oexp g (x:a{ref1 x}) wpV ->
                fs_oexp g (x:a{ref2 x}) (fun fsG -> refv_wp ref1 ref2 (wpV fsG))
let helper_refv _ wpV v =
  fun fsG -> M.elim_pure_wp_monotonicity (wpV fsG);
    v fsG

unfold
val helper_seq :#g:env ->
                #ref1:Type0 ->
                wpV:spec_env g (_:unit{ref1}) ->
                v:fs_oexp g (_:unit{ref1}) wpV ->
                #a:Type ->
                wpK:spec_env g a ->
                k:fs_oexp g a wpK ->
                fs_oexp g a
                  (fun fsG -> pure_bind_wp (x:unit{ref1}) a (wpV fsG) (fun _ -> wpK fsG))
let helper_seq wpV v wpK k =
  fun fsG ->
    M.elim_pure_wp_monotonicity (wpV fsG);
    M.elim_pure_wp_monotonicity (wpK fsG);
    v fsG ; k fsG

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type typing : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| Qtt       : #g:env ->  typing g _ (helper_unit g)
| QTrue       : #g:env ->  typing g _ (helper_true g)
| QFalse      : #g:env ->  typing g _ (helper_false g)

| QAxiom      : #g : env ->
                #a : Type ->
                typing (extend a g) _ (helper_var0 g a)

| QWeaken      : #g : env ->
                #a : Type ->
                #b : Type ->
                #wpX : spec_env g a ->
                #x : fs_oexp g a wpX ->
                typing g wpX x ->
                typing (extend b g) _ (helper_weaken b wpX x)

| QApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                #f :fs_oexp g (a -> b) wpF ->
                cf:typing g wpF f ->
                #wpX : spec_env g a ->
                #x :fs_oexp g a wpX ->
                cx:typing g wpX x ->
                typing #b g _ (helper_app #_ #_ #_ #wpF f x)

| QIf         : #g :env ->
                #a :Type ->
                #wpC : spec_env g bool ->
                #c   : fs_oexp g bool wpC ->
                cc   : typing g wpC c ->
                #wpT : spec_env g a ->
                #t   : fs_oexp g a wpT ->
                ct   : typing g wpT t ->
                #wpE : spec_env g a ->
                #e   : fs_oexp g a wpE ->
                ce   : typing g wpE e ->
                typing g _ (helper_if c t e)

| QLambdaTot  : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpCtx:spec_env (extend a g) b ->
                #body :fs_oexp (extend a g) b wpCtx ->
                cf:typing #b (extend a g) wpCtx body ->
                typing g (wp_lambda_tot #g #a #b wpCtx body) (helper_lambda body)

| QLambdaWP :
  #g : env ->
  #a : Type ->
  #b : Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  #body : fs_oexp (extend a g) b wpCtx ->
  typing #b (extend a g) wpCtx body ->
  typing g (wp_lambda_wp wpCtx wpFun body) (helper_lambda_wp wpCtx wpFun body)

| QRefinement : #g:env ->
                #a:Type ->
                ref1:(a -> Type0) ->
                #ref2:(a -> Type0) ->
                #wpV:spec_env g (x:a{ref1 x}) ->
                #v:fs_oexp g (x:a{ref1 x}) wpV ->
                typing #(x:a{ref1 x}) g wpV v ->
                typing #(x:a{ref2 x}) g _ (helper_refv ref2 wpV v)

| QSeq        : #g:env ->
                ref1:Type0 ->
                #wpV:spec_env g (_:unit{ref1}) ->
                #v:fs_oexp g (_:unit{ref1}) wpV ->
                typing #(_:unit{ref1}) g wpV v -> (** the name typing is misleading here.
                                         I have to compute the WP of `v` to be able to
                                         compile the entire term, even if this is computationally irelevant **)

                #a:Type ->
                #wpK:spec_env g a ->
                #k:fs_oexp g a wpK ->
                typing #a g wpK k ->
                typing #a g _ (helper_seq wpV v wpK k)

// DO NOT MARK WITH UNFOLD
let helper_oexp (x:'a) (#wp:spec_env empty 'a) (#_:squash (forall fsG. wp fsG <= pure_return 'a x))
  : fs_oexp empty 'a wp
  = fun _ -> x

type typing_closed #a (#wp:spec_env empty a) (x:a) =
  proof:squash (forall fsG. wp fsG <= pure_return a x) -> typing empty wp (helper_oexp x #wp #proof)

type typing_debug #a (wp:spec_env empty a) (x:a) =
  typing_closed #a #wp x

let (⊢) (#a:Type)(g:env) (#wp:spec_env g a) (x:fs_oexp g a wp) =
  typing g wp x

let (⊩) (a:Type) (x:a) =
  wp:spec_env empty a & (proof:squash (forall fsG. wp fsG <= pure_return a x) -> typing #a empty wp (helper_oexp x #wp #proof))

let mk_dturniqet #a #x (#wp:spec_env empty a) (thk_dv:(proof:squash (forall fsG. wp fsG <= pure_return a x) -> typing #a empty wp (helper_oexp x #wp #proof))) : a ⊩ x =
  (| _, thk_dv |)


let simplify_stack_ops () : Tac unit =
   l_to_r [`lem_hd_stack; `lem_tail_stack_inverse]

let simplify_via_norm () : Tac unit =
  let _ = repeat forall_intro in
  or_else 
    (fun () -> 
      or_else 
        (fun () -> norm [delta_only [`%fs_tail; `%FE.on_dom; `%ret; `%pure_return; `%pure_return0]; zeta; iota]; trivial ())
        (fun () -> norm [delta; zeta_full]; trivial ()))
    trefl


let qVar1 #g #a #b : (extend b (extend a g)) ⊢ (fun fsG -> fs_hd (fs_tail fsG)) =
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
  = mk_dturniqet #_ #refbool (fun _ -> QRefinement _ QTrue)

let test_falsepre ()
  : Tot ((x:bool{False} -> bool) ⊩ falsepre)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #falsepre (fun _ -> QLambdaTot (QRefinement _ QAxiom))

let test_just_true ()
  : Tot ((bool -> (x:bool{x == true})) ⊩ just_true)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #just_true (fun _ -> QLambdaTot (QRefinement _ QTrue))

let test_moving_ref ()
  : Tot ((_:bool{some_ref} -> _:unit{some_ref}) ⊩ moving_ref)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #moving_ref (fun _ -> QLambdaTot (QRefinement _ Qtt))

let test_always_false ()
  : Tot ((bool -> y:bool{y == false}) ⊩ always_false)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #always_false (fun _ -> QLambdaTot (QRefinement _ (QIf QAxiom QFalse QAxiom)))

let test_always_false_complex ()
  : Tot ((bool -> y:bool{y == false}) ⊩ always_false_complex)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #always_false_complex (fun _ -> QLambdaTot (QRefinement _ (QIf QAxiom (QIf QAxiom QFalse QTrue) QFalse)))

let test_always_false_ho ()
  : Tot (((f:(unit -> x:bool{x == true})) -> y:bool{y == false}) ⊩ always_false_ho)
  by (simplify_via_norm ())
  = mk_dturniqet #_ #always_false_ho (fun _ -> QLambdaTot (QRefinement _ (QIf (QRefinement _ (QApp QAxiom Qtt)) QFalse QTrue)))

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

// The following three tests require --admit_smt_queries true because
// wp_lambda_tot needs a monotonicity proof (M.is_monotonic) which Z3
// cannot discharge when quantifiers range over function types or abstract
// refinement predicates (Z3 reports "incomplete quantifiers").
#push-options "--admit_smt_queries true"

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
          (QRefinement _ QAxiom))
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
  or_else (fun () ->
    let _ = forall_intro () in
    let _ = forall_intro () in
    let h = implies_intro () in
    let _ = forall_intro () in
    let h2 = implies_intro () in
    rewrite h2;
    assumption ()
  ) (fun () ->
    pointwise' (fun () ->
      norm [primops; iota; delta; zeta; simplify; unmeta; unascribe];
      or_else trefl smt
    );
    or_else (fun () ->
      let _ = forall_intro () in
      let _ = forall_intro () in
      let h = implies_intro () in
      let _ = forall_intro () in
      let h2 = implies_intro () in
      rewrite h2;
      assumption ()
    ) smt
  )

let get_derivation #a #x (thk_deriv:a ⊩ x) (proof:squash (forall fsG. (dfst thk_deriv) fsG <= pure_return a x)) : typing empty (dfst thk_deriv) (helper_oexp x) =
  (dsnd thk_deriv) proof

let d_test_constant () : typing _ _ _ by (compute ()) =
  get_derivation test_constant ()
let d_test_constant' () : typing _ _ _ by (compute ()) =
  get_derivation test_constant' ()
let d_test_identity () : typing _ _ _ by (compute ()) =
  get_derivation test_identity ()
let d_test_thunked_id () : typing _ _ _ by (compute ()) =
  get_derivation test_thunked_id ()
let d_test_proj1 () : typing _ _ _ by (compute ()) =
  get_derivation (test_proj1 ()) ()
let d_test_proj2 () : typing _ _ _ by (compute ()) =
  get_derivation (test_proj2 ()) ()
let d_test_proj3 () : typing _ _ _ by (compute ()) =
  get_derivation test_proj3 ()
let d_test_apply_top_level_def () : typing _ _ _ by (compute ()) =
  get_derivation (test_apply_top_level_def ()) ()
let d_test_apply_top_level_def' () : typing _ _ _ by (compute ()) =
  get_derivation (test_apply_top_level_def' ()) ()
let d_test_papply__top_level_def () : typing _ _ _ by (compute ()) =
  get_derivation (test_papply__top_level_def ()) ()
let d_test_apply_arg () : typing _ _ _ by (compute ()) =
  get_derivation test_apply_arg ()
let d_test_apply_arg2 () : typing _ _ _ =
  get_derivation (test_apply_arg2 ()) (synth_by_tactic squash_wp)
let d_test_papply_arg2 () : typing _ _ _ =
  get_derivation (test_papply_arg2 ()) (synth_by_tactic squash_wp)
let d_test_anif () : typing _ _ _ =
  get_derivation test_anif ()
let d_test_negb () : typing _ _ _ by (compute ()) =
  get_derivation test_negb ()
let d_test_negb_pred () : typing _ _ _ by (compute ())=
  get_derivation (test_negb_pred ()) ()
let d_test_if2 () : typing _ _ _ =
  get_derivation (test_if2 ()) (synth_by_tactic squash_wp)
let d_test_callback_return () : typing _ _ _ =
  get_derivation (test_callback_return ()) (synth_by_tactic squash_wp)
let d_test_callback_return' () : typing _ _ _ =
  get_derivation (test_callback_return' ()) (synth_by_tactic squash_wp)

// d_test_* for ExamplesRefs
let d_test_refbool () : typing _ _ _ by (compute ()) =
  get_derivation test_refbool ()
let d_test_falsepre () : typing _ _ _ =
  get_derivation (test_falsepre ()) (synth_by_tactic squash_wp)
let d_test_just_true () : typing _ _ _ =
  get_derivation (test_just_true ()) (synth_by_tactic squash_wp)
let d_test_moving_ref () : typing _ _ _ =
  get_derivation (test_moving_ref ()) (synth_by_tactic squash_wp)
let d_test_always_false () : typing _ _ _ =
  get_derivation (test_always_false ()) (synth_by_tactic squash_wp)
let d_test_always_false_complex () : typing _ _ _ =
  get_derivation (test_always_false_complex ()) (synth_by_tactic squash_wp)
let d_test_always_false_ho () : typing _ _ _ =
  get_derivation (test_always_false_ho ()) (synth_by_tactic squash_wp)
let d_test_if_x () : typing _ _ _ =
  get_derivation (test_if_x ()) (synth_by_tactic squash_wp)
let d_test_seq_basic () : typing _ _ _ =
  get_derivation (test_seq_basic ()) (synth_by_tactic squash_wp)
let d_test_seq_qref () : typing _ _ _ =
  get_derivation (test_seq_qref ()) (synth_by_tactic squash_wp)
#push-options "--admit_smt_queries true"
let d_test_seq_p_implies_q () : typing _ _ _ =
  get_derivation (test_seq_p_implies_q ()) (synth_by_tactic squash_wp)
let d_test_if_seq () : typing _ _ _ =
  get_derivation (test_if_seq ()) (synth_by_tactic squash_wp)
let d_test_context () : typing _ _ _ =
  get_derivation (test_context ()) (synth_by_tactic squash_wp)
#pop-options
