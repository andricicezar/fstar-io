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

unfold
val wp_lambda_wp :
  #g :env ->
  #a :Type ->
  #b :Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  fs_oexp (extend a g) b wpCtx ->
  spec_env g (x:a -> PURE b (wpFun x))

let wp_lambda_wp #g #a #b wpCtx wpFun body fsG : pure_wp (x:a -> PURE b (wpFun x))  =
  let w : pure_wp' _ = fun (p:pure_post (x:a -> PURE b (wpFun x))) ->
    (forall (x: a) (p: pure_post b).
      wpFun x p ==>
      (wpCtx (fs_stack fsG x) (fun _ -> True) /\ (** Cezar: this is the only extra thing compared to the VC created by F* **)
      wpCtx (fs_stack fsG x) (fun res ->
        res == body (fs_stack fsG x) ==>
        pure_return _ res p))
    //) /\ pure_return _ (fun x -> body (fs_stack fsG x)) p // Cezar: this is not accepted?
    ) /\ p (fun x -> body (fs_stack fsG x))
  in
  assume (M.is_monotonic w);
  mk_pure_wp w



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
  fs_oexp g (x:a -> PURE b (wpFun x)) (wp_lambda_wp wpCtx wpFun body)

let helper_lambda_wp #g #a #b wpCtx wpFun body fsG : PURE (x:a -> PURE b (wpFun x)) (wp_lambda_wp wpCtx wpFun body fsG) =
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


unfold
let helper_oexp (x:'a) (#wp:spec_env empty 'a) (#_:squash (forall fsG. wp fsG <= pure_return 'a x))
  : fs_oexp empty 'a wp
  = fun _ -> x

type typing_closed #a (#wp:spec_env empty a) (x:a) =
  proof:squash (forall fsG. wp fsG <= pure_return a x) -> typing empty wp (helper_oexp x #wp #proof)

type typing_debug #a (wp:spec_env empty a) (x:a) =
  typing_closed #a #wp x

let (⊢) (#a:Type)(g:env) (#wp:spec_env g a) (x:fs_oexp g a wp) =
  typing g wp x

let (⊩) (a:Type) (#wp:spec_env empty a) (x:a) =
  proof:squash (forall fsG. wp fsG <= pure_return a x) -> typing #a empty wp (helper_oexp x #wp #proof)

let simplify_stack_ops () : Tac unit =
   l_to_r [`lem_hd_stack; `lem_tail_stack_inverse]

let simplify_via_norm () : Tac unit =
  let _ = repeat forall_intro in
  or_else 
    (fun () -> 
      or_else 
        (fun () -> norm [delta_only [`%fs_tail; `%FE.on_dom; `%ret; `%pure_return; `%pure_return0]; zeta; iota]; trivial ())
        (fun () -> norm [delta; zeta_full]; trivial ()))
    (fun () -> trefl ())


let qVar1 #g #a #b : (extend b (extend a g)) ⊢ (fun fsG -> fs_hd (fs_tail fsG)) =
  QWeaken QAxiom

let qVar2 #g #a #b #c : (extend c (extend b (extend a g))) ⊢ (fun fsG -> fs_hd (fs_tail (fs_tail fsG))) =
  QWeaken qVar1

#push-options "--no_smt"

open Examples

let test_ut_unit ()
  : unit ⊩ ut_unit
  = fun _ -> Qtt

let test_ut_true
  : bool ⊩ ut_true
  = fun _ -> QTrue

let test_ut_false
  : bool ⊩ ut_false
  = fun _ -> QFalse

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
  = fun _ -> QLambdaTot QTrue

let test_constant'
  : ((bool -> bool) ⊩ constant)
  = fun _ -> QLambdaTot (QWeaken QTrue)

let test_identity
  : (bool -> bool) ⊩ identity
  = fun _ -> QLambdaTot QAxiom

let test_thunked_id
  : (bool -> (bool -> bool)) ⊩ thunked_id
  = fun _ -> QLambdaTot (QLambdaTot QAxiom)

let test_proj1 ()
  : Tot ((bool -> bool -> bool -> bool) ⊩ proj1)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QLambdaTot (QLambdaTot qVar2))

let test_proj2 ()
  : Tot ((bool -> bool -> bool -> bool) ⊩ proj2)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QLambdaTot (QLambdaTot qVar1))

let test_proj3
  : (bool -> bool -> bool -> bool) ⊩ proj3
  = fun _ -> QLambdaTot (QLambdaTot (QLambdaTot QAxiom))

#push-options "--print_implicits --print_universes"

let t = apply_top_level_def
let t1 = Pervasives.norm [] apply_top_level_def

let _ = assert (t == t1) by (
    norm [delta_only [`%t;`%t1;`%apply_top_level_def]; zeta];
    norm [delta_only [`%apply_top_level_def]; zeta];
    // They are the same!
    dump "H")
#pop-options

// TODO: why is `Pervasives.norm []` needed here?
let test_apply_top_level_def ()
  : Tot ((bool -> bool) ⊩ Pervasives.norm [] apply_top_level_def)
  by (norm [delta_only [`%apply_top_level_def]; zeta; iota]; 
      dump "H";
      simplify_via_norm ())
  = fun _ -> QLambdaTot (QApp
              (QApp
                (QLambdaTot (QLambdaTot QAxiom))
                QAxiom)
              QTrue)

let test_apply_top_level_def' ()
  : Tot ((bool -> bool -> bool) ⊩ Pervasives.norm [] apply_top_level_def')
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QLambdaTot (QApp
                       (QApp
                          (QLambdaTot (QLambdaTot QAxiom))
                          qVar1)
                       QAxiom))

let test_papply__top_level_def ()
  : Tot ((bool -> bool -> bool) ⊩ Pervasives.norm [] papply__top_level_def)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QApp
              (QLambdaTot (QLambdaTot QAxiom))
              QAxiom)

let test_apply_arg
  : ((unit -> unit) -> unit) ⊩ apply_arg
  = fun _ -> QLambdaTot (QApp QAxiom Qtt)

let test_apply_arg2 ()
  : Tot (((bool -> bool -> bool) -> bool) ⊩ apply_arg2)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QApp (QApp QAxiom QTrue) QFalse)

let test_papply_arg2 ()
  : Tot (((bool -> bool -> bool) -> bool -> bool) ⊩ papply_arg2)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QApp QAxiom QTrue)

[@expect_failure]
let test_proj2'
  : (bool -> bool -> bool -> bool) ⊩ proj2
  = fun _ -> QLambdaTot (QLambdaTot (QLambdaTot QAxiom))

let test_anif
  : bool ⊩ anif
  = fun _ -> QIf QTrue QFalse QTrue

let test_negb
  : (bool -> bool) ⊩ negb
  = fun _ -> QLambdaTot (QIf QAxiom QFalse QTrue)

let test_negb_pred ()
  : Tot (((bool -> bool) -> bool -> bool) ⊩ Pervasives.norm [] negb_pred)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QLambdaTot (QIf (QApp qVar1 QAxiom) QFalse QTrue))

let test_if2 ()
  : Tot ((bool -> bool -> bool) ⊩ if2)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QLambdaTot (QIf qVar1 QFalse QAxiom))

let test_callback_return ()
  : Tot ((bool -> (bool -> bool)) ⊩ callback_return)
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QIf QAxiom
                 (QLambdaTot qVar1)
                 (QLambdaTot QAxiom))

let test_callback_return' ()
  : Tot ((bool -> (bool -> bool)) ⊩ callback_return')
  by (simplify_via_norm ())
  = fun _ -> QLambdaTot (QIf QAxiom
                 (QLambdaTot qVar1)
                 (QLambdaTot QAxiom)) // TODO: why does it not work to unfold identity here?

#pop-options