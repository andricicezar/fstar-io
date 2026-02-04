module QExp

open FStar.Tactics.V2

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
let ret (#a:Type u#a) x : pure_wp a = pure_return a x

let refv_wp (#a:Type u#a) (ref1 ref2:a -> Type0) (wpV:pure_wp (x:a{ref1 x})) : pure_wp (x:a{ref2 x}) =
  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic u#a);
  pure_bind_wp (x:a{ref1 x}) (x:a{ref2 x}) wpV (fun r ->
    (fun (p:pure_post (x:a{ref2 x})) -> ref2 r /\ p r))

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

unfold
val fs_tail : #t:Type -> #g:_ -> fs_env (extend t g) -> fs_env g
let fs_tail #t #g fsG =
  FE.on_dom
    (x:var{Some? (g x)})
    #(fun x -> Some?.v (g x))
    (fun y -> fsG (y+1))

type spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> PURE a (wpG fsG)

unfold
val helper_var0 : g:env ->
                 a:Type ->
                 fs_oexp (extend a g) a (fun fsG -> ret (fs_hd fsG))
let helper_var0 g a fsG : PURE a (ret (fs_hd fsG)) =
  fs_hd fsG

unfold
val helper_var1 : g:env ->
                  a:Type ->
                  b:Type ->
                  fs_oexp (extend b (extend a g)) a (fun fsG -> ret (fs_hd (fs_tail #b fsG)))
let helper_var1 g a b fsG = fs_hd (fs_tail #b fsG)

unfold
val helper_var2 : g:env ->
                  a:Type ->
                  b:Type ->
                  c:Type ->
                  fs_oexp (extend c (extend b (extend a g))) a (fun fsG -> ret (fs_hd (fs_tail #b (fs_tail #c fsG))))
let helper_var2 g a b c fsG = fs_hd (fs_tail #b (fs_tail #c fsG))

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
                #a :Type u#a ->
                #b :Type u#b ->
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
                #a :Type u#a ->
                #wpC : spec_env g bool ->
                c   : fs_oexp g bool wpC ->
                #wpT : spec_env g a ->
                t   : fs_oexp g a wpT ->
                #wpE : spec_env g a ->
                e   : fs_oexp g a wpE ->
                fs_oexp g a (wp_if wpC wpT wpE)
let helper_if c t e =
  fun fsG ->
    M.elim_pure_wp_monotonicity_forall u#0 ();
    M.elim_pure_wp_monotonicity_forall u#a ();
    if c fsG then t fsG else e fsG

val wp_lambda : #g :env ->
                #a :Type u#0 ->
                #b :Type u#b ->
                wpBody:spec_env (extend a g) b ->
                spec_env g (a -> b)

let wp_lambda #g #a #b wpBody fsG : pure_wp (a -> b) =
  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic u#b);
  fun (p:pure_post (a -> b)) ->
    forall (f:a -> b).
      (forall (p':pure_post b) (fsG':fs_env (extend a g)).
        fsG == fs_tail fsG' ==>  wpBody fsG' p' ==>  p' (f (fs_hd fsG'))
      ) ==>  p f

unfold
val helper_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpBody:spec_env (extend a g) b ->
                f :fs_oexp g (a -> b) (wp_lambda wpBody) ->
                fs_oexp (extend a g) b wpBody
let helper_lambda #g #a f =
  fun fsG -> f (fs_tail #a fsG) (fs_hd fsG)

val wp_lambda0' :
  #g :env ->
  #a :Type u#0 ->
  #b :Type u#b ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  fs_oexp (extend a g) b wpCtx ->
  fsG:fs_env g ->
  pure_wp' (x:a -> PURE b (wpFun x))

let wp_lambda0' #g #a #b wpCtx wpFun body fsG =
  fun (p:pure_post (x:a -> PURE b (wpFun x))) ->
    (forall (x: a) (p: pure_post b).
      wpFun x p ==>
      (wpCtx (fs_stack fsG x) (fun _ -> True) /\ (** Cezar: this is the only extra thing compared to the VC created by F* **)
      wpCtx (fs_stack fsG x) (fun res ->
        res == body (fs_stack fsG x) ==>
        pure_return _ res p))
    //) /\ pure_return _ (fun x -> body (fs_stack fsG x)) p // Cezar: this is not accepted?
    ) /\ p (fun x -> body (fs_stack fsG x))

let lem_wp_lambda'_monotonic #g #a #b wpCtx wpFun body fsG : Lemma (pure_wp_monotonic0 (x:a -> PURE b (wpFun x)) (wp_lambda0' #g #a #b wpCtx wpFun body fsG)) =
  admit ()

val wp_lambda' :
  #g :env ->
  #a :Type u#0 ->
  #b :Type u#b ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  fs_oexp (extend a g) b wpCtx ->
  fsG:fs_env g ->
  pure_wp (x:a -> PURE b (wpFun x))
let wp_lambda' #g (#a:Type u#0) (#b:Type u#b) wpCtx wpFun body fsG : pure_wp (x:a -> PURE b (wpFun x)) = admit ()

//  lem_wp_lambda'_monotonic wpCtx wpFun body fsG;
//  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic u#b);
// wp_lambda0' #g #a #b wpCtx wpFun body fsG


unfold
val helper_lambda' :
  #g : env ->
  #a : Type ->
  #b : Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  body : fs_oexp (extend a g) b wpCtx ->
  fs_oexp g (x:a -> PURE b (wpFun x)) (wp_lambda' wpCtx wpFun body)
let helper_lambda' wpCtx wpFun body fsG =
  admit ();
  fun x -> body (fs_stack fsG x)




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
                #a:Type u#a ->
                wpK:spec_env g a ->
                k:fs_oexp g a wpK ->
                fs_oexp g a
                  (fun fsG -> pure_bind_wp (x:unit{ref1}) a (wpV fsG) (fun _ -> wpK fsG))
let helper_seq _ v _ k =
  fun fsG -> M.elim_pure_wp_monotonicity_forall u#0 ();  M.elim_pure_wp_monotonicity_forall u#a ();
    v fsG ; k fsG

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env ->  compilable g _ (helper_unit g)
| CTrue       : #g:env ->  compilable g _ (helper_true g)
| CFalse      : #g:env ->  compilable g _ (helper_false g)

| CVar0       : #g:env ->
                #a:Type ->
                compilable #a _ _ (helper_var0 g a)

| CVar1       : #g:env ->
                #a:Type ->
                #b:Type ->
                compilable #a _ _ (helper_var1 g a b)
| CVar2       : #g:env ->
                #a:Type ->
                #b:Type ->
                #c:Type ->
                compilable #a _ _ (helper_var2 g a b c)

| CApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                #f :fs_oexp g (a -> b) wpF ->
                cf:compilable g wpF f ->
                #wpX : spec_env g a ->
                #x :fs_oexp g a wpX ->
                cx:compilable g wpX x ->
                compilable #b g _ (helper_app #_ #_ #_ #wpF f x)

| CIf         : #g :env ->
                #a :Type ->
                #wpC : spec_env g bool ->
                #c   : fs_oexp g bool wpC ->
                cc   : compilable g wpC c ->
                #wpT : spec_env g a ->
                #t   : fs_oexp g a wpT ->
                ct   : compilable g wpT t ->
                #wpE : spec_env g a ->
                #e   : fs_oexp g a wpE ->
                ce   : compilable g wpE e ->
                compilable g _ (helper_if c t e)

| CLambda     : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpBody:spec_env (extend a g) b ->
                #f :fs_oexp g (a -> b) (wp_lambda wpBody) ->
                compilable #b (extend a g) wpBody (helper_lambda f) ->
                compilable g (wp_lambda #g #a #b wpBody) f

| QLambda :
  #g : env ->
  #a : Type ->
  #b : Type ->
  #wpCtx : spec_env (extend a g) b ->
  #wpFun : (a -> pure_wp b) ->
  #body : fs_oexp (extend a g) b wpCtx ->
  compilable #b (extend a g) wpCtx body ->
  compilable #(x:a -> PURE b (wpFun x)) g (wp_lambda' wpCtx wpFun body) (helper_lambda' wpCtx wpFun body)


| CRefinement : #g:env ->
                #a:Type ->
                ref1:(a -> Type0) ->
                #ref2:(a -> Type0) ->
                #wpV:spec_env g (x:a{ref1 x}) ->
                #v:fs_oexp g (x:a{ref1 x}) wpV ->
                compilable #(x:a{ref1 x}) g wpV v ->
                compilable #(x:a{ref2 x}) g _ (helper_refv ref2 wpV v)

| CSeq        : #g:env ->
                ref1:Type0 ->
                #wpV:spec_env g (_:unit{ref1}) ->
                #v:fs_oexp g (_:unit{ref1}) wpV ->
                compilable #(_:unit{ref1}) g wpV v -> (** the name compilable is misleading here.
                                         I have to compute the WP of `v` to be able to
                                         compile the entire term, even if this is computationally irelevant **)

                #a:Type ->
                #wpK:spec_env g a ->
                #k:fs_oexp g a wpK ->
                compilable #a g wpK k ->
                compilable #a g _ (helper_seq wpV v wpK k)


let test_app0 ()
  : Tot (compilable (extend (bool -> bool) empty) _ (fun fsG -> fs_hd fsG true))
  = CApp CVar0 CTrue

// FIXME, why does it need tactics to do such simple proofs?
let test_app1 ()
  : Tot (compilable (extend (bool -> bool -> bool) empty) _ (fun fsG -> ((fs_hd fsG) true) false))
  by (dump "H")
  = CApp (CApp CVar0 CTrue) CFalse

let test2_var
  : compilable (extend unit (extend unit empty)) _ (fun fsG -> fs_hd (fs_tail fsG))
  = CVar1

unfold
let helper_oexp (x:'a) (#wp:spec_env empty 'a) (#_:squash (forall fsG. wp fsG <= pure_return 'a x))
  : fs_oexp empty 'a wp
  = fun _ -> x

#push-options "--no_smt"

type compilable_closed #a (#wp:spec_env empty a) (x:a) =
  proof:squash (forall fsG. wp fsG <= pure_return a x) -> compilable empty wp (helper_oexp x #wp #proof)

type compilable_debug #a (wp:spec_env empty a) (x:a) =
  compilable_closed #a #wp x

let test1_exp ()
  : Tot (compilable_closed #(bool -> bool) (fun x -> x))
  = fun _ -> QLambda CVar0

let test1_exp' ()
  : Tot (compilable_closed #(bool -> bool -> bool) (fun x y -> y))
  = fun _ ->  QLambda (QLambda CVar0)

let test_fapp1 ()
  : compilable_closed #((unit -> unit) -> unit) (fun f -> f ())
  = fun _ -> QLambda (CApp CVar0 CUnit)

let test_fapp2 ()
  : compilable_closed #((bool -> bool -> bool) -> bool) (fun f -> f true false)
  = fun _ -> QLambda (CApp (CApp CVar0 CTrue) CFalse)

let test4_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> x)
  = fun _ -> QLambda (QLambda (QLambda CVar2))

let test5_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x -> fun y z -> y)
  = fun _ -> QLambda (QLambda (QLambda CVar1))

let test6_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> z)
  = fun _ -> QLambda (QLambda (QLambda CVar0))

[@expect_failure]
let test4_exp'' ()
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = fun _ -> QLambda (QLambda (QLambda CVar0))

let test1_hoc ()
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  = fun _ -> QLambda (CApp CVar0 CFalse)

let test2_if0 ()
  : compilable_closed #(bool) (if true then false else true)
  = fun _ -> (CIf CTrue CFalse CTrue)

let test2_if ()
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  = fun _ -> QLambda (CIf CVar0 CFalse CTrue)

#pop-options


// TODO: why do I have to hoist these outside?
unfold
let myf : fs_oexp (extend bool empty) (bool -> bool) (wp_lambda (fun fsG -> ret (fs_hd (fs_tail fsG)))) =
  fun fsG y -> fs_hd fsG

unfold
let myid : fs_oexp (extend bool empty) (bool -> bool) (wp_lambda (fun fsG -> ret (fs_hd fsG))) =
  fun fsG z -> z

#push-options "--no_smt"

val creame : bool -> (bool -> bool)
let creame = (fun x -> if x then (fun y -> x) else (fun z -> z))

let test3_if_ho ()
  : compilable_closed #(bool -> (bool -> bool)) creame
  by (dump "H")
  = fun _ -> QLambda (CIf CVar0
                       (QLambda CVar1) // TODO: why cannot it infer myf?
                       (QLambda CVar0))

let test1_if ()
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  by (dump "H")
  = fun _ -> QLambda (QLambda (CIf CVar1 CFalse CVar0))

let test1_comp_ref ()
  : compilable_closed #(x:bool{x == true} -> x:bool{x == true}) (fun x -> x)
  = fun _ -> QLambda CVar0

let test1_erase_ref ()
  : compilable_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = fun _ -> QLambda (CRefinement _ CVar0)

open Examples

let test_erase_refine_again ()
  : compilable_closed #(x:bool{p_ref x} -> x:bool{p_ref x}) (fun x -> x)
  = fun _ -> QLambda (CRefinement _ (CRefinement _ CVar0))

[@expect_failure]
let test_just_false
  : compilable_closed #(bool -> (x:bool{x == true})) (fun x -> false)
  = fun _ -> QLambda (CRefinement _ CFalse)

let test_just_true' ()
  : compilable_closed just_true
  = fun _ -> QLambda (CRefinement _ CTrue)

let test_moving_ref' ()
  : compilable_closed moving_ref
  = fun _ -> QLambda (CRefinement _ CUnit)

let test_always_false' ()
  : compilable_closed always_false
  by (dump "H")
  = fun _ -> QLambda (CRefinement _ (CIf CVar0 (CFalse) CVar0))

let test_always_false'' ()
  : Tot (compilable_closed always_false)
  by (norm [delta_only [`%always_false]]; dump "H") // TODO: why is the unfolding necessary?
  = fun _ ->
    QLambda (CIf CVar0
                (CRefinement (fun y -> True) CFalse)
                (CRefinement (fun y -> True) CVar0))

let test_always_false_complex' ()
  : compilable_closed always_false_complex
  = fun _ -> QLambda (CRefinement _ (CIf CVar0 (CIf CVar0 CFalse CTrue) CFalse))

let test_always_false_complex'' ()
  : compilable_closed always_false_complex
  = fun _ -> QLambda (CIf CVar0 (CIf CVar0 (CRefinement _ CFalse) (CRefinement _ CTrue)) (CRefinement _ CFalse))

let test_always_false_ho ()
  : compilable_closed always_false_ho
  = fun _ -> QLambda (CIf (CRefinement _ (CApp CVar0 CUnit)) (CRefinement _ CFalse) (CRefinement _ CTrue))

let test_if_x' ()
  : compilable_closed if_x
  by (norm [delta_only [`%if_x]]) // TODO: why is the unfolding necessary?
  = fun _ -> QLambda (QLambda (CIf CVar0 (CApp CVar1 (CRefinement _ CVar0)) CFalse))

let test_seq_basic' ()
  : compilable_closed (FStar.Pervasives.norm [delta_only [`%seq_basic]] seq_basic)
  = fun _ -> QLambda (CSeq _ (CApp CVar0 CUnit) CUnit)

let test_seq_qref' ()
  : compilable_closed seq_qref
  = fun _ -> QLambda (CSeq _ (CApp CVar0 CUnit) (CRefinement _ CUnit))

let test_seq_p_implies_q' ()
  : compilable_closed seq_p_implies_q
  = fun _ -> QLambda (QLambda (CSeq _ (CApp CVar1 CVar0) (CRefinement _ CVar0)))

let test_if_seq' ()
  : compilable_closed if_seq
  = fun _ -> QLambda (QLambda (
     CIf CVar0
       (CSeq _ (CApp CVar1 (CRefinement _ CVar0))
                     (CRefinement _ CVar0))
       (CRefinement _ CVar0)))

#pop-options

unfold
let myid2 : fs_oexp (extend (f:(x:bool{x == true}) -> bool -> bool) (extend bool empty)) (bool -> bool) (wp_lambda (fun fsG -> ret (fs_hd fsG))) =
  fun fsG y -> y

#push-options "--no_smt"

let test_context' ()
  : compilable_closed (FStar.Pervasives.norm [delta_only [`%context];iota;unascribe] context)
  by (dump "H")
 // by (norm [delta_only [`%context]]; tadmit ()) // TODO: why is the unfolding necessary? // TODO: why is the tadmit necessary?
  = fun _ ->
    // TODO: why does it fail here?
    QLambda (QLambda (CIf CVar1
                          (CApp CVar0 (CRefinement _ CVar1))
                          (QLambda CVar0)))
