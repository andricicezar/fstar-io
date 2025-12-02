module QExp

open FStar.Tactics.V2

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
let ret #a x : pure_wp a =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  fun p -> p x

let refv_wp #a (ref1 ref2:a -> Type0) (wpV:pure_wp (x:a{ref1 x})) : pure_wp (x:a{ref2 x}) =
  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic);
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
assume val fs_env (g:env) : Type u#0
assume val fs_empty : fs_env empty
assume val fs_stack : #g:env -> fsG:fs_env g -> #t:Type -> t -> fs_env (extend t g)
assume val fs_hd : #g:env -> #t:Type -> fs_env (extend t g) -> t
assume val fs_tail : #t:Type -> #g:env -> fs_env (extend t g) -> fs_env g

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
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                f :fs_oexp g (a -> b) wpF ->
                #wpX : spec_env g a ->
                x :fs_oexp g a wpX ->
                fs_oexp g b (wp_app wpF wpX)

let helper_app f x =
  fun fsG ->
    M.elim_pure_wp_monotonicity_forall ();
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
let helper_if c t e =
  fun fsG ->
    M.elim_pure_wp_monotonicity_forall ();
    if c fsG then t fsG else e fsG

val wp_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                wpBody:spec_env (extend a g) b ->
                spec_env g (a -> b)

let wp_lambda #g #a #b wpBody fsG : pure_wp (a -> b) =
  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic);
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

val wp_lambda' :
  #g :env ->
  #a :Type ->
  #b :Type ->
  wpFun: (a -> pure_wp b) ->
  spec_env (extend a g) b ->
  spec_env g (x:a -> PURE b (wpFun x))

let wp_lambda' #g #a #b wpFun wpCtx fsG : pure_wp (x:a -> PURE b (wpFun x)) =
  reveal_opaque (`%pure_wp_monotonic) (pure_wp_monotonic) ;
  fun (p:pure_post (x:a -> PURE b (wpFun x))) ->
    (forall x. (* wpFun x (fun _ -> True) ==> *) wpCtx (fs_stack fsG x) (fun _ -> True)) /\
    forall (f:(x:a -> PURE b (wpFun x))).
      (
        forall (q : pure_post b) (x:a).
          wpFun x q ==>
          wpCtx (fs_stack fsG x) q ==>
          q (f x)
      ) ==>
      p f

    // forall x.
    //   // wpFun x (fun r -> exists f. r == f x) ==>
    //   wpCtx (fs_stack fsG x) p

    // forall (f:(x:a -> PURE b (wpFun x))).
    //   (forall (p':pure_post b) (fsG':fs_env (extend a g)).
    //     fsG == fs_tail fsG' ==> wpFun (fs_hd fsG') (fun _ -> True) ==> wpCtx fsG' p' ==>  p' (f (fs_hd fsG'))
    //   ) ==>  p f


val test :
  #g : env ->
  #a : Type ->
  #b : Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  fs_oexp (extend a g) b wpCtx ->
  fs_oexp g (x:a -> PURE b (wpFun x)) (wp_lambda' wpFun wpCtx)

let test #g #a #b wpCtx wpFun body (* : _ by (explode () ; dump "h") *) =
  // assume (forall fsG x. wpCtx (fs_stack fsG x) (fun _ -> True)) ;
  // assume (forall p (f:(x:a -> PURE b (wpFun x))). p f) ;
  // assume (False) ;
  // admit () ;
  // assume (forall (fsG: fs_env g).
  //     forall (p: pure_post (x: a -> PURE b (wpFun x))).
  //       // wp_lambda' wpFun wpCtx fsG p ==>
  //       forall (f:(x:a -> PURE b (wpFun x))).
  //       ((forall (x: a).
  //           (* forall (q: pure_post b) *) (* q' *)(* . *)
  //             // wpFun x q ==>
  //             wpCtx (fs_stack fsG x) (* q' *) (fun _ -> True)
  //               (* (fun r -> p f) *)) /\
  //           p f)) ;
  assume (
    forall (fsG: fs_env g).
      forall (p: pure_post (x: a -> PURE b (wpFun x))) (* (f:fs_oexp (extend a g) b wpCtx) *).
        wp_lambda' wpFun wpCtx fsG p ==>
        (forall (x: a).
            forall (p: pure_post b).
              wpFun x p ==>
              wpCtx (fs_stack fsG x)
                (fun res ->
                    res == body (fs_stack fsG x) ==>
                    (forall (return_val: b). return_val == res ==> p return_val))) /\
        p (fun x -> body (fs_stack fsG x))
  ) ;
  fun fsG x ->
    body (fs_stack fsG x)

// unfold
// val helper_lambdaWP :
//   #g :env ->
//   #a :Type ->
//   #b :Type ->
//   #wp: _ ->
//   #wp': _ ->
//   fs_oexp g (x:a -> PURE b (wp x)) (wp_lambdaWP wp wp') ->
//   fs_oexp (extend a g) b wp'

// let helper_lambdaWP #g #a f fsG =
//   admit () ;
//   f (fs_tail #a fsG) (fs_hd fsG)


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
let helper_seq _ v _ k =
  fun fsG -> M.elim_pure_wp_monotonicity_forall ();
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
                cf:compilable #b (extend a g)
                              wpBody
                              (helper_lambda f) ->
                             // (fun fsG -> f (fs_tail #a fsG) (fs_hd fsG)) ->
                compilable g (wp_lambda #g #a #b wpBody) f

// "Ideal" rule below
| QLambda :
  #g : env ->
  #a : Type ->
  #b : Type ->
  wpCtx : spec_env (extend a g) b ->
  wpFun : (a -> pure_wp b) ->
  #body : fs_oexp (extend a g) b wpCtx ->
  compilable #b (extend a g) wpCtx body ->
  compilable #(x:a -> PURE b (wpFun x)) g (wp_lambda' wpFun wpCtx) (fun fsG x -> body (fs_stack fsG x))

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
  by (unfold_def (`wp_app);
      explode ();
       tadmit ();
      trefl ();
      trefl ();
      trefl ()
     )
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
  : compilable_closed #(bool -> bool) (fun x -> x)
  = fun _ -> CLambda CVar0

let test1_exp' ()
  : Tot (compilable_closed #(bool -> bool -> bool) (fun x y -> y))
  = fun _ ->  CLambda (CLambda CVar0)

let test_fapp1 ()
  : compilable_closed #((unit -> unit) -> unit) (fun f -> f ())
  = fun _ -> CLambda (CApp CVar0 CUnit)

let test_fapp2 ()
  : compilable_closed #((bool -> bool -> bool) -> bool) (fun f -> f true false)
  = fun _ -> CLambda (CApp (CApp CVar0 CTrue) CFalse)

let test4_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> x)
  = fun _ -> CLambda (CLambda (CLambda CVar2))

let test5_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x -> fun y z -> y)
  = fun _ -> CLambda (CLambda (CLambda CVar1))

let test6_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> z)
  = fun _ -> CLambda (CLambda (CLambda CVar0))

[@expect_failure]
let test4_exp'' ()
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = fun _ -> CLambda (CLambda (CLambda CVar0))

let test1_hoc ()
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  = fun _ -> CLambda (CApp CVar0 CFalse)

let test2_if0 ()
  : compilable_closed #(bool) (if true then false else true)
  = fun _ -> (CIf CTrue CFalse CTrue)

let test2_if ()
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  = fun _ -> CLambda (CIf CVar0 CFalse CTrue)

#pop-options

unfold
let on_true (b : bool) : Pure bool (requires b == true) (ensures fun r -> r == b) =
  b

[@@expect_failure]
let test_on_true ()
  : compilable_closed #(b: bool -> Pure bool (requires b == true) (ensures fun r -> r == b)) on_true
=
  // let wp : bool -> pure_wp bool = _ in
  // let wp' : spec_env (extend bool empty) bool = fun fsG p -> True in
  // fun _ -> CLambdaDepWP #_ #bool #bool wp wp' CVar0
  fun _ -> CLambdaDepWP #_ #bool #bool _ _ CVar0

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
  = fun _ -> CLambda (CIf CVar0
                       (CLambda #_ #_ #_ #_ #myf CVar1) // TODO: why cannot it infer myf?
                       (CLambda #_ #_ #_ #_ #myid CVar0))

let test1_if ()
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  = fun _ -> CLambda (CLambda (CIf CVar1 CFalse CVar0))

let test1_comp_ref ()
  : compilable_closed #(x:bool{x == true} -> x:bool{x == true}) (fun x -> x)
  = fun _ -> CLambda CVar0

let test1_erase_ref ()
  : compilable_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = fun _ -> CLambda (CRefinement _ CVar0)

open Examples

let test_erase_refine_again ()
  : compilable_closed #(x:bool{p_ref x} -> x:bool{p_ref x}) (fun x -> x)
  = fun _ -> CLambda (CRefinement _ (CRefinement _ CVar0))

[@expect_failure]
let test_just_false
  : compilable_closed #(bool -> (x:bool{x == true})) (fun x -> false)
  = fun _ -> CLambda (CRefinement _ CFalse)

let test_just_true' ()
  : compilable_closed just_true
  = fun _ -> CLambda (CRefinement _ CTrue)

let test_moving_ref' ()
  : compilable_closed moving_ref
  = fun _ -> CLambda (CRefinement _ CUnit)

let test_always_false' ()
  : compilable_closed always_false
  = fun _ -> CLambda (CRefinement _ (CIf CVar0 (CFalse) CVar0))

let test_always_false'' ()
  : Tot (compilable_closed always_false)
  by (norm [delta_only [`%always_false]]) // TODO: why is the unfolding necessary?
  = fun _ ->
    CLambda (CIf CVar0
                (CRefinement (fun y -> True) CFalse)
                (CRefinement (fun y -> True) CVar0))

let test_always_false_complex' ()
  : compilable_closed always_false_complex
  = fun _ -> CLambda (CRefinement _ (CIf CVar0 (CIf CVar0 CFalse CTrue) CFalse))

let test_always_false_complex'' ()
  : compilable_closed always_false_complex
  = fun _ -> CLambda (CIf CVar0 (CIf CVar0 (CRefinement _ CFalse) (CRefinement _ CTrue)) (CRefinement _ CFalse))

let test_always_false_ho ()
  : compilable_closed always_false_ho
  = fun _ -> CLambda (CIf (CRefinement _ (CApp CVar0 CUnit)) (CRefinement _ CFalse) (CRefinement _ CTrue))

let test_if_x' ()
  : compilable_closed if_x
  by (norm [delta_only [`%if_x]]) // TODO: why is the unfolding necessary?
  = fun _ -> CLambda (CLambda (CIf CVar0 (CApp CVar1 (CRefinement _ CVar0)) CFalse))

let test_seq_basic' ()
  : compilable_closed seq_basic
  = fun _ -> CLambda (CSeq _ (CApp CVar0 CUnit) CUnit)

let test_seq_qref' ()
  : compilable_closed seq_qref
  = fun _ -> CLambda (CSeq _ (CApp CVar0 CUnit) (CRefinement _ CUnit))

let test_seq_p_implies_q' ()
  : compilable_closed seq_p_implies_q
  = fun _ -> CLambda (CLambda (CSeq _ (CApp CVar1 CVar0) (CRefinement _ CVar0)))

let test_if_seq' ()
  : compilable_closed if_seq
  by (norm [delta_only [`%if_seq]]) // TODO: why is the unfolding necessary?
  = fun _ -> CLambda (CLambda (
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
  : compilable_closed context
  by (norm [delta_only [`%context]]; tadmit ()) // TODO: why is the unfolding necessary? // TODO: why is the tadmit necessary?
  = fun _ ->
    // TODO: why does it fail here?
    CLambda (CLambda (CIf CVar1
                          (CApp CVar0 (CRefinement _ CVar1))
                          (CLambda #_ #_ #_ #_ #(fun _ y -> y) CVar0)))
