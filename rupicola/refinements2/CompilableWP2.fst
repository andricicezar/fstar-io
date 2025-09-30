module CompilableWP2

open FStar.Tactics.V2

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

unfold let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
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

val helper_var0 : g:env ->
                 a:Type ->
                 fs_oexp (extend a g) a (fun fsG -> ret (fs_hd fsG))
let helper_var0 g a fsG : PURE a (ret (fs_hd fsG)) =
  fs_hd fsG

val helper_var1 : g:env ->
                  a:Type ->
                  b:Type ->
                  fs_oexp (extend b (extend a g)) a (fun fsG -> ret (fs_hd (fs_tail #b fsG)))
let helper_var1 g a b fsG = fs_hd (fs_tail #b fsG)

val helper_var2 : g:env ->
                  a:Type ->
                  b:Type ->
                  c:Type ->
                  fs_oexp (extend c (extend b (extend a g))) a (fun fsG -> ret (fs_hd (fs_tail #b (fs_tail #c fsG))))
let helper_var2 g a b c fsG = fs_hd (fs_tail #b (fs_tail #c fsG))

val helper_unit : g:env -> fs_oexp g unit (fun _ -> ret ())
let helper_unit g = fun _ -> ()

val helper_true : g:env -> fs_oexp g bool (fun _ -> ret true)
let helper_true g = fun _ -> true

val helper_false : g:env -> fs_oexp g bool (fun _ -> ret false)
let helper_false g = fun _ -> false

val helper_app: #g :env ->
                #a :Type ->
                #b :Type ->
                wpF : spec_env g (a -> b) ->
                f :fs_oexp g (a -> b) wpF ->
                wpX : spec_env g a ->
                x :fs_oexp g a wpX ->
                fs_oexp g b
                  (fun fsG ->
                    pure_bind_wp (a -> b) b (wpF fsG) (fun f' ->
                      pure_bind_wp a b (wpX fsG) (fun x' ->
                       ret (f' x'))))
let helper_app _ f _ x : (fs_oexp _ _ _) by (unfold_def (`ret))=
  fun fsG ->
    M.elim_pure_wp_monotonicity_forall ();
    (f fsG) (x fsG)

val helper_if : #g :env ->
                #a :Type ->
                wpC : spec_env g bool ->
                c   : fs_oexp g bool wpC ->
                wpT : spec_env g a ->
                t   : fs_oexp g a wpT ->
                wpE : spec_env g a ->
                e   : fs_oexp g a wpE ->
                fs_oexp g a
                  (fun fsG ->
                    pure_bind_wp bool a (wpC fsG) (fun r ->
                      pure_if_then_else _ r (wpT fsG) (wpE fsG)))
let helper_if _ c _ t _ e =
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

val helper_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                wpBody:spec_env (extend a g) b ->
                f :fs_oexp g (a -> b) (wp_lambda wpBody) ->
                fs_oexp (extend a g) b wpBody
let helper_lambda #g #a _ f =
  fun fsG -> f (fs_tail #a fsG) (fs_hd fsG)

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
                compilable #b g _ (helper_app wpF f wpX x)

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
                compilable g _ (helper_if wpC c wpT t wpE e)

| CLambda     : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpBody:spec_env (extend a g) b ->
                #f :fs_oexp g (a -> b) (wp_lambda wpBody) ->
                cf:compilable #b (extend a g)
                              wpBody
                              (helper_lambda wpBody f) ->
                             // (fun fsG -> f (fs_tail #a fsG) (fs_hd fsG)) ->
                compilable g (wp_lambda #g #a #b wpBody) f

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

type compilable_closed #a (#wp:spec_env empty a) (x:a) =
  squash (forall fsG. wp fsG <= pure_return _ x) -> compilable empty wp (fun _ -> x)

type compilable_debug #a (wp:spec_env empty a) (x:a) =
  compilable_closed #a #wp x

//type compilable_debug' #a wp (x:a) =
// unit -> PURE (compilable_closed #a #wp x) (fun p -> forall fsG. wp fsG <= )

#set-options "--split_queries always --no_smt"

let test2_var
  : compilable (extend unit (extend unit empty)) _ (fun fsG -> fs_hd (fs_tail fsG))
  = CVar1

let test1_exp ()
  : Tot (compilable_closed #(bool -> bool) (fun x -> x)
  ) by (
    let x = implies_intro () in
    assumption ())
  = fun _ -> CLambda #_ #_ #_ #_ #_ (CVar0 #_ #_)

let test1_exp' ()
  : Tot (compilable_closed #(bool -> bool -> bool) (fun x y -> y))
  by (
    set_guard_policy Drop;
    let x = implies_intro () in
    split ();
    assumption ();
    let _ = forall_intro () in
    let h = implies_intro () in
    assumption ())
  = fun _ ->  CLambda (CLambda CVar0)

let test_app0 ()
  : Tot (compilable (extend (unit -> unit) empty) _ (fun fsG -> fs_hd fsG ()))
  by (
    let fsG = forall_intro () in
    let p = forall_intro () in
    let h = implies_intro () in
    let u = forall_intro () in
    tadmit ())
  = CApp CVar0 CUnit

// FIXME, why does it need tactics to do such simple proofs?
let test_app1 ()
  : Tot (compilable (extend (bool -> bool -> bool) empty) _ (fun fsG -> ((fs_hd fsG) true) false))
  by (tadmit ())
     //explode (); dump "H";
     // rewrite_eqs_from_context (); assumption ();
     // trefl ();
     // trefl ();
     // trefl ())
  = CApp (CApp CVar0 CTrue) CFalse

let test ()
  : Tot (unit -> unit)
  = fun x -> x

let test2 ()
  : Tot ((unit -> unit) -> unit)
   = fun f -> f ()

let test_fapp1 ()
  : compilable_closed #((unit -> unit) -> unit) (fun f -> f ())
  by (
    let x = implies_intro () in
    // assumption ();
    tadmit ()
  )
  = fun _ -> CLambda (CApp CVar0 CUnit)

let test_fapp2 ()
  : compilable_closed #((bool -> bool -> bool) -> bool) (fun f -> f true false)
  by (
    let _ = forall_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CApp (CApp CVar0 CTrue) CFalse)

let test4_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> x)
  by (
    set_guard_policy Drop;

    let _ = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    let _ = forall_intro () in
    let _ = implies_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CLambda (CLambda CVar2))

let test5_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> y)
  by (
    set_guard_policy Drop;

    let _ = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    let _ = forall_intro () in
    let _ = implies_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CLambda (CLambda CVar1))

let test6_exp' ()
  : compilable_closed #(bool -> bool -> bool -> bool) (fun x y z -> z)
  by (
    set_guard_policy Drop;

    let _ = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    let _ = forall_intro () in
    let _ = implies_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CLambda (CLambda CVar0))

[@expect_failure]
let test4_exp' ()
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = fun _ -> CLambda (CLambda (CLambda CVar0))

let test1_hoc ()
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  by (
    let x = forall_intro () in
    assumption ())
  = fun _ -> CLambda (CApp CVar0 CFalse)

let test2_if ()
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in

    compute (); trefl ())
  = fun _ -> CLambda (CIf CVar0 CFalse CTrue)

let test3_if_ho ()
  : compilable_closed #(bool -> (bool -> bool)) (fun x -> if x then (fun y -> x) else (fun z -> z))
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    split ();

    tadmit ();


    let _ = forall_intro () in
    let _ = implies_intro () in
    split ();

    tadmit ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    let _ = forall_intro () in
    let _ = implies_intro () in

    split ();
    tadmit ();

    let _ = forall_intro () in
    let _ = implies_intro () in

    tadmit ()

  )
  = fun _ -> CLambda (CIf CVar0
                       (CLambda #_ #_ #_ #_ #(fun fsG y -> fs_hd fsG) CVar1)
                       (CLambda #_ #_ #_ #_ #(fun fsG z -> z) CVar0))

let test1_if ()
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let h = implies_intro () in

    split ();
    assumption ();

    let _ = forall_intro () in
    let h2 = implies_intro () in
    let _ = forall_intro () in
    let h2 = implies_intro () in

    compute (); trefl ())
  = fun _ -> CLambda (CLambda (CIf CVar1 CFalse CVar0))

let test1_comp_ref ()
  : compilable_closed #(x:bool{x == true} -> x:bool{x == true}) (fun x -> x)
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    assumption ()
  )
  = fun _ -> CLambda CVar0

let test1_erase_ref ()
  : compilable_closed #(x:bool{x == true} -> bool) (fun x -> x)
  by (
    let x = implies_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CRefinement _ CVar0)

open Examples

let test_erase_refine_again ()
  : compilable_closed #(x:bool{p_ref x} -> x:bool{p_ref x}) (fun x -> x)
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CRefinement _ (CRefinement _ CVar0))

[@expect_failure]
let test_just_false
  : compilable_closed #(bool -> (x:bool{x == true})) (fun x -> false)
  = fun _ -> CLambda (CRefinement _ CFalse)

let test_just_true' ()
  : compilable_closed test_just_true
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    assumption ()
  )
  = fun _ -> CLambda (CRefinement _ CTrue)

let test_moving_ref' ()
  : compilable_closed test_moving_ref
  by (
    set_guard_policy Drop;
    let x = forall_intro () in
    tadmit ()
 //   assumption ();
  )
  = fun _ -> CLambda (CRefinement _ CUnit)

let test_always_false' ()
  : compilable_closed test_always_false
  by (
    set_guard_policy Drop;
    let _ = forall_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    compute (); trefl ()
  )
  = fun _ -> CLambda (CRefinement _ (CIf CVar0 (CFalse) CVar0))

let test_always_false'' ()
  : Tot (compilable_closed test_always_false)
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    compute (); trefl ()
  )
  = fun _ ->
    CLambda (CIf CVar0 (CRefinement _ CFalse) (CRefinement _ CVar0))

let test_always_false_complex' ()
  : compilable_closed test_always_false_complex
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    compute (); trefl ()
  )
  = fun _ -> CLambda (CRefinement _ (CIf CVar0 (CIf CVar0 CFalse CTrue) CFalse))

let test_always_false_complex'' ()
  : compilable_closed test_always_false_complex
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    compute (); trefl ()
  )
  = fun _ -> CLambda (CIf CVar0 (CIf CVar0 (CRefinement _ CFalse) (CRefinement _ CTrue)) (CRefinement _ CFalse))

let test_always_false_ho ()
  : compilable_closed test_always_false_ho
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    compute (); trefl ()
  )
  = fun _ -> CLambda (CIf (CRefinement _ (CApp CVar0 CUnit)) (CRefinement _ CFalse) (CRefinement _ CTrue))

let test_if_x' ()
  : compilable_closed test_if_x
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in

    split ();
    assumption ();
    let _ = forall_intro () in
    let _ = implies_intro () in
    let _ = forall_intro () in
    let _ = implies_intro () in
    compute (); trefl ()
  )
  = fun _ -> CLambda (CLambda (CIf CVar0 (CApp CVar1 (CRefinement _ CVar0)) CFalse))

let test_seq_basic' ()
  : compilable_closed test_seq_basic
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    tadmit ()
  )
  = fun _ -> CLambda (CSeq _ (CApp CVar0 CUnit) CUnit)

let test_seq_qref' ()
  : compilable_closed test_seq_qref
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    tadmit ()
  )
  = fun _ -> CLambda (CSeq _ (CApp CVar0 CUnit) (CRefinement _ CUnit))

let test_seq_p_implies_q' ()
  : compilable_closed test_seq_p_implies_q
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in

    assumption ()
  )
  = fun _ -> CLambda (CLambda (CSeq _ (CApp CVar1 CVar0) (CRefinement _ CVar0)))

let test_if_seq' ()
  : compilable_closed test_if_seq
  by (
    set_guard_policy Drop;
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    split ();
    assumption ();

    let _ = forall_intro () in
    let _ = implies_intro () in
    let _ = forall_intro () in
    let _ = implies_intro () in

    compute (); trefl ()
  )
  = fun _ -> CLambda (CLambda (
     CIf CVar0
       (CSeq _ (CApp CVar1 (CRefinement _ CVar0))
                     (CRefinement _ CVar0))
       (CRefinement _ CVar0)))

let test_context' ()
  : compilable_closed test_context
  by (
    set_guard_policy Drop;
    tadmit ())
  = fun _ -> CLambda (CLambda (CIf CVar1
                          (CApp CVar0 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar1))
                          (CLambda #_ #_ #_ #_ #(fun fsG y -> y) CVar0)))
