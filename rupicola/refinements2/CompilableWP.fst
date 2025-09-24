module CompilableWP

open FStar.Tactics

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

unfold let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
(** Using the ret is nicer, but makes things more fragile **)
unfold let ret #a x : pure_wp a = pure_return a x //fun p -> p x

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
assume val fs_hd : #g:env{Some? (g 0)} -> fs_env g -> Some?.v (g 0)
assume val fs_stack : #g:env -> fsG:fs_env g -> #t:Type0 -> t -> fs_env (extend t g)
assume val fs_tail : #t:Type0 -> #g:env -> fs_env (extend t g) -> fs_env g

type spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> PURE a (wpG fsG)

unfold
val wp_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                wpBody:spec_env (extend a g) b ->
                spec_env g (a -> b)

let wp_lambda #g #a #b wpBody fsG : pure_wp (a -> b) =
  M.as_pure_wp
  fun (p:pure_post (a -> b)) ->
    forall (f:a -> b).
      (forall (p':pure_post b) (fsG':fs_env (extend a g)).
        fsG == fs_tail fsG' ==>  wpBody fsG' p' ==>  p' (f (fs_hd fsG'))
      ) ==>  p f

unfold
val helper_var : g:env{Some? (g 0)} ->
                 a:Type{Some?.v (g 0) == a} ->
                 fs_oexp g a (fun fsG -> pure_return a (fs_hd fsG))
let helper_var g a fsG =
  fs_hd fsG

unfold
val helper_var1 : g:env{Some? (g 0)} ->
                  a:Type{Some?.v (g 0) == a} ->
                  b:Type ->
                  fs_oexp (extend b g) a (fun fsG -> pure_return a (fs_hd (fs_tail #b fsG)))
let helper_var1 g a b fsG = fs_hd (fs_tail #b fsG)

unfold
val helper_var2 : g:env{Some? (g 0)} ->
                  a:Type{Some?.v (g 0) == a} ->
                  b:Type ->
                  c:Type ->
                  fs_oexp (extend c (extend b g)) a (fun fsG -> pure_return a (fs_hd (fs_tail #b (fs_tail #c fsG))))
let helper_var2 g a b c fsG = fs_hd (fs_tail #b (fs_tail #c fsG))

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env ->
                compilable g
                  (fun _ -> pure_return unit ())
                  (fun _ -> ())
| CTrue       : #g:env ->
                compilable g
                  (fun _ -> pure_return bool true)
                  (fun _ -> true)
| CFalse      : #g:env ->
                compilable g
                  (fun _ -> pure_return bool false)
                  (fun _ -> false)

(** Can we generalize the following three rules? **)
| CVar0       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                compilable #a g
                  _
                  (helper_var g a)
| CVar1       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                #b:Type ->
                compilable #a (extend b g)
                  _
                  (helper_var1 g a b)
| CVar2       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                #b:Type ->
                #c:Type ->
                compilable #a (extend c (extend b g))
                  _
                  (helper_var2 g a b c)

| CApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                #f :fs_oexp g (a -> b) wpF ->
                cf:compilable g wpF f ->
                #wpX : spec_env g a ->
                #x :fs_oexp g a wpX ->
                cx:compilable g wpX x ->
                compilable #b g
                  (fun fsG ->
                    pure_bind_wp (a -> b) b (wpF fsG) (fun f' ->
                      pure_bind_wp a b (wpX fsG) (fun x' ->
                       pure_return b (f' x'))))
                  (fun fsG -> M.elim_pure_wp_monotonicity_forall ();
                    (f fsG) (x fsG))

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
                compilable g
                  (fun fsG ->
                    pure_bind_wp bool a (wpC fsG) (fun r ->
                      pure_if_then_else _ r (wpT fsG) (wpE fsG)))
                  (fun fsG ->
                    M.elim_pure_wp_monotonicity_forall ();
                    if c fsG then t fsG else e fsG)

| CLambda     : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpBody:spec_env (extend a g) b ->
                #f :fs_oexp g (a -> b) (wp_lambda wpBody) ->
                cf:compilable #b (extend a g)
                              wpBody
                              (fun fsG -> f (fs_tail #a fsG) (fs_hd fsG)) ->
                compilable g (wp_lambda wpBody) f

| CRefinement : #g:env ->
                #a:Type ->
                ref1:(a -> Type0) ->
                #ref2:(a -> Type0) ->
                #wpV:spec_env g (x:a{ref1 x}) ->
                #v:fs_oexp g (x:a{ref1 x}) wpV ->
                compilable #(x:a{ref1 x}) g wpV v ->
                compilable #(x:a{ref2 x}) g
                  (fun fsG ->
                    pure_bind_wp (x:a{ref1 x}) (x:a{ref2 x}) (wpV fsG) (fun r ->
                      M.as_pure_wp (fun (p:pure_post (x:a{ref2 x})) -> ref2 r /\ p r)))
//                    pure_bind_wp _ _ (pure_assert_wp0 (ref2 r))
//                      (fun _ -> pure_return (x:a{ref2 x}) r)))
                  (fun fsG -> M.elim_pure_wp_monotonicity_forall ();
                    v fsG)
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
                compilable #a g
                  (fun fsG -> pure_bind_wp (x:unit{ref1}) a (wpV fsG) (fun _ -> wpK fsG))
                  (fun fsG -> M.elim_pure_wp_monotonicity_forall ();
                    v fsG ; k fsG)

type compilable_closed #a #wp (x:a{forall fsG. wp fsG <= ret x}) =
  compilable empty wp (fun _ -> x)

type compilable_debug #a wp (x:a) (_:squash (forall fsG. wp fsG <= ret x)) =
  compilable empty wp (fun _ -> x)

let test2_var
  : compilable (extend unit (extend unit empty)) _ (fun fsG -> fs_hd (fs_tail fsG))
  = CVar1

let test_app0 ()
  : (compilable (extend (unit -> unit) empty) _ (fun fsG -> fs_hd fsG ()))
  = CApp CVar0 CUnit

[@expect_failure] // FIXME
let test_app1 ()
  : Tot (compilable (extend (unit -> unit -> unit) empty) _ (fun fsG -> fs_hd fsG () ()))
  = CApp (CApp CVar0 CUnit) CUnit

let test1_exp
  : compilable_closed #(unit -> unit) (fun x -> x)
  = CLambda CVar0

let test_fapp1 ()
  : Tot (compilable_debug #((unit -> unit) -> unit) _ (fun f -> f ()) ())
  = CLambda (CApp CVar0 CUnit)

[@expect_failure] // FIXME, depends on test_app1
let test_fapp2
  : compilable_closed #((unit -> unit -> unit) -> unit) (fun f -> f () ())
  = CLambda (CApp (CApp CVar0 CUnit) CUnit)

let test4_exp'
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = CLambda (CLambda (CLambda CVar1))

let test1_hoc
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  = CLambda (CApp CVar0 CFalse)

let test2_if
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  = CLambda (CIf CVar0 CFalse CTrue)

let test1_if
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  = CLambda (CLambda (CIf CVar1 CFalse CVar0))

let test1_comp_ref
  : compilable_closed #(x:bool{x == true} -> x:bool{x == true}) (fun x -> x)
  = CLambda CVar0

let test1_erase_ref
  : compilable_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = CLambda (CRefinement (fun x -> x == true) CVar0)

open Examples

let test_erase_refine_again
  : compilable_closed #(x:bool{p_ref x} -> x:bool{p_ref x}) (fun x -> x)
  = CLambda (CRefinement (fun _ -> True) (CRefinement p_ref #(fun _ -> True) CVar0))

[@expect_failure]
let test_just_false
  : compilable_closed #(bool -> (x:bool{x == true})) (fun x -> false)
  = CLambda (CRefinement (fun x -> True) #(fun x -> x == true) CFalse)

let test_just_true'
  : compilable_closed test_just_true
  = CLambda (CRefinement _ CTrue)

let test_moving_ref'
  : compilable_closed test_moving_ref
  = CLambda (CRefinement _ CUnit)

let test_always_false'
  : compilable_closed test_always_false
  = CLambda (CRefinement _ (CIf CVar0 (CFalse) CVar0))

let test_always_false''
  : compilable_closed test_always_false
  = CLambda (CIf CVar0 (CRefinement (fun _ -> True) CFalse) (CRefinement (fun _ -> True) CVar0))

let test_always_false_complex'
  : compilable_closed test_always_false_complex
  = CLambda (CRefinement _ (CIf CVar0 (CIf CVar0 CFalse CTrue) CFalse))

let test_always_false_complex''
  : compilable_closed test_always_false_complex
  = CLambda (CIf CVar0 (CIf CVar0 (CRefinement (fun _ -> True) CFalse) (CRefinement (fun _ -> True) CTrue)) (CRefinement (fun _ -> True) CFalse))

let test_always_false_ho
  : compilable_closed test_always_false_ho
  = CLambda (CIf (CRefinement (fun x -> x == true) (CApp CVar0 CUnit)) (CRefinement (fun _ -> True) CFalse) (CRefinement (fun _ -> True) CTrue))

let test_if_x'
  : compilable_closed test_if_x
  = CLambda (CLambda (CIf CVar0 (CApp CVar1 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar0)) CFalse))

let test_seq_basic' ()
  : compilable_closed test_seq_basic
  = CLambda (CSeq True (CApp CVar0 CUnit) CUnit)

let test_seq_qref'
  : compilable_closed test_seq_qref
  = CLambda (CSeq q_ref (CApp CVar0 CUnit) (CRefinement _ CUnit))


[@expect_failure] // FIXME
let test_seq_p_implies_q'
  : compilable_debug _ test_seq_p_implies_q _
  = CLambda (CLambda (CSeq q_ref (CApp CVar1 CVar0) (CRefinement p_ref #(fun _ -> q_ref) CVar0)))

[@expect_failure] // FIXME
let test_true_implies_q
  : compilable_debug _ test_if_seq _
  = CLambda (CLambda (
     CIf CVar0
         (CSeq q_ref (CApp CVar1 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar0))
                     (CRefinement (fun _ -> True) #(fun r -> r == true ==>  q_ref) CVar0))
         (CRefinement (fun _ -> True) #(fun r -> r == true ==>  q_ref) CVar0)))

[@expect_failure] // FIXME, depends on test_app1
let test_context'
  : compilable_closed test_context
  = CLambda (CLambda (CIf CVar1
                          (CApp CVar0 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar1))
                          (CLambda #_ #_ #_ #_ #(fun fsG y -> y) CVar0)))
