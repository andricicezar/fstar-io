module CompilableWP

open FStar.Tactics.V2

assume val z : nat

let f () : Pure (nat -> nat) (z > 0) (fun _ -> True) by (dump "H") =
  (fun x -> x / z)


(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

  (**
let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires M.is_monotonic wp)
      (ensures pure_wp_monotonic a wp)
    [SMTPat (pure_wp_monotonic a wp)]
  = M.intro_pure_wp_monotonicity wp **)

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
assume val fs_top : #g:env{Some? (g 0)} -> fs_env g -> Some?.v (g 0)
assume val fs_push : #g:env -> fsG:fs_env g -> #t:Type0 -> t -> fs_env (extend t g)
assume val fs_pop : #t:Type0 -> #g:env -> fs_env (extend t g) -> fs_env g

(**
assume val lem_fs_extend #g (fsG:fs_env g) #t (v:t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG x == get_v (fs_extend fsG v) (x+1)) /\
  get_v (fs_extend fsG v) 0 == v)
  [SMTPat (fs_extend fsG v)]

assume val lem_fs_shrink #g #t (fsG:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG (x+1) == get_v (fs_shrink fsG) x))
  [SMTPat (fs_shrink fsG)]

assume val shrink_extend_inverse #g (fsG:fs_env g) #t (x:t) : Lemma (fs_pop (fs_push fsG x) == fsG)
  [SMTPat (fs_pop (fs_push fsG x))]
**)

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
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  fun (p:pure_post (a -> b)) ->
    forall (f:a -> b).
      (forall (p':pure_post b) (fsG':fs_env (extend a g)).
        fsG == fs_pop fsG' ==>  wpBody fsG' p' ==>  p' (f (fs_top fsG'))
      ) ==>  p f

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env ->
                compilable g
                  (fun _ -> pure_return _ ())
                  (fun _ -> ())
| CTrue       : #g:env ->
                compilable g
                  (fun _ -> pure_return _ true)
                  (fun _ -> true)
| CFalse      : #g:env ->
                compilable g
                  (fun _ -> pure_return _ false)
                  (fun _ -> false)

(** Can we generalize the following three rules? **)
| CVar0       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                compilable #a g
                  (fun fsG -> pure_return _ (fs_top fsG))
                  (fun fsG -> fs_top fsG)
| CVar1       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                #b:Type ->
                compilable #a (extend b g)
                  (fun fsG -> pure_return _ (fs_top (fs_pop #b fsG)))
                  (fun fsG -> fs_top (fs_pop #b fsG))
| CVar2       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                #b:Type ->
                #c:Type ->
                compilable #a (extend c (extend b g))
                  (fun fsG ->
                    pure_return _ (fs_top (fs_pop #b (fs_pop #c fsG))))
                  (fun fsG -> fs_top (fs_pop #b (fs_pop #c fsG)))

| CApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                #f :fs_oexp g (a -> b) wpF ->
                cf:compilable g wpF f ->
                #wpX : spec_env g a ->
                #x :fs_oexp g a wpX ->
                cx:compilable g wpX x ->
                compilable g
                  (fun fsG ->
                    pure_bind_wp _ _ (wpF fsG) (fun f' ->
                      pure_bind_wp _ _ (wpX fsG) (fun x' ->
                        pure_return _ (f' x'))))
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
                    pure_bind_wp _ _ (wpC fsG) (fun r ->
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
                              (fun fsG -> f (fs_pop #a fsG) (fs_top fsG)) ->
                compilable g _ f

| CRefinement : #g:env ->
                #a:Type ->
                ref1:(a -> Type0) ->
                #ref2:(a -> Type0) ->
                #wpV:spec_env g (x:a{ref1 x}) ->
                #v:fs_oexp g (x:a{ref1 x}) wpV ->
                compilable g wpV v ->
                compilable g
                  (fun fsG ->
                    pure_bind_wp (x:a{ref1 x}) (x:a{ref2 x}) (wpV fsG) (fun r ->
                      M.as_pure_wp (fun (p:pure_post (x:a{ref2 x})) -> ref2 r /\ p r)))
//                    pure_bind_wp _ _ (pure_assert_wp0 (ref2 r))
//                      (fun _ -> pure_return (x:a{ref2 x}) r)))

//                   M.elim_pure_wp_monotonicity_forall ();
//                    M.as_pure_wp (fun (p:pure_post (x:a{ref2 x})) ->
//                      wpV fsG (fun r -> ref2 r /\ p r)))
                  (fun fsG ->
                    M.elim_pure_wp_monotonicity_forall ();
                    v fsG)

| CSeq        : #g:env ->
                ref1:Type0 ->
                #wpV:spec_env g (x:unit{ref1}) ->
                #v:fs_oexp g (x:unit{ref1}) wpV ->
                compilable g wpV v -> (** the name compilable is misleading here.
                                         I have to compute the WP of `v` to be able to
                                         compile the entire term **)

                #a:Type ->
                #wpK:spec_env g a ->
                #k:fs_oexp g a wpK ->
                compilable g wpK k ->
                compilable g
                  (fun fsG -> pure_bind_wp (x:unit{ref1}) a (wpV fsG) (fun _ -> wpK fsG))
                  (fun fsG -> M.elim_pure_wp_monotonicity_forall ();
                    v fsG ; k fsG)

type compilable_closed #a #wp (x:a{forall fsG. wp fsG <= ret x}) =
  compilable empty wp (fun _ -> x)

type compilable_debug #a wp (x:a{forall fsG. wp fsG <= ret x}) =
  compilable empty wp (fun _ -> x)

let test2_var
  : compilable (extend unit (extend unit empty)) _ (fun fsG -> fs_top (fs_pop fsG))
  = CVar1

let test1_exp
  : compilable_closed #(unit -> unit) (fun x -> x)
  = CLambda CVar0

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
  = CLambda (CRefinement (fun x -> x == true) #(fun _ -> True) CVar0)

open Examples

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

let test_context
  : (x:bool) -> (f:(x:bool{x == true}) -> bool -> bool) -> bool -> bool
  = fun x f ->
    if x then (f x)
    else (fun y -> y)

// How to make this work?
let test_context'
  : compilable_closed test_context
  = CLambda (CLambda (CIf CVar1
                          (CApp CVar0 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar1))
                          (CLambda #_ #_ #_ #_ #(fun fsG y -> y) CVar0)))

let test_p_implies_q'
  : compilable_debug _ test_p_implies_q
  = CLambda (CLambda (CSeq q_ref (CApp CVar1 CVar0) (CRefinement p_ref CVar0)))
 // = CLambda (CLambda (CApp (CLambda (CRefinement p_ref #(fun _ -> q_ref) CVar1)) (CApp CVar1 CVar0)))

let test_true_implies_q
  : compilable_closed _ test_true_implies_q
  = CLambda (CLambda (
     CIf CVar0
         (CSeq q_ref (CApp CVar1 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar0))
                     (CRefinement (fun _ -> True) #(fun x -> x == true ==> q_ref) CVar0))
         (CRefinement (fun _ -> True) #(fun x -> x == true ==> q_ref) CFalse)))
