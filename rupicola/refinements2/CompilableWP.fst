module CompilableWP

open FStar.Tactics

assume val z : nat

let f () : Pure (nat -> nat) (z > 0) (fun _ -> True) by (dump "H") =
  (fun x -> x / z)


(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires M.is_monotonic wp)
      (ensures pure_wp_monotonic a wp)
    [SMTPat (pure_wp_monotonic a wp)]
  = M.intro_pure_wp_monotonicity wp

unfold
let pure_trivial #a : pure_wp a =
  fun p -> forall r. p r

unfold let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
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
assume val get_v : #g:env -> fs_env g -> x:var{Some? (g x)} -> Some?.v (g x)
assume val fs_extend : #g:env -> fsG:fs_env g -> #t:Type0 -> t -> fs_env (extend t g)
assume val fs_shrink : #t:Type0 -> #g:env -> fs_env (extend t g) -> fs_env g

assume val lem_fs_extend #g (fsG:fs_env g) #t (v:t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG x == get_v (fs_extend fsG v) (x+1)) /\
  get_v (fs_extend fsG v) 0 == v)
  [SMTPat (fs_extend fsG v)]

assume val lem_fs_shrink #g #t (fsG:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG (x+1) == get_v (fs_shrink fsG) x))
  [SMTPat (fs_shrink fsG)]

assume val shrink_extend_inverse #g (fsG:fs_env g) #t (x:t) : Lemma (fs_shrink (fs_extend fsG x) == fsG)
  [SMTPat (fs_shrink (fs_extend fsG x))]

type spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> PURE a (wpG fsG) // <= ret x} (** this works better than using PURE **)

unfold
val wp_ref :
  #g:env ->
  #a:Type ->
  ref1:(a -> Type0) ->
  ref2:(a -> Type0) ->
  wpV:spec_env g (x:a{ref1 x}) ->
  spec_env g (x:a{ref2 x})
let wp_ref #g #a ref1 ref2 wpV =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun fsG (p:pure_post (x:a{ref2 x})) ->
    wpV fsG (fun r -> ref2 r /\ p r)

unfold
val helper_ref : #g:env ->
                 #a:Type ->
                 #ref1:(a -> Type0) ->
                 #ref2:(a -> Type0) ->
                 #wpV:spec_env g (x:a{ref1 x}) ->
                 v:fs_oexp g (x:a{ref1 x}) wpV ->
                 fs_oexp g (x:a{ref2 x}) (wp_ref ref1 ref2 wpV)
let helper_ref #g #a #ref1 #ref2 #wpV v =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun fsG -> v fsG

unfold
val wp_lambda : #g :env ->
                #a :Type ->
                #b :Type ->
                wpBody:spec_env (extend a g) b ->
                spec_env g (a -> b)

let wp_lambda #g #a #b wpBody fsG : pure_wp (a -> b) =
  fun (p:pure_post (a -> b)) ->
    forall (f:a -> b).
      (forall (p':pure_post b) (fsG':fs_env (extend a g)).
        fsG == fs_shrink fsG' ==>  wpBody fsG' p' ==>  p' (f (get_v fsG' 0))
      ) ==>  p f
(**
 //  (forall f. p f) ==>
 //    (forall x. wpBody (fs_extend fsG x) (fun _ -> True)) /\
 //    (forall f. ret f p)


  //  forall (fsG':fs_env (extend a g)). fsG == fs_shrink fsG' ==>
  //    wpBody fsG' (fun r -> forall f. f fsG' (get_v fsG' 0) == r /\ p (f fsG'))
**)

unfold
val helper_lambda : #g :env ->
                    #a :Type ->
                    #b :Type ->
                    wpBody:spec_env (extend a g) b ->
                    f :fs_oexp g (a -> b) (wp_lambda wpBody) ->
                    fs_oexp (extend a g) b wpBody
let helper_lambda #g #a #b wpBody f : fs_oexp (extend a g) b wpBody =
  fun fsG -> f (fs_shrink #a fsG) (get_v fsG 0)

unfold
val helper_var : g:env ->
                 a:Type ->
                 x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                 fs_oexp g a (fun fsG p -> p (get_v fsG x))
let helper_var g a x fsG = get_v fsG x

unfold
val helper_var1 : g:env ->
                  a:Type ->
                  b:Type ->
                  x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                  fs_oexp (extend b g) a (fun fsG p -> p (get_v (fs_shrink #b fsG) x))
let helper_var1 g a b x fsG = get_v (fs_shrink #b fsG) x

unfold
val helper_var2 : g:env ->
                  a:Type ->
                  b:Type ->
                  c:Type ->
                  x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                  fs_oexp (extend c (extend b g)) a (fun fsG p -> p (get_v (fs_shrink #b (fs_shrink #c fsG)) x))
let helper_var2 g a b c x fsG = get_v (fs_shrink #b (fs_shrink #c fsG)) x

unfold
val fapp_wp : #g :env ->
              #a :Type ->
              #b :Type ->
              wpF : spec_env g (a -> b) ->
              wpX : spec_env g a ->
              spec_env g b
let fapp_wp #g #a #b wpF wpX fsG : pure_wp b =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun (p:pure_post b) -> wpF fsG (fun f' -> wpX fsG (fun x' -> p (f' x')))

unfold
val helper_fapp : g :env ->
                  a :Type ->
                  b :Type ->
                  wpF : spec_env g (a -> b) ->
                  f :fs_oexp g (a -> b) wpF ->
                  wpX : spec_env g a ->
                  x :fs_oexp g a wpX ->
                  fs_oexp g b (fapp_wp wpF wpX)

let helper_fapp g a b wpF f wpX x : fs_oexp g b (fapp_wp wpF wpX) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun fsG -> (f fsG) (x fsG)

unfold
val if_wp : #g :env ->
            #a :Type ->
            wpC : spec_env g bool ->
            wpT : spec_env g a ->
            wpE : spec_env g a ->
            spec_env g a
let if_wp #g #a wpC wpT wpE fsG : pure_wp a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun (p:pure_post a) ->
    wpC fsG (fun r -> (r == true ==> wpT fsG p) /\ (r == false ==> wpE fsG p))

unfold
val helper_if : #g :env ->
                #a :Type ->
                #wpC : spec_env g bool ->
                c   : fs_oexp g bool wpC ->
                #wpT : spec_env g a ->
                t   : fs_oexp g a wpT ->
                #wpE : spec_env g a ->
                e   : fs_oexp g a wpE ->
                fs_oexp g a (if_wp wpC wpT wpE)
let helper_if c t e fsG =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  if c fsG then t fsG else e fsG

unfold
val wp_seq :     #g:env ->
                 ref1:Type0 ->
                 wpV:spec_env g (x:unit{ref1}) ->
                 #a:Type ->
                 wpK:spec_env g a ->
                 spec_env g a
let wp_seq ref1 wpV wpK fsG =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p -> wpV fsG (fun _ -> wpK fsG p)

unfold
val helper_seq : #g:env ->
                 ref1:Type0 ->
                 #wpV:spec_env g (x:unit{ref1}) ->
                 v:fs_oexp g (x:unit{ref1}) wpV -> (** since this is pure, I don't have to compile it **)

                 #a:Type ->
                 #wpK:spec_env g a ->
                 k:fs_oexp g a wpK ->
                 fs_oexp g a (wp_seq ref1 wpV wpK)
let helper_seq ref1 v k =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun fsG -> v fsG ; k fsG

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env -> compilable g (fun _ p -> p ()) (fun _ -> ())
| CTrue       : #g:env -> compilable g (fun _ p -> p true) (fun _ -> true)
| CFalse      : #g:env -> compilable g (fun _ p -> p false) (fun _ -> false)

(** The following three rules for variables should be generalized. What would be an elegant solution? **)
| CVar0       : #g:env ->
                #a:Type ->
                #_:squash (Some? (g 0) /\ a == Some?.v (g 0)) ->
                compilable #a g _ (helper_var g a 0)
| CVar1       : #g:env ->
                #a:Type ->
                #b:Type ->
                #_:squash (Some? (g 0) /\ a == Some?.v (g 0)) ->
 //               compilable #a (extend b g) (fun fsG p -> p (get_v fsG (x+1))) (fun fsG -> get_v fsG (x+1)) ->
                compilable #a (extend b g) _ (helper_var1 g a b 0)
| CVar2       : #g:env ->
                #a:Type ->
                #b:Type ->
                #c:Type ->
                #_:squash (Some? (g 0) /\ a == Some?.v (g 0)) ->
 //               compilable #a (extend c (extend b g)) (fun fsG p -> p (get_v fsG (x+2))) (fun fsG -> get_v fsG (x+2)) ->
                compilable #a (extend c (extend b g)) _ (helper_var2 g a b c 0)

| CApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                #f :fs_oexp g (a -> b) wpF ->
                cf:compilable g wpF f ->
                #wpX : spec_env g a ->
                #x :fs_oexp g a wpX ->
                cx:compilable g wpX x ->
                compilable g _ (helper_fapp g a b wpF f wpX x)

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
                cf:compilable #b (extend a g) wpBody (helper_lambda wpBody f) ->
                compilable g _ f

| CRefinement : #g:env ->
                #a:Type ->
                ref1:(a -> Type0) ->
                #ref2:(a -> Type0) ->
                #wpV:spec_env g (x:a{ref1 x}) ->
                #v:fs_oexp g (x:a{ref1 x}) wpV ->
                compilable g wpV v ->
                compilable g _ (helper_ref #g #a #ref1 #ref2 #wpV v)

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
                compilable g _ (helper_seq ref1 v k)


let empty_wp #a (wp:spec_env empty a) : pure_wp a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun p -> forall fsG. wp fsG p

unfold let compilable_closed #a #wp (x:a{forall fsG. wp fsG <= ret x}) =
  compilable empty wp (fun _ -> x)

let test2_var
  : compilable (extend unit (extend unit empty)) _ (fun fsG -> get_v (fs_shrink fsG) 0)
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
  = CLambda (CRefinement (fun x -> x == true) CVar0)

open Examples

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

let test_if_x'
  : compilable_closed test_if_x
  = CLambda (CLambda (CIf CVar0 (CApp CVar1 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar0)) CFalse))

let test_p_implies_q'
  : compilable_closed test_p_implies_q
  = CLambda (CLambda (CSeq q_ref (CApp CVar1 CVar0) (CRefinement p_ref CVar0)))
 // = CLambda (CLambda (CApp (CLambda (CRefinement p_ref #(fun _ -> q_ref) CVar1)) (CApp CVar1 CVar0)))

let test_true_implies_q
  : compilable_closed test_true_implies_q
  = CLambda (CLambda (
     CIf CVar0
         (CSeq q_ref (CApp CVar1 (CRefinement (fun _ -> True) #(fun x -> x == true) CVar0))
                     (CRefinement (fun _ -> True) #(fun x -> x == true ==> q_ref) CVar0))
         (CRefinement (fun _ -> True) #(fun x -> x == true ==> q_ref) CFalse)))
