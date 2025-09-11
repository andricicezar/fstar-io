module CompilableWP

open FStar.Tactics

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

let intro_pure_wp_monotonicity (#a:Type) (wp:pure_wp' a)
  : Lemma
      (requires M.is_monotonic wp)
      (ensures pure_wp_monotonic a wp)
    [SMTPat (pure_wp_monotonic a wp)]
  = M.intro_pure_wp_monotonicity wp

let pure_wp (a: Type) = wp:pure_wp' a{M.is_monotonic wp}

unfold
let pure_trivial #a : pure_wp a =
  fun p -> forall r. p r

unfold let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
unfold let ret #a x : pure_wp a = pure_return a x //fun p -> p x

(** Typing environment **)
type typsr = Type0
let get_Type (t:typsr) = t
type env = var -> option typsr
let empty : env = fun _ -> None

(* we only need extend at 0 *)
let extend (t:typsr) (g:env)
  : env
  = fun y -> if y = 0 then Some t
          else g (y-1)

(** F* evaluation environment **)
assume val fs_env (g:env) : Type u#0
assume val fs_empty : fs_env empty
assume val get_v : #g:env -> fs_env g -> x:var{Some? (g x)} -> get_Type (Some?.v (g x))
assume val fs_extend : #g:env -> fsG:fs_env g -> #t:typsr -> get_Type t -> fs_env (extend t g)
assume val fs_shrink : #t:typsr -> #g:env -> fs_env (extend t g) -> fs_env g

(**
assume val lem_fs_extend #g (fsG:fs_env g) #t (v:get_Type t) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG x == get_v (fs_extend fsG v) (x+1)) /\
  get_v (fs_extend fsG v) 0 == v)
  [SMTPat (fs_extend fsG v)]

assume val lem_fs_shrink #g #t (fsG:fs_env (extend t g)) : Lemma (
  (forall (x:var). Some? (g x) ==>  get_v fsG (x+1) == get_v (fs_shrink fsG) x))
  [SMTPat (fs_shrink fsG)]

assume val shrink_extend_inverse #g (fsG:fs_env g) #t (x:get_Type t) : Lemma (fs_shrink (fs_extend fsG x) == fsG)
  [SMTPat (fs_shrink (fs_extend fsG x))]
**)

type spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> x:a{wpG fsG <= ret x} (** this works better than using PURE **)

noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env -> compilable g (fun _ -> ret ()) (fun _ -> ())
| CTrue       : #g:env -> compilable g (fun _ -> ret true) (fun _ -> true)
| CFalse      : #g:env -> compilable g (fun _ -> ret false) (fun _ -> false)
(** The following three rules for variables should be generalized. What would be an elegant solution? **)
| CVar        : #g:env ->
                #a:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable #a g (fun fsG -> ret (get_v fsG x)) (fun fsG -> get_v fsG x)
| CVarShrink1 : #g:env ->
                #a:Type ->
                #b:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable #a (extend b g) (fun fsG -> ret (get_v fsG (x+1))) (fun fsG -> get_v fsG (x+1)) ->
                compilable #a (extend b g) (fun fsG -> ret (get_v (fs_shrink #b fsG) x)) (fun fsG -> get_v (fs_shrink #b fsG) x)
| CVarShrink2 : #g:env ->
                #a:Type ->
                #b:Type ->
                #c:Type ->
                #x:var{Some? (g x) /\ a == Some?.v (g x)} ->
                compilable #a (extend c (extend b g)) (fun fsG -> ret (get_v fsG (x+2))) (fun fsG -> get_v fsG (x+2)) ->
                compilable #a (extend c (extend b g)) (fun fsG -> ret (get_v (fs_shrink #b (fs_shrink #c fsG)) x)) (fun fsG -> get_v (fs_shrink #b (fs_shrink #c fsG)) x)

| CApp        : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpF : spec_env g (a -> b) ->
                #f :fs_oexp g (a -> b) wpF ->
                cf:compilable g wpF f ->
                #wpX : spec_env g a ->
                #x :fs_oexp g a wpX ->
                cx:compilable g wpX x ->
                compilable g (fun fsG p -> wpX fsG (fun x' -> wpF fsG (fun f' -> p (f' x')))) (fun fsG -> (f fsG) (x fsG))

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
                compilable g (fun fsG p -> wpC fsG (fun r -> (r ==> wpT fsG p) /\ (~r ==> wpE fsG p))) (fun fsG -> if c fsG then t fsG else e fsG)

| CLambda     : #g :env ->
                #a :Type ->
                #b :Type ->
                #wpBody:spec_env (extend a g) b ->
   //             #f :fs_oexp g (a -> b) (fun fsG p -> forall (x:a). wpBody (fs_extend fsG x) (fun r -> forall f. f x == r ==> p f)) ->
                #f :fs_oexp g (a -> b) (fun fsG p -> forall (fsG':fs_env (extend a g)). fsG == fs_shrink fsG' ==>  wpBody fsG' (fun r -> forall f. f fsG' (get_v fsG' 0) == r ==> p (f fsG'))) ->
                cf:compilable #b (extend a g) wpBody (fun fsG -> admit (); f (fs_shrink fsG) (get_v fsG 0)) ->
                compilable g (fun fsG p -> forall (fsG':fs_env (extend a g)). fsG == fs_shrink fsG' ==>  wpBody fsG' (fun r -> forall f. f fsG' (get_v fsG' 0) == r ==> p (f fsG'))) f
 ///               compilable g (fun fsG p -> forall (x:a). wpBody (fs_extend fsG x) (fun r -> forall f. f x == r ==> p f)) f

unfold let compilable_closed #a #wp (x:a{forall fsG. wp fsG <= ret x}) = compilable empty wp (fun _ -> x)

let test2_var
  : compilable (extend unit (extend unit empty)) _ (fun fsG -> get_v (fs_shrink fsG) 0)
  = CVarShrink1 CVar

let _ =
  assert ((fun p ->
            forall (x: unit) (y: unit) (z: unit).
              ret (get_v (fs_shrink (fs_extend (fs_extend (fs_extend fs_empty #unit x) #unit y) #unit z))
                    0)
                (fun _ ->
                    forall (f: (_: (_: unit -> unit){l_True}))
                      (f: (_: (_: unit -> _: unit -> unit){l_True}))
                      (f: (_: (_: unit -> _: unit -> _: unit -> unit){l_True})).
                      p f)) <=
        ret (fun x y z -> y)) by (
          l_to_r [`shrink_extend_inverse;`lem_fs_extend];
          unfold_def (`ret);
          unfold_def (`(<=));
          norm [iota];
          dump "H")

let test4_exp'
  : compilable_closed #(unit -> unit -> unit -> unit) (fun x y z -> y)
  = CLambda (CLambda (CLambda (CVarShrink1 (CVar))))

let test1_hoc
  : compilable_closed #((bool -> bool) -> bool) (fun f -> f false)
  = CLambda (CApp CVar CFalse)

let test2_if
  : compilable_closed #(bool -> bool) (fun x -> if x then false else true)
  = CLambda (CIf CVar CFalse CTrue)

let test1_if
  : compilable_closed #(bool -> bool -> bool) (fun x y -> if x then false else y)
  = CLambda (CLambda (CIf (CVarShrink1 CVar) CFalse CVar))

let test1_comp_ref
  : compilable_closed #(x:bool{x == true} -> x:bool{x == true}) (fun x -> x)
  = CLambda CVar

[@expect_failure]
let test_pm2
  : compilable_closed
      #(bool -> y:bool{y == false})
      (fun x -> if x then if x then false else true else false)
  = CLambda (CIf CVar (CIf CVar CFalse CTrue) CFalse)

[@expect_failure]
let test1_erase_ref
  : compilable_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = CLambda CVar

[@expect_failure]
let test1_add_ref
  : compilable_closed #(bool -> (x:bool{x == true})) (fun x -> true)
  = CLambda CTrue

let test1_erase_ref
  : compilable_ref_closed #(x:bool{x == true} -> bool) (fun x -> x)
  = CRLambda (CRRefErase (fun x -> x == true) CRVar)
