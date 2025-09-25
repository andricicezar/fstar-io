module SimpleCompilableWP2

open FStar.Tactics

(** Helpers to deal with Monotonicity of Pure **)
module M = FStar.Monotonic.Pure

unfold let (<=) #a (wp1 wp2:pure_wp a) = pure_stronger a wp1 wp2
unfold let ret #a x : pure_wp a =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  fun p -> p x

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
let helper_var0 g a fsG =
  fs_hd fsG


[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env ->
                compilable g
                  (fun _ -> ret ())
                  (fun _ -> ())

| CVar0       : #g:env ->
                #a:Type ->
                compilable #a _ _ (helper_var0 g a)

| CVar0'       : #g:env ->
                #a:Type ->
                compilable #a (extend a g) (fun fsG -> ret (fs_hd fsG)) (fun fsG -> fs_hd fsG)

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
                       ret (f' x'))))
                  (fun fsG -> M.elim_pure_wp_monotonicity_forall ();
                    (f fsG) (x fsG))

let test_app0 ()
  : Tot (compilable (extend (unit -> unit) empty) _ (fun fsG -> fs_hd fsG ()))
  by (dump "H")
  = CApp CVar0 CUnit

let test_app0' ()
  : Tot (compilable (extend (unit -> unit) empty) _ (fun fsG -> fs_hd fsG ()))
  by (dump "H") // this fails, has a different VC
  = CApp CVar0' CUnit
