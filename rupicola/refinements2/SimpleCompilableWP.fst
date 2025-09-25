module SimpleCompilableWP

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
assume val fs_push : #g:env -> fsG:fs_env g -> #t:Type0 -> t -> fs_env (extend t g)
assume val fs_top : #g:env{Some? (g 0)} -> fs_env g -> Some?.v (g 0)
assume val fs_tail : #t:Type0 -> #g:env -> fs_env (extend t g) -> fs_env g

unfold let spec_env (g:env) (a:Type) =
  fsG:fs_env g -> pure_wp a

(** Definition of open FStar expressions **)
type fs_oexp (g:env) (a:Type) (wpG:spec_env g a) =
  fsG:fs_env g -> PURE a (wpG fsG)

unfold
val helper_var : g:env{Some? (g 0)} ->
                 a:Type{Some?.v (g 0) == a} ->
                 fs_oexp g a (fun fsG -> pure_return a (fs_top fsG))
let helper_var g a fsG = fs_top fsG

[@@no_auto_projectors] // FStarLang/FStar#3986
noeq
type compilable : #a:Type -> g:env -> wp:spec_env g a -> fs_oexp g a wp -> Type =
| CUnit       : #g:env ->
                compilable g
                  (fun _ -> pure_return unit ())
                  (fun _ -> ())

(** Can we generalize the following three rules? **)
| CVar0       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                compilable #a g
                  (fun fsG -> pure_return a (fs_top fsG))
                  (fun fsG -> fs_top fsG)

| CVar0'       : #g:env{Some? (g 0)} ->
                #a:Type{a == Some?.v (g 0)} ->
                compilable #a g
                  _
                  (helper_var g a)

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

let test_fapp2' ()
  : (compilable (extend (unit -> unit) empty) _ (fun fsG -> (fs_top fsG) ()))
  = CApp CVar0' CUnit

let test_fapp2 ()
  : (compilable (extend (unit -> unit) empty) _ (fun fsG -> (fs_top fsG) ()))
  = CApp CVar0 CUnit

let test_fapp2'' ()
  : Tot (compilable (extend (unit -> unit) empty) _ (fun fsG -> (fs_top fsG) ()))
  by (
    set_guard_policy Drop; dump "h0";
    split (); tadmit (); dump "h1";
    split (); tadmit (); dump "h2";
    let wpVar = forall_intro () in
    let wpVarH = implies_intro () in
    split (); bump_nth 2; tadmit ();
    dump "h3";
    let fsG = forall_intro () in
    let p = forall_intro () in
    let pH = implies_intro () in
    split ();
    trivial ();
    let g = forall_intro () in
    let gH = implies_intro () in

    let f = forall_intro () in
 //   binder_retype wpVarH; norm[delta_only[`%pure_return1;`%pure_return;`%Pervasives.pure_return;`%pure_return0]]; trefl ();
    //let _ = pose (`((`#wpVar) (`#fsG) (`#p))) in

    dump "H")
  = CApp #_ #_ #_ #_ #(fun fsG -> fs_top fsG) CVar0 CUnit

let test_fapp3 ()
  : Tot (compilable (extend (unit -> unit -> unit) empty) _ (fun fsG -> (fs_top fsG) () ()))
  = CApp (CApp CVar0 CUnit) CUnit
