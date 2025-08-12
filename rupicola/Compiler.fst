module Compiler

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC
open SyntacticTypes
open SemanticTyping
open EquivRel

class compile_typ (s:Type) = {
  [@@@no_method] t : (t:typ{elab_typ t == s})
  (** CA: is this equality problematic?
      CA: Explain why do we need it **)
}

instance compile_typ_unit : compile_typ unit = { t = TUnit }
instance compile_typ_arrow s1 s2 {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 -> s2) =
  { t = begin
    let t = (TArr c1.t c2.t) in
    assert (elab_typ t == (elab_typ c1.t -> elab_typ c2.t))
      by (norm [delta_only [`%elab_typ];zeta;iota]);
    assert (s1 == elab_typ c1.t);
    assert (s2 == elab_typ c2.t);
    assert ((s1 -> s2) == elab_typ t) by (
      rewrite (nth_binder (-1));
      rewrite (nth_binder (-3))
    );
    t
   end }

let rec elab_typ_is_compile_typ (t:typ) : compile_typ (elab_typ t) =
  match t with
  | TUnit -> compile_typ_unit
  | TArr t1 t2 ->
    assume (elab_typ t == (elab_typ t1 -> elab_typ t2)); (** I just proved this a few lines above **)
    compile_typ_arrow (elab_typ t1) (elab_typ t2) #(elab_typ_is_compile_typ t1) #(elab_typ_is_compile_typ t2)

instance elab_typ_is_compile_typ' (t:typ) : compile_typ (elab_typ t) = elab_typ_is_compile_typ t

let rec inverse_elab_typ_compile_typ (t:typ) : Lemma ((elab_typ_is_compile_typ t).t == t) [SMTPat (elab_typ_is_compile_typ t).t] =
  match t with
  | TUnit -> ()
  | TArr t1 t2 ->
    inverse_elab_typ_compile_typ t1;
    inverse_elab_typ_compile_typ t2;
    ()

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (unit -> unit) = solve
let _ = assert (test1.t == (TArr TUnit TUnit))
let test2 : compile_typ ((unit -> unit) -> (unit -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TUnit) (TArr TUnit TUnit))


(** Compiling expressions **)
class compile_exp (#a:Type0) {| ca: compile_typ a |} (g:env) (g_card:env_card g) (fs_e:fs_env g_card -> a) = {
  [@@@no_method] e : (e:exp{fv_in_env g e}); (** expression is closed by g *)
  [@@@no_method] proof : unit -> Lemma (sem_typing g e ca.t);
  [@@@no_method] equiv_proof : unit -> Lemma (fs_e `equiv ca.t` e);
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) {| ca: compile_typ a |} (s:a) = compile_exp #a empty 0 (fun _ -> s)

let lemma_compile_closed_in_equiv_rel (#a:Type0) {| ca:compile_typ a |} (fs_e:a) {| cs:compile_closed #a #ca fs_e |}
  : Lemma (ca.t ⦂ (fs_e, cs.e)) =
  cs.equiv_proof ();
  equiv_closed_terms #ca.t fs_e cs.e

instance compile_exp_unit g g_card : compile_exp #unit #solve g g_card (fun _ -> ()) = {
  e = EUnit;
  proof = (fun () -> typing_rule_unit g);
  equiv_proof = (fun () -> equiv_unit g_card);
}

let test_unit : compile_closed () = solve

(** get_v' works better with typeclass resolution than get_v **)
[@"opaque_to_smt"]
val get_v' : #g:_ -> #g_card:env_card g -> fs_env g_card -> i:nat{i < g_card} -> a:Type{a == elab_typ (Some?.v (g (fs_to_var g_card i)))} -> a
let get_v' #g #g_card fs_s i a =
  get_v #g #g_card fs_s i

instance compile_exp_var (a:Type) {| ca:compile_typ a |} (g:env) (g_card:env_card g) (i:nat{i < g_card /\ ca.t == Some?.v (g (fs_to_var g_card i))})
  : compile_exp #a #ca g g_card (fun fs_s -> get_v' fs_s i a) =
  let x = fs_to_var g_card i in {
    e = EVar x;
    proof = (fun () ->
      inverse_elab_typ_compile_typ (Some?.v (g x));
      typing_rule_var g x
    );
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g #g_card);
      equiv_var g_card x);
}

let test1_var : compile_exp (extend TUnit empty) 1 (fun fs_s -> get_v' fs_s 0 unit) = solve

instance compile_exp_var_shrink1 (** CA: how to make this general? **)
  (a:Type) {| ca:compile_typ a |}
  (g':env)
  (g_card':env_card g')
  (t:typ)
  (g:env{g' == extend t g})
  (g_card:(env_card g){g_card == g_card' - 1})
  (i:nat{i < g_card /\ ca.t == Some?.v (g' (fs_to_var g_card' i))})
  {| ce:compile_exp g' g_card' (fun fs_s -> get_v' #g' #g_card' fs_s i a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' g_card' (fun fs_s -> get_v' #g #g_card (fs_shrink #t #g #g_card fs_s) i a) = {
    e = ce.e;
    proof = ce.proof;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g' #g_card');
      reveal_opaque (`%get_v') (get_v' #g #g_card);
      ce.equiv_proof ());
  }

let test2_var : compile_exp (extend TUnit (extend TUnit empty)) 2 (fun fs_s -> get_v' (fs_shrink #TUnit #_ #1 fs_s) 0 unit) = solve

(** TODO: **)
let test3_var : compile_exp (extend TUnit (extend TUnit (extend TUnit empty))) 3 (fun fs_s -> get_v' (fs_shrink #TUnit #_ #1 (fs_shrink #TUnit #_ #2 fs_s)) 0 unit) =
  admit ()
//  solve

instance compile_exp_lambda
  g
  (g_card:env_card g)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:fs_env g_card -> a -> b)
  {| cf: compile_exp #b #cb (extend ca.t g) (g_card+1) (fun fs_s -> f (fs_shrink #ca.t fs_s) (get_v' fs_s g_card a)) |}
  : compile_exp #_ #(compile_typ_arrow a b) g g_card (fun (fs_s:fs_env g_card) -> f fs_s) = {
  e = begin
    let g' = extend ca.t g in
    assert (fv_in_env (extend ca.t g) cf.e);
    assume (fv_in_env g (ELam cf.e));
    ELam cf.e
  end;
  proof = (fun () ->
    cf.proof ();
    typing_rule_lam g ca.t cf.e cb.t
  );
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    reveal_opaque (`%get_v') (get_v' #(extend ca.t g) #(g_card+1));
    equiv_lam g_card ca.t cf.e cb.t f
  )
}

let test1_exp : compile_closed (fun (x:unit) -> ()) = solve
let _ = assert (test1_exp.e == ELam (EUnit))

let test2_exp : compile_closed #(unit -> unit) (fun x -> x) = solve
let _ = assert (test2_exp.e == ELam (EVar 0))

let test3_exp : compile_closed #(unit -> unit -> unit) (fun x y -> x) = solve
let _ = assert (test3_exp.e == ELam (ELam (EVar 1)))

let test3_exp' : compile_closed #(unit -> unit -> unit) (fun x y -> y) = solve
let _ = assert (test3_exp'.e == ELam (ELam (EVar 0)))

(** TODO: **)
let test4_exp : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> x) =
  admit ()
//  solve

let test4_exp' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> y) = solve

let test4_exp'' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> z) = solve


instance compile_exp_app
  g
  (g_card:env_card g)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:fs_env g_card -> a -> b) {| cf: compile_exp #_ #solve g g_card f |}
  (x:fs_env g_card -> a)     {| cx: compile_exp #_ #ca g g_card x |}
  : compile_exp #_ #cb g g_card (fun fs_s -> (f fs_s) (x fs_s)) = {
  e = begin
    assume (fv_in_env g (EApp cf.e cx.e));
    EApp cf.e cx.e
  end;
  proof = (fun () ->
    cf.proof ();
    cx.proof ();
    typing_rule_app g cf.e cx.e ca.t cb.t
  );
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    cx.equiv_proof ();
    equiv_app g_card ca.t cb.t cf.e cx.e f x
  );
}

let test0_fapp : compile_closed #unit #solve ((fun x y -> y) () ()) = solve
let _ = assert (test0_fapp.e == EUnit)

(** How to deal with top level definitions? **)

val myf : unit -> unit
let myf () = ()

(* It seems that it just unfolds the definition of myf, which is pretty cool **)
let test1_topf : compile_closed (myf ()) = solve
// because of partial evaluation we have to consider both cases
let _ = assert (test1_topf.e == EApp (ELam EUnit) EUnit \/
                test1_topf.e == EUnit)

val myf2 : unit -> unit -> unit
let myf2 x y = x

(* Also handles partial application. Pretty amazing! *)
let test2_topf : compile_closed (myf2 ()) = solve
let _ = assert (test2_topf.e == EApp (ELam (ELam (EVar 1))) EUnit \/
                test2_topf.e == ELam EUnit)
