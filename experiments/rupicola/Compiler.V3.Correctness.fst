module Compiler.V3.Correctness

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot
open STLC

let rec elab_typ (t:typ) : Type0 = // this could already create universe problems when using monads `Type u#a -> Type u#(max 1 a)`
  match t with
  | TUnit -> unit
  | TArr t1 t2 -> (elab_typ t1 -> elab_typ t2)

class compile_typ (s:Type) = {
  [@@@no_method] t : (t:typ{elab_typ t == s}) (** CA: is this equality problematic? **)
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
    assume (elab_typ t == (elab_typ t1 -> elab_typ t2));
    compile_typ_arrow (elab_typ t1) (elab_typ t2) #(elab_typ_is_compile_typ t1) #(elab_typ_is_compile_typ t2)

let rec inverse_elab_typ_compile_typ (t:typ) : Lemma ((elab_typ_is_compile_typ t).t == t) [SMTPat (elab_typ_is_compile_typ t).t] =
  match t with
  | TUnit -> ()
  | TArr t1 t2 ->
    inverse_elab_typ_compile_typ t1;
    inverse_elab_typ_compile_typ t2;
    ()

instance elab_typ_is_compile_typ' (t:typ) : compile_typ (elab_typ t) = elab_typ_is_compile_typ t

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (unit -> unit) = solve
let _ = assert (test1.t == (TArr TUnit TUnit))
let test2 : compile_typ ((unit -> unit) -> (unit -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TUnit) (TArr TUnit TUnit))

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __closed terms__. **)
let rec (∋) (t:typ) (p:elab_typ t * closed_exp) : Tot Type0 (decreases %[t;0]) =
  let fs_v = fst p in
  let e = snd p in
  match t with
  | TUnit -> fs_v == () /\ e == EUnit
  | TArr t1 t2 -> begin
    let fs_f : elab_typ t1 -> elab_typ t2 = fs_v in
    match e with
    | ELam t' e' -> t1 == t' /\
      (forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>
        t2 ⋮ (fs_f fs_v, subst_beta t1 v e'))
    | _ -> False
  end
and (⋮) (t:typ) (p: elab_typ t * closed_exp) : Tot Type0 (decreases %[t;1]) =
  let fs_e = fst p in
  let e = snd p in
  forall (e':closed_exp). steps e e' ==> irred e' ==> t ∋ (fs_e, e')

type env_card (g:env) =
  g_card:nat{forall (i:nat). i < g_card ==> Some? (g i)}

(** STLC Evaluation Environment : variable -> value **)

let gsub (g:env) (g_card:env_card g) (b:bool{b ==> (forall x. None? (g x))}) =
  s:(sub b){
    forall (x:var). Some? (g x) ==>  x < g_card /\ is_value (s x)}

let gsub_empty : gsub empty 0 true =
  (fun v -> EVar v)

let gsub_extend (#g:env) #b #g_card (s:gsub g g_card b) (t:typ) (v:value) : gsub (extend t g) (g_card+1) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsubst (#g:env) #b #g_card (s:gsub g b g_card) (e:exp{fv_in_env g e}) : closed_exp =
  lem_subst_freevars_closes_exp s e 0;
  subst s e

(** F* Evaluation Environment **)

(** CA: this is an abstraction that helps with dealing with variables.
   It is like a symbol we introduce when dealing with lambdas and eliminate when dealing with variables **)

(** The deBrujin index is inverse to the index in F* env **)
let var_to_fs (g_card:nat) (x:var{x < g_card}) : (i:nat{i < g_card}) = g_card-x-1
let fs_to_var (g_card:nat) (i:nat{i < g_card}) : var = g_card-i-1
let lem_inverse (g_card:nat) (x:var{x < g_card}) : Lemma (fs_to_var g_card (var_to_fs g_card x) == x) = ()
let lem_inverse' (g_card:nat) (i:var{i < g_card}) : Lemma (var_to_fs g_card (fs_to_var g_card i) == i) = ()

assume type fs_env #g (g_card:env_card g) : Type u#1000 (** having such an env is even possible in practice? what would its universe be? **)
assume val get_v : #g:_ -> #g_card:env_card g -> fs_env g_card -> i:nat{i < g_card} -> elab_typ (Some?.v (g (fs_to_var g_card i)))
assume val fs_extend : #g:_ -> #g_card:env_card g -> fs_s:fs_env g_card -> #t:typ -> elab_typ t -> fs_s':(fs_env #(extend t g) (g_card+1))
assume val fs_shrink : #t:typ -> #g:_ -> #g_card:env_card g -> fs_env #(extend t g) (g_card+1) -> fs_env #g g_card

assume val lem_fs_extend #g (#g_card:env_card g) (fs_s:fs_env g_card) #t (v:elab_typ t) : Lemma (
  (forall (i:nat). i < g_card ==> get_v fs_s i == get_v (fs_extend fs_s v) i) /\
  get_v (fs_extend fs_s v) g_card == v)
  [SMTPat (fs_extend fs_s v)]

assume val lem_fs_shrink #g (#g_card:env_card g) #t (fs_s:fs_env #(extend t g) (g_card+1)) : Lemma (
  (forall (i:nat). i < g_card ==> get_v fs_s i == get_v (fs_shrink fs_s) i))
  [SMTPat (fs_shrink fs_s)]

assume val pop_extend_inverse #g (#g_card:env_card g) (fs_s:fs_env g_card) #t (x:elab_typ t) : Lemma (fs_shrink (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_shrink (fs_extend fs_s x))]

let (∽) (#g:env) #b #g_card (s:gsub g g_card b) (fs_s:fs_env g_card) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (get_v fs_s (var_to_fs g_card x), s x)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:env) (#g_card:env_card g) (t:typ) (fs_e:fs_env g_card -> elab_typ t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g g_card b) (fs_s:fs_env g_card).
    s ∽ fs_s ==>  t ⋮ (fs_e fs_s, gsubst s e)

let (≈) (#g:env) (#g_card:env_card g) (#t:typ) (fs_v:fs_env g_card -> elab_typ t) (e:exp) : Type0 =
  equiv #g #g_card t fs_v e

(** Rules **)

let equiv_unit #g (g_card:env_card g)
  : Lemma ((fun (_:fs_env g_card) -> ()) `equiv TUnit` EUnit)
  = assert ((fun (_:fs_env g_card) -> ()) `equiv TUnit` EUnit) by (explode ())

let equiv_var #g (g_card:env_card g) (x:var{x < g_card})
  : Lemma ((fun (fs_s:fs_env g_card) -> get_v fs_s (var_to_fs g_card x)) ≈ EVar x)
  = assert ((fun (fs_s:fs_env g_card) -> get_v fs_s (var_to_fs g_card x)) ≈ EVar x) by (explode ())

let equiv_lam #g (g_card:env_card g) (t1:typ) (body:exp) (t2:typ) (f:fs_env g_card -> elab_typ (TArr t1 t2)) : Lemma
  (requires (fun (fs_s:fs_env #(extend t1 g) (g_card+1)) -> f (fs_shrink #t1 fs_s) (get_v fs_s g_card)) ≈ body)
            // the asymmetry is here. body is an open expression, while for f, I don't have an open expression
            // the equiv is quantifying over the free variable of body, but not get_v
  (ensures f ≈ (ELam t1 body)) =
  let g' = extend t1 g in
  let g_card' : env_card g' = g_card + 1 in
  assume (fv_in_env g (ELam t1 body));
  introduce forall b (s:gsub g g_card b) fs_s. s ∽ fs_s ==> TArr t1 t2 ⋮ (f fs_s, gsubst s (ELam t1 body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam t1 body) == ELam t1 body');
      introduce forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>  t2 ⋮ (f fs_s fs_v, subst_beta t1 v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fs_s' = fs_extend fs_s fs_v in
          eliminate forall b (s':gsub g' g_card' b) fs_s'. s' ∽ fs_s' ==>  t2 ⋮ (f (fs_shrink #t1 fs_s') (get_v fs_s' g_card), (gsubst s' body))
            with false s' fs_s';
          assert (s ∽ fs_s);
          assert (gsub_extend s t1 v ∽ fs_extend fs_s fs_v);
          assert (t2 ⋮ (f (fs_shrink fs_s') (get_v fs_s' g_card), (gsubst s' body)));
          assert (get_v (fs_extend fs_s fs_v) g_card == fs_v);
          assert (t2 ⋮ (f (fs_shrink fs_s') fs_v, (gsubst s' body)));
          assert (t2 ⋮ (f fs_s fs_v, (gsubst s' body)));
          assume ((subst (sub_beta v) (subst (sub_elam s) body)) == (subst (gsub_extend s t1 v) body)); (** substitution lemma **)
          assert (t2 ⋮ (f fs_s fs_v, subst_beta t1 v body'))
        end
      end;
      assert (TArr t1 t2 ∋ (f fs_s, gsubst s (ELam t1 body)));
      assume (TArr t1 t2 ⋮ (f fs_s, gsubst s (ELam t1 body))) (** lemma used by Amal **)
    end
  end

let equiv_app #g (g_card:env_card g) (t1:typ) (t2:typ) (e1:exp) (e2:exp) (fs_e1:fs_env g_card -> elab_typ (TArr t1 t2)) (fs_e2:fs_env g_card -> elab_typ t1) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures (fun fs_s -> (fs_e1 fs_s) (fs_e2 fs_s)) ≈ (EApp e1 e2)) =
  assert (fv_in_env g e1);
  assert (fv_in_env g e2);
  assume (fv_in_env g (EApp e1 e2)); (** should be proveable **)
  introduce forall b (s:gsub g g_card b) fs_s. s ∽ fs_s ==> t2 ⋮ ((fs_e1 fs_s) (fs_e2 fs_s), gsubst s (EApp e1 e2)) with begin
    let fs_e1' = fs_e1 fs_s in
    let fs_e2' = fs_e2 fs_s in
    let fs_e = fs_e1' fs_e2' in
    introduce s ∽ fs_s ==>  t2 ⋮ (fs_e, gsubst s (EApp e1 e2)) with _. begin
      introduce forall (e':closed_exp). steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps (EApp (gsubst s e1) (gsubst s e2)) e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp t1 (gsubst s e1) (gsubst s e2) e' steps_e_e' in
            assert (TArr t1 t2 ∋ (fs_e1', ELam t1 e11));
            assert (t1 ∋ (fs_e2', e2'));
            assert (t2 ⋮ (fs_e, subst_beta t1 e2' e11));
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end

(** Compiling expressions **)

class compile_exp (#a:Type0) {| ca: compile_typ a |} (g:env) (g_card:env_card g) (fs_e:fs_env g_card -> a) = {
  [@@@no_method] t : (t:exp{fv_in_env g t});
  [@@@no_method] proof : typing g t ca.t;
  [@@@no_method] equiv_proof : unit -> Lemma (fs_e `equiv ca.t` t);
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) {| ca: compile_typ a |} (s:a) = compile_exp #a empty 0 (fun _ -> s)

instance compile_exp_unit g g_card : compile_exp #unit #solve g g_card (fun _ -> ()) = {
  t = EUnit;
  proof = TyUnit;
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
    t = EVar x;
    proof = begin
      inverse_elab_typ_compile_typ (Some?.v (g x));
      TyVar #g x
    end;
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
    t = ce.t;
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
  t = begin
    let g' = extend ca.t g in
    assert (fv_in_env (extend ca.t g) cf.t);
    assume (fv_in_env g (ELam ca.t cf.t));
    ELam ca.t cf.t
  end;
  proof = TyLam #g ca.t cf.proof;
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    reveal_opaque (`%get_v') (get_v' #(extend ca.t g) #(g_card+1));
    equiv_lam g_card ca.t cf.t cb.t f
  )
}

let test1_exp : compile_closed (fun (x:unit) -> ()) = solve
let _ = assert (test1_exp.t == ELam TUnit (EUnit))

let test2_exp : compile_closed #(unit -> unit) (fun x -> x) = solve
let _ = assert (test2_exp.t == ELam TUnit (EVar 0))

let test3_exp : compile_closed #(unit -> unit -> unit) (fun x y -> x) = solve
let _ = assert (test3_exp.t == ELam TUnit (ELam TUnit (EVar 1)))

let test3_exp' : compile_closed #(unit -> unit -> unit) (fun x y -> y) = solve
let _ = assert (test3_exp'.t == ELam TUnit (ELam TUnit (EVar 0)))

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
  t = begin
    assume (fv_in_env g (EApp cf.t cx.t));
    EApp cf.t cx.t
  end;
  proof = TyApp #g cf.proof cx.proof;
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    cx.equiv_proof ();
    equiv_app g_card ca.t cb.t cf.t cx.t f x
  );
}

let test0_fapp : compile_closed #unit #solve ((fun x y -> y) () ()) = solve
let _ = assert (test0_fapp.t == EUnit)

(** How to deal with top level definitions? **)

val myf : unit -> unit
let myf () = ()

(* It seems that it just unfolds the definition of myf, which is pretty cool **)
let test1_topf : compile_closed (myf ()) = solve
// because of partial evaluation we have to consider both cases
let _ = assert (test1_topf.t == EApp (ELam TUnit EUnit) EUnit \/
                test1_topf.t == EUnit)

val myf2 : unit -> unit -> unit
let myf2 x y = x

(* Also handles partial application. Pretty amazing! *)
let test2_topf : compile_closed (myf2 ()) = solve
let _ = assert (test2_topf.t == EApp (ELam TUnit (ELam TUnit (EVar 1))) EUnit \/
                test2_topf.t == ELam TUnit EUnit)
