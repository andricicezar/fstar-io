module Compiler.V3.Correctness

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot
open STLC

let rec elab_typ (t:typ) : Type0 =
  match t with
  | TUnit -> unit
  | TArr t1 t2 -> (elab_typ t1 -> elab_typ t2)

class compile_typ (s:Type) = {
  [@@@no_method] t : (t:typ{elab_typ t == s}) // this could already create universe problems when using monads `Type u#a -> Type u#(max 1 a)`
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

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (unit -> unit) = solve
let _ = assert (test1.t == (TArr TUnit TUnit))
let test2 : compile_typ ((unit -> unit) -> (unit -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TUnit) (TArr TUnit TUnit))

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
        t2 ⋮ ((fs_f fs_v), (subst_beta t1 v e')))
    | _ -> False
  end
and (⋮) (t:typ) (p: elab_typ t * closed_exp) : Tot Type0 (decreases %[t;1]) =
  let fs_e = fst p in
  let e = snd p in
  forall (e':closed_exp). steps e e' ==> irred e' ==> t ∋ (fs_e, e)

assume val get_v : i:nat -> a:Type -> a
(** CA: this is an abstraction that helps with dealing with variables.
   It is like a symbol we introduce when dealing with lambdas and eliminate when dealing with variables **)

(** The deBrujin index is inverse to the index in F* env **)

let var_to_fs (g_card:nat) (x:var{x < g_card}) : (i:nat{i < g_card}) =
  g_card-x-1

let fs_to_var (g_card:nat) (i:nat{i < g_card}) : var =
  g_card-i-1

let lem_inverse (g_card:nat) (x:var{x < g_card}) : Lemma (fs_to_var g_card (var_to_fs g_card x) == x) = ()
let lem_inverse' (g_card:nat) (i:var{i < g_card}) : Lemma (var_to_fs g_card (fs_to_var g_card i) == i) = ()

type env_card (g:env) =
  g_card:nat{forall (i:nat). i < g_card ==> Some? (g i)}

let gsub (g:env) (g_card:env_card g) (b:bool{b ==> (forall x. None? (g x))}) =
  s:(sub b){
    forall (x:var). Some? (g x) ==>
      x < g_card /\
      is_value (s x)}

(** I suppose such a condition would be useless if one has a back-translation from STLC expressions to F* expression **)

let gsub_empty : gsub empty 0 true =
  (fun v -> EVar v)

let gsub_extend (#g:env) #b #g_card (s:gsub g g_card b) (t:typ) (v:value) : gsub (extend t g) (g_card+1) false =
  let f = fun (y:var) -> if y = 0 then v else s (y-1) in
  introduce exists (x:var). ~(EVar? (f x)) with 0 and ();
  f

let gsubst (#g:env) #b #g_card (s:gsub g b g_card) (e:exp{fv_in_env g e}) : closed_exp =
  lem_subst_freevars_closes_exp s e 0;
  subst s e

(** Asymmetric Cross Language Binary Logical Relation between F* and STLC expressions.
   It is assymetric because F* values are all closed, and only the e expressions are open. **)

let equiv (#g:env) (g_card:env_card g) (t:typ) (fs_v:elab_typ t) (e:exp) : Type0 =
  fv_in_env g e /\
  (forall b (s:gsub g g_card b).
    (forall (x:var). Some? (g x) ==> Some?.v (g x) ∋ (get_v (var_to_fs g_card x) (elab_typ (Some?.v (g x))), (s x))) ==>
    t ⋮ (fs_v, (gsubst s e)))

let equiv_unit #g (g_card:env_card g) : Lemma (() `equiv g_card TUnit` EUnit)  =
  ()

class compile_exp (#a:Type0) {| ca: compile_typ a |} (s:a) (g:env) (g_card:env_card g) = {
  [@@@no_method] t : (t:exp{fv_in_env g t});
  [@@@no_method] proof : typing g t ca.t;
  [@@@no_method] equiv_proof : unit -> Lemma (equiv g_card ca.t s t);
}

instance compile_exp_unit g g_card : compile_exp #unit #solve () g g_card = {
  t = EUnit;
  proof = TyUnit;
  equiv_proof = (fun () -> ());
}

let test_unit g n : compile_exp () g n = solve

instance compile_exp_var (#a:Type) {| ca: compile_typ a |} g (g_card:env_card g) (i:nat{i < g_card /\ Some?.v (g (g_card-i-1)) == ca.t}) : compile_exp (get_v i a) g g_card =
  let v = g_card-i-1 in {
    t = EVar v;
    proof = TyVar #g v;
    equiv_proof = (fun () -> assert (equiv g_card ca.t (get_v i a) (EVar v)));
  }

let equiv_lam #g (g_card:env_card g) (t1:typ) (body:exp) (t2:typ) (f:elab_typ (TArr t1 t2)) : Lemma
  (requires equiv #(extend t1 g) (g_card+1) t2 (f (get_v g_card (elab_typ t1))) body)
            // the assymetry is here. body is an open expression, while for f, I don't have an open expression
            // the equiv is quantifying over the free variable of body, but not get_v
  (ensures equiv g_card (TArr t1 t2) f (ELam t1 body)) =
  let g' = extend t1 g in
  let g_card' = g_card + 1 in
  assume (fv_in_env g (ELam t1 body));
  let fs_v' = get_v g_card (elab_typ t1) in
  introduce forall b (s:gsub g g_card b). (** ... ==> **) TArr t1 t2 ⋮ (f, gsubst s (ELam t1 body)) with begin
    let body' = subst (sub_elam s) body in
    assert (gsubst s (ELam t1 body) == ELam t1 body');
    introduce forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>  t2 ⋮ (f fs_v, subst_beta t1 v body') with begin
      introduce _ ==> _ with _. begin
        //assume (t1 ∋ (fs_v', v));
        eliminate forall b (s:gsub g' g_card' b).
          (forall (x:var). Some? (g' x) ==> Some?.v (g' x) ∋ (get_v (var_to_fs g_card' x) (elab_typ (Some?.v (g' x))), (s x))) ==>  t2 ⋮ (f fs_v', (gsubst s body))
        with false (gsub_extend s t1 v);
        // ^ here I want to instantiate with a F* env that contains fs_v'.

        admit ()
      end
    end;
    assert (TArr t1 t2 ∋ (f, gsubst s (ELam t1 body)));
    assume (TArr t1 t2 ⋮ (f, gsubst s (ELam t1 body)))
  end

(**  let g' = extend t1 g in
  assert (fv_in_env g' body);
  assume (fv_in_env g (ELam t1 body));
  introduce forall b (s:gsub g b). gsubst s (ELam t1 body) ⋮ TArr t1 t2 with begin
    let g' = extend t1 g in
    let body' = subst (sub_elam s) body in
    assert (gsubst s (ELam t1 body) == ELam t1 body');
    introduce forall (v:value). v ∈ t1 ==>  subst_beta t1 v body' ⋮ t2 with begin
      introduce _ ==> _ with _. begin
        assert (sem_typing g' body t2);
        eliminate forall b (s:gsub g' b). (gsubst s body) ⋮ t2 with false (gsub_extend s t1 v);
        assert (gsubst (gsub_extend s t1 v) body ⋮ t2);
        lem_substitution s t1 v body;
        assert (subst_beta t1 v body' ⋮ t2)
      end
    end;
    assert (gsubst s (ELam t1 body) ∈ TArr t1 t2);
    lem_value_is_typed_exp (gsubst s (ELam t1 body)) (TArr t1 t2)
  end
**)

instance compile_exp_lambda
  g
  (g_card:env_card g)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:a -> b) {| cf: (compile_exp #_ #cb (f (get_v g_card a)) (extend ca.t g) (g_card+1)) |}
  : compile_exp #_ #solve (fun x -> f x) g g_card = {
  t = begin
    let g' = extend ca.t g in
    assert (fv_in_env (extend ca.t g) cf.t);
    assume (fv_in_env g (ELam ca.t cf.t));
    ELam ca.t cf.t
  end;
  proof = TyLam #g ca.t cf.proof;
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    equiv_lam g_card ca.t cf.t cb.t f
  )
}

let test1_exp : compile_exp #(unit -> unit) (fun x -> ()) empty 0 =
  solve
let _ = assert (test1_exp.t == ELam TUnit (EUnit))

let test2_exp : compile_exp #(unit -> unit) (fun x -> x) empty 0 =
  solve
let _ = assert (test2_exp.t == ELam TUnit (EVar 0))

let test3_exp : compile_exp #(unit -> unit -> unit) (fun x y -> x) empty 0 =
  solve
let _ = assert (test3_exp.t == ELam TUnit (ELam TUnit (EVar 1)))

let test4_exp : compile_exp #(unit -> unit -> unit) (fun x y -> y) empty 0 =
  solve
let _ = assert (test4_exp.t == ELam TUnit (ELam TUnit (EVar 0)))

instance compile_exp_app
  g
  (g_card:env_card g)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:a -> b) {| cf: compile_exp #_ #solve f g g_card |}
  (x:a)     {| cx: compile_exp #_ #ca x g g_card |}
  : compile_exp #_ #cb (f x) g g_card = {
  t = EApp (cf.t) (cx.t);
  proof = TyApp #g cf.proof cx.proof;
}

let test0_fapp : compile_exp #unit #solve ((fun x y -> y) () ()) empty 0 =
  solve
let _ = assert (test0_fapp.t == EUnit)

(** How to deal with top level definitions? **)

val myf : unit -> unit
let myf () = ()

(* It seems that it just unfolds the definition of myf, which is pretty cool **)
let test1_topf : compile_exp (myf ()) empty 0 =
  solve
// because of partial evaluation we have to consider both cases
let _ = assert (test1_topf.t == EApp (ELam TUnit EUnit) EUnit \/
                test1_topf.t == EUnit)

val myf2 : unit -> unit -> unit
let myf2 x y = x

(* Also handles partial application. Pretty amazing! *)
let test2_topf : compile_exp (myf2 ()) empty 0 =
  solve
let _ = assert (test2_topf.t == EApp (ELam TUnit (ELam TUnit (EVar 1))) EUnit \/
                test2_topf.t == ELam TUnit EUnit)
