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
  [@@@no_method] t : (t:typ{elab_typ t == s})
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

instance elab_typ_is_compile_typ' (t:typ) : compile_typ (elab_typ t) = elab_typ_is_compile_typ t

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
let var_to_fs (g_card:nat) (x:var{x < g_card}) : (i:nat{i < g_card}) =
  g_card-x-1

let fs_to_var (g_card:nat) (i:nat{i < g_card}) : var =
  g_card-i-1

assume type fs_env #g (g_card:env_card g) : Type u#1000 (** having such an env is even possible in practice? what would its universe be? **)
assume val get_v : #g:_ -> #g_card:env_card g -> fs_env g_card -> i:nat{i < g_card} -> elab_typ (Some?.v (g (fs_to_var g_card i)))
assume val fs_extend : #g:_ -> #g_card:env_card g -> fs_s:fs_env g_card -> #t:typ -> elab_typ t -> fs_s':(fs_env #(extend t g) (g_card+1))
assume val fs_pop : #t:typ -> #g:_ -> #g_card:env_card g -> fs_env #(extend t g) (g_card+1) -> fs_env #g g_card

assume val lem_fs_extend #g (#g_card:env_card g) (fs_s:fs_env g_card) #t (v:elab_typ t) : Lemma (
  (forall (i:nat). i < g_card ==> get_v fs_s i == get_v (fs_extend fs_s v) i) /\
  get_v (fs_extend fs_s v) g_card == v)
  [SMTPat (fs_extend fs_s v)]

assume val lem_fs_pop #g (#g_card:env_card g) #t (fs_s:fs_env #(extend t g) (g_card+1)) : Lemma (
  (forall (i:nat). i < g_card ==> get_v fs_s i == get_v (fs_pop fs_s) i))
  [SMTPat (fs_pop fs_s)]

assume val pop_extend_inverse #g (#g_card:env_card g) (fs_s:fs_env g_card) #t (x:elab_typ t) : Lemma (fs_pop (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_pop (fs_extend fs_s x))]

let lem_inverse (g_card:nat) (x:var{x < g_card}) : Lemma (fs_to_var g_card (var_to_fs g_card x) == x) = ()
let lem_inverse' (g_card:nat) (i:var{i < g_card}) : Lemma (var_to_fs g_card (fs_to_var g_card i) == i) = ()

(** Asymmetric Cross Language Binary Logical Relation between F* and STLC expressions.
   It is assymetric because F* values are all closed, and only the e expressions are open. **)

let equiv_envs (#g:env) #b #g_card (s:gsub g g_card b) (fs_s:fs_env g_card) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (get_v fs_s (var_to_fs g_card x), (s x))

let equiv (#g:env) (g_card:env_card g) (t:typ) (fs_v:fs_env g_card -> elab_typ t) (e:exp) : Type0 =
  fv_in_env g e /\
  (forall b (s:gsub g g_card b) (fs_s:fs_env g_card).
    equiv_envs s fs_s ==>  t ⋮ (fs_v fs_s, (gsubst s e)))

let equiv_unit #g (g_card:env_card g) : Lemma ((fun _ -> ()) `equiv g_card TUnit` EUnit)  =
  ()

class compile_exp (#a:Type0) {| ca: compile_typ a |} (g:env) (g_card:env_card g) (fs_e:fs_env g_card -> a) = {
  [@@@no_method] t : (t:exp{fv_in_env g t});
  [@@@no_method] proof : typing g t ca.t;
  [@@@no_method] equiv_proof : unit -> Lemma (equiv g_card ca.t fs_e t);
}

instance compile_exp_unit g g_card : compile_exp #unit #solve g g_card (fun _ -> ()) = {
  t = EUnit;
  proof = TyUnit;
  equiv_proof = (fun () -> ());
}

let test_unit g n : compile_exp g n (fun _ -> ()) = solve

instance compile_exp_var g (g_card:env_card g) (i:nat{i < g_card}) :
  compile_exp g g_card (fun fs_s -> get_v fs_s i) =
  let x = fs_to_var g_card i in {
    t = EVar x;
    proof = begin
      assume ((elab_typ_is_compile_typ' (Some?.v (g x))).t == (Some?.v (g x)));
      TyVar #g x
    end;
    equiv_proof = (fun () -> ());
  }

instance compile_exp_var2 g (g_card:env_card g) t (i:nat{i < g_card}) :
  compile_exp
    (extend t g)
    (g_card+1)
    (fun fs_s -> get_v (fs_pop #t fs_s) i) =
  let x = fs_to_var (g_card+1) i in {
    t = EVar x;
    proof = begin
      assume ((elab_typ_is_compile_typ' (Some?.v ((extend t g) x))).t == (Some?.v ((extend t g) x)));
      TyVar #(extend t g) x
    end;
    equiv_proof = (fun () -> ());
  }

(*
instance compile_exp_var3 (#a:Type) {| ca: compile_typ a |} g (g_card:env_card g) (i:nat{i < g_card-2 /\ Some?.v (g (g_card-i-1)) == ca.t}) : compile_exp g g_card (fun fs_s -> get_v ((fs_pop (fs_pop fs_s))) i a) =
  let v = g_card-i-1 in {
    t = EVar v;
    proof = TyVar #g v;
    equiv_proof = (fun () -> admit ());
  }**)

let equiv_lam #g (g_card:env_card g) (t1:typ) (body:exp) (t2:typ) (f:fs_env g_card -> elab_typ (TArr t1 t2)) : Lemma
  (requires equiv #(extend t1 g) (g_card+1) t2 (fun fs_s -> f (fs_pop fs_s) (get_v fs_s g_card)) body)
            // the assymetry is here. body is an open expression, while for f, I don't have an open expression
            // the equiv is quantifying over the free variable of body, but not get_v
  (ensures equiv g_card (TArr t1 t2) f (ELam t1 body)) =
  let g' = extend t1 g in
  let g_card' : env_card g' = g_card + 1 in
  assume (fv_in_env g (ELam t1 body));
  introduce forall b (s:gsub g g_card b) fs_s. equiv_envs s fs_s ==> TArr t1 t2 ⋮ (f fs_s, gsubst s (ELam t1 body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam t1 body) == ELam t1 body');
      introduce forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>  t2 ⋮ (f fs_s fs_v, subst_beta t1 v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fs_s' = fs_extend fs_s fs_v in
          eliminate forall b (s':gsub g' g_card' b) fs_s'. equiv_envs s' fs_s' ==>  t2 ⋮ (f (fs_pop #t1 fs_s') (get_v fs_s' g_card), (gsubst s' body))
            with false s' fs_s';
          assert (equiv_envs s fs_s);
          assert (equiv_envs (gsub_extend s t1 v) (fs_extend fs_s fs_v));
          assert (t2 ⋮ (f (fs_pop fs_s') (get_v fs_s' g_card), (gsubst s' body)));
          assert (get_v (fs_extend fs_s fs_v) g_card == fs_v);
          assert (t2 ⋮ (f (fs_pop fs_s') fs_v, (gsubst s' body)));
          assert (t2 ⋮ (f fs_s fs_v, (gsubst s' body)));
          assume ((subst (sub_beta v) (subst (sub_elam s) body)) == (subst (gsub_extend s t1 v) body)); (** substitution lemma **)
          assert (t2 ⋮ (f fs_s fs_v, subst_beta t1 v body'))
        end
      end;
      assert (TArr t1 t2 ∋ (f fs_s, gsubst s (ELam t1 body)));
      assume (TArr t1 t2 ⋮ (f fs_s, gsubst s (ELam t1 body)))
    end
  end

instance compile_exp_lambda
  g
  (g_card:env_card g)
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:fs_env g_card -> a -> b)
  {| cf: (compile_exp #_ #cb (extend ca.t g) (g_card+1) (fun fs_s -> f (fs_pop fs_s) (get_v fs_s g_card))) |}
  : compile_exp #_ #solve g g_card (fun x -> f x) = {
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

class compile_whole (#a:Type0) {| ca: compile_typ a |} (s:a) = {
  t : compile_exp #a empty 0 (fun _ -> s)
}

let test1_exp : compile_whole #(unit -> unit) (fun x -> ()) = { t = solve }

let _ = assert (test1_exp.t.t == ELam TUnit (EUnit))

let test2_exp : compile_whole #(unit -> unit) (fun x -> x) = { t =
  compile_exp_lambda empty 0 (fun _ x -> x)
    #(compile_exp_var (extend TUnit empty) 1 0)
}
let _ = assert (test2_exp.t.t == ELam TUnit (EVar 0))

let test3_exp : compile_whole #(unit -> unit -> unit) (fun x y -> x) = { t =
  compile_exp_lambda empty 0 (fun _ x y -> x) (** CA: returning y instead of x does not return any error! **)
    #(compile_exp_lambda (extend TUnit empty) 1 (fun fs_s y -> get_v fs_s 0)
      #(compile_exp_var2 (extend TUnit empty) 1 TUnit 0))
}

let _ = assert (test3_exp.t.t == ELam TUnit (ELam TUnit (EVar 1)))

let test4_exp : compile_whole #(unit -> unit -> unit) (fun x y -> y) = { t =
  compile_exp_lambda empty 0 (fun _ x y -> y)
    #(compile_exp_lambda (extend TUnit empty) 1 (fun fs_s y -> y)
      #(compile_exp_var (extend TUnit (extend TUnit empty)) 2 1))
}
let _ = assert (test4_exp.t.t == ELam TUnit (ELam TUnit (EVar 0)))

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
  equiv_proof = (fun () -> admit ());
}

let test0_fapp : compile_whole #unit #solve ((fun x y -> y) () ()) = { t = solve }
let _ = assert (test0_fapp.t.t == EUnit)

(** How to deal with top level definitions? **)

val myf : unit -> unit
let myf () = ()

(* It seems that it just unfolds the definition of myf, which is pretty cool **)
let test1_topf : compile_whole (myf ()) = { t = solve }
// because of partial evaluation we have to consider both cases
let _ = assert (test1_topf.t.t == EApp (ELam TUnit EUnit) EUnit \/
                test1_topf.t.t == EUnit)

val myf2 : unit -> unit -> unit
let myf2 x y = x

(* Also handles partial application. Pretty amazing! *)
let test2_topf : compile_whole (myf2 ()) = { t = solve }
let _ = assert (test2_topf.t.t == EApp (ELam TUnit (ELam TUnit (EVar 1))) EUnit \/
                test2_topf.t.t == ELam TUnit EUnit)
