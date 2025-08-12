module EquivRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.List.Tot

open STLC
open SyntacticTypes

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
    | ELam e' ->
      (forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>
        t2 ⦂ (fs_f fs_v, subst_beta v e'))
    | _ -> False
  end
and (⦂) (t:typ) (p: elab_typ t * closed_exp) : Tot Type0 (decreases %[t;1]) =
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

let lem_gsubst_empty (e:closed_exp) : Lemma (gsubst gsub_empty e == e)
  [SMTPat (gsubst gsub_empty e)] =
  admit ()

(** F* Evaluation Environment : variable -> value **)

(** CA: this is an abstraction that helps with dealing with variables.
   It is like a symbol we introduce when dealing with lambdas and eliminate when dealing with variables **)

(** The deBrujin index is inverse to the index in F* env **)
let var_to_fs (g_card:nat) (x:var{x < g_card}) : (i:nat{i < g_card}) = g_card-x-1
let fs_to_var (g_card:nat) (i:nat{i < g_card}) : var = g_card-i-1
let lem_inverse (g_card:nat) (x:var{x < g_card}) : Lemma (fs_to_var g_card (var_to_fs g_card x) == x) = ()
let lem_inverse' (g_card:nat) (i:var{i < g_card}) : Lemma (var_to_fs g_card (fs_to_var g_card i) == i) = ()


val fs_env #g (g_card:env_card g) : Type u#0 (** having such an env is even possible in practice? what would its universe be? **)
val fs_empty : fs_env #empty 0
val get_v : #g:_ -> #g_card:env_card g -> fs_env g_card -> i:nat{i < g_card} -> elab_typ (Some?.v (g (fs_to_var g_card i)))
val fs_extend : #g:_ -> #g_card:env_card g -> fs_s:fs_env g_card -> #t:typ -> elab_typ t -> fs_s':(fs_env #(extend t g) (g_card+1))
val fs_shrink : #t:typ -> #g:_ -> #g_card:env_card g -> fs_env #(extend t g) (g_card+1) -> fs_env #g g_card

val lem_fs_extend #g (#g_card:env_card g) (fs_s:fs_env g_card) #t (v:elab_typ t) : Lemma (
  (forall (i:nat). i < g_card ==> get_v fs_s i == get_v (fs_extend fs_s v) i) /\
  get_v (fs_extend fs_s v) g_card == v)
  [SMTPat (fs_extend fs_s v)]

val lem_fs_shrink #g (#g_card:env_card g) #t (fs_s:fs_env #(extend t g) (g_card+1)) : Lemma (
  (forall (i:nat). i < g_card ==> get_v fs_s i == get_v (fs_shrink fs_s) i))
  [SMTPat (fs_shrink fs_s)]

val shrink_extend_inverse #g (#g_card:env_card g) (fs_s:fs_env g_card) #t (x:elab_typ t) : Lemma (fs_shrink (fs_extend fs_s x) == fs_s)
  [SMTPat (fs_shrink (fs_extend fs_s x))]

let (∽) (#g:env) #b #g_card (s:gsub g g_card b) (fs_s:fs_env g_card) : Type0 =
  forall (x:var). Some? (g x) ==>
    Some?.v (g x) ∋ (get_v fs_s (var_to_fs g_card x), s x)

(** Cross Language Binary Logical Relation between F* and STLC expressions
     for __open terms__. **)
let equiv (#g:env) (#g_card:env_card g) (t:typ) (fs_e:fs_env g_card -> elab_typ t) (e:exp) : Type0 =
  fv_in_env g e /\
  forall b (s:gsub g g_card b) (fs_s:fs_env g_card).
    s ∽ fs_s ==>  t ⦂ (fs_e fs_s, gsubst s e)

let (≈) (#g:env) (#g_card:env_card g) (#t:typ) (fs_v:fs_env g_card -> elab_typ t) (e:exp) : Type0 =
  equiv #g #g_card t fs_v e

(** Equiv closed terms **)
let equiv_closed_terms (#t:typ) (fs_e:elab_typ t) (e:closed_exp) :
  Lemma (requires equiv #empty #0 t (fun _ -> fs_e) e)
        (ensures  t ⦂ (fs_e, e)) =
  eliminate forall b (s:gsub empty 0 b) (fs_s:fs_env #empty 0).
    s ∽ fs_s ==>  t ⦂ ((fun _ -> fs_e) fs_s, gsubst s e) with true gsub_empty fs_empty

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
  (ensures f ≈ (ELam body)) =
  let g' = extend t1 g in
  let g_card' : env_card g' = g_card + 1 in
  assume (fv_in_env g (ELam body));
  introduce forall b (s:gsub g g_card b) fs_s. s ∽ fs_s ==> TArr t1 t2 ⦂ (f fs_s, gsubst s (ELam body)) with begin
    introduce _ ==> _ with _. begin
      let body' = subst (sub_elam s) body in
      assert (gsubst s (ELam body) == ELam body');
      introduce forall (v:value) (fs_v:elab_typ t1). t1 ∋ (fs_v, v) ==>  t2 ⦂ (f fs_s fs_v, subst_beta v body') with begin
        introduce _ ==> _ with _. begin
          let s' = gsub_extend s t1 v in
          let fs_s' = fs_extend fs_s fs_v in
          eliminate forall b (s':gsub g' g_card' b) fs_s'. s' ∽ fs_s' ==>  t2 ⦂ (f (fs_shrink #t1 fs_s') (get_v fs_s' g_card), (gsubst s' body))
            with false s' fs_s';
          assert (s ∽ fs_s);
          assert (gsub_extend s t1 v ∽ fs_extend fs_s fs_v);
          assert (t2 ⦂ (f (fs_shrink fs_s') (get_v fs_s' g_card), (gsubst s' body)));
          assert (get_v (fs_extend fs_s fs_v) g_card == fs_v);
          assert (t2 ⦂ (f (fs_shrink fs_s') fs_v, (gsubst s' body)));
          assert (t2 ⦂ (f fs_s fs_v, (gsubst s' body)));
          assume ((subst (sub_beta v) (subst (sub_elam s) body)) == (subst (gsub_extend s t1 v) body)); (** substitution lemma **)
          assert (t2 ⦂ (f fs_s fs_v, subst_beta v body'))
        end
      end;
      assert (TArr t1 t2 ∋ (f fs_s, gsubst s (ELam body)));
      assume (TArr t1 t2 ⦂ (f fs_s, gsubst s (ELam body))) (** lemma used by Amal **)
    end
  end

let equiv_app #g (g_card:env_card g) (t1:typ) (t2:typ) (e1:exp) (e2:exp) (fs_e1:fs_env g_card -> elab_typ (TArr t1 t2)) (fs_e2:fs_env g_card -> elab_typ t1) : Lemma
  (requires fs_e1 ≈ e1 /\ fs_e2 ≈ e2)
  (ensures (fun fs_s -> (fs_e1 fs_s) (fs_e2 fs_s)) ≈ (EApp e1 e2)) =
  assert (fv_in_env g e1);
  assert (fv_in_env g e2);
  assume (fv_in_env g (EApp e1 e2)); (** should be proveable **)
  introduce forall b (s:gsub g g_card b) fs_s. s ∽ fs_s ==> t2 ⦂ ((fs_e1 fs_s) (fs_e2 fs_s), gsubst s (EApp e1 e2)) with begin
    let fs_e1' = fs_e1 fs_s in
    let fs_e2' = fs_e2 fs_s in
    let fs_e = fs_e1' fs_e2' in
    introduce s ∽ fs_s ==>  t2 ⦂ (fs_e, gsubst s (EApp e1 e2)) with _. begin
      introduce forall (e':closed_exp). steps (gsubst s (EApp e1 e2)) e' /\ irred e' ==> t2 ∋ (fs_e, e') with begin
        introduce _ ==> t2 ∋ (fs_e, e') with h. begin
          let steps_e_e' : squash (steps (EApp (gsubst s e1) (gsubst s e2)) e') = () in
          FStar.Squash.map_squash #_ #(squash (t2 ∋ (fs_e, e'))) steps_e_e' (fun steps_e_e' ->
            let (e11, e2') = destruct_steps_eapp (gsubst s e1) (gsubst s e2) e' steps_e_e' in
            assert (TArr t1 t2 ∋ (fs_e1', ELam e11));
            assert (t1 ∋ (fs_e2', e2'));
            assert (t2 ⦂ (fs_e, subst_beta e2' e11));
            assert (t2 ∋ (fs_e, e'))
          )
        end
      end
    end
  end
