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
  (** CA: can this equality become problematic when
          `typ` will encode types that elaborate to
          refined types, arrows with pre-post conditions, and monadic arrows? **)
  (** CA: To get rid of the equality, one would have to find different
          definitions for `get_v'` and redefine the `equiv` relation. **)
}

instance compile_typ_unit : compile_typ unit = { t = TUnit }
instance compile_typ_bool : compile_typ bool = { t = TBool }
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
  | TBool -> compile_typ_bool
  | TArr t1 t2 ->
    assume (elab_typ t == (elab_typ t1 -> elab_typ t2)); (** I just proved this a few lines above **)
    compile_typ_arrow (elab_typ t1) (elab_typ t2) #(elab_typ_is_compile_typ t1) #(elab_typ_is_compile_typ t2)

instance elab_typ_is_compile_typ' (t:typ) : compile_typ (elab_typ t) = elab_typ_is_compile_typ t

let rec inverse_elab_typ_compile_typ (t:typ) : Lemma ((elab_typ_is_compile_typ t).t == t) [SMTPat (elab_typ_is_compile_typ t).t] =
  match t with
  | TUnit -> ()
  | TBool -> ()
  | TArr t1 t2 ->
    inverse_elab_typ_compile_typ t1;
    inverse_elab_typ_compile_typ t2;
    ()

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (bool -> unit) = solve
let _ = assert (test1.t == (TArr TBool TUnit))
let test2 : compile_typ ((unit -> bool) -> (bool -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TBool) (TArr TBool TUnit))


(** Compiling expressions **)
class compile_exp (#a:Type0) {| ca: compile_typ a |} (g:env) (fs_e:fs_env g -> a) = {
  [@@@no_method] e : (e:exp{fv_in_env g e}); (** expression is closed by g *)

  (** The following two lemmas are indepenent one of the other (we don't use one to prove the other). **)
  [@@@no_method] typing_proof : unit -> Lemma (sem_typing g e ca.t);
  [@@@no_method] equiv_proof : unit -> Lemma (fs_e `equiv ca.t` e);
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) {| ca: compile_typ a |} (s:a) = compile_exp #a empty (fun _ -> s)

let lemma_compile_closed_in_equiv_rel (#a:Type0) {| ca:compile_typ a |} (fs_e:a) {| cs:compile_closed #a #ca fs_e |}
  : Lemma (ca.t ⦂ (fs_e, cs.e) /\ cs.e ⋮ ca.t) =
  cs.equiv_proof ();
  equiv_closed_terms #ca.t fs_e cs.e;
  cs.typing_proof ();
  lem_sem_typing_closed cs.e ca.t

instance compile_exp_unit g : compile_exp #unit #solve g (fun _ -> ()) = {
  e = EUnit;
  typing_proof = (fun () -> typing_rule_unit g);
  equiv_proof = (fun () -> equiv_unit g);
}

instance compile_exp_true g : compile_exp #bool #solve g (fun _ -> true) = {
  e = ETrue;
  typing_proof = (fun () -> typing_rule_true g);
  equiv_proof = (fun () -> equiv_true g);
}

instance compile_exp_false g : compile_exp #bool #solve g (fun _ -> false) = {
  e = EFalse;
  typing_proof = (fun () -> typing_rule_false g);
  equiv_proof = (fun () -> equiv_false g);
}

let test_unit : compile_closed () = solve
let test_true : compile_closed true = solve
let test_false : compile_closed false = solve

(** get_v' works better with typeclass resolution than get_v **)
[@"opaque_to_smt"] (** not sure if the right pragma to prevent F* unfolding it during type class resolution **)
val get_v' : #g:env -> fs_env g -> x:var{Some? (g x)} -> a:Type{a == elab_typ (Some?.v (g x))} -> a
let get_v' #g fs_s i a =
  get_v #g fs_s i

instance compile_exp_var (a:Type) {| ca:compile_typ a |} (g:env) (x:var{Some? (g x) /\ ca.t == Some?.v (g x)})
  : compile_exp #a #ca g (fun fs_s -> get_v' fs_s x a) = {
    e = EVar x;
    typing_proof = (fun () ->
      inverse_elab_typ_compile_typ (Some?.v (g x));
      typing_rule_var g x
    );
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g);
      equiv_var g x);
}

let test1_var : compile_exp (extend TUnit empty) (fun fs_s -> get_v' fs_s 0 unit) = solve

instance compile_exp_var_shrink1 (** CA: how to make this general? **)
  (a:Type) {| ca:compile_typ a |}
  (g':env)
  (t:typ)
  (g:env{g' == extend t g})
  (x:var{Some? (g x) /\ ca.t == Some?.v (g x)})
  {| ce:compile_exp g' (fun fs_s -> get_v' #g' fs_s (x+1) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t #g fs_s) x a) = {
    e = ce.e;
    typing_proof = ce.typing_proof;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof ());
  }

instance compile_exp_var_shrink2 (** CA: how to make this general? **)
  (a:Type) {| ca:compile_typ a |}
  (g':env)
  (t1 t2:typ)
  (g:env{g' == extend t1 (extend t2 g)})
  (x:var{Some? (g x) /\ ca.t == Some?.v (g x)})
  {| ce:compile_exp g' (fun fs_s -> get_v' #g' fs_s (x+2) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t2 (fs_shrink #t1 fs_s)) x a) = {
    e = ce.e;
    typing_proof = ce.typing_proof;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof ());
  }

let test2_var : compile_exp (extend TUnit (extend TUnit empty)) (fun fs_s -> get_v' (fs_shrink fs_s) 0 unit) =
  solve

let test3_var : compile_exp (extend TUnit (extend TUnit (extend TUnit empty))) (fun fs_s -> get_v' (fs_shrink (fs_shrink fs_s)) 0 unit) =
  solve

instance compile_exp_lambda
  g
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:fs_env g -> a -> b)
  {| cf: compile_exp #b #cb (extend ca.t g) (fun fs_s -> f (fs_shrink #ca.t fs_s) (get_v' fs_s 0 a)) |}
  : compile_exp g f = {
  e = begin
    let g' = extend ca.t g in
    assert (fv_in_env (extend ca.t g) cf.e);
    assume (fv_in_env g (ELam cf.e));
    ELam cf.e
  end;
  typing_proof = (fun () ->
    cf.typing_proof ();
    typing_rule_lam g ca.t cf.e cb.t
  );
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    reveal_opaque (`%get_v') (get_v' #(extend ca.t g));
    equiv_lam g ca.t cf.e cb.t f
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
  solve
let _ = assert (test4_exp.e == ELam (ELam (ELam (EVar 2))))

let test4_exp' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> y) = solve
let _ = assert (test4_exp'.e == ELam (ELam (ELam (EVar 1))))

let test4_exp'' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> z) = solve
let _ = assert (test4_exp''.e == ELam (ELam (ELam (EVar 0))))


instance compile_exp_app
  g
  (#a:Type) {| ca: compile_typ a |}
  (#b:Type) {| cb: compile_typ b |}
  (f:fs_env g -> a -> b) {| cf: compile_exp #_ #solve g f |}
  (x:fs_env g -> a)     {| cx: compile_exp #_ #ca g x |}
  : compile_exp #_ #cb g (fun fs_s -> (f fs_s) (x fs_s)) = {
  e = begin
    assume (fv_in_env g (EApp cf.e cx.e));
    EApp cf.e cx.e
  end;
  typing_proof = (fun () ->
    cf.typing_proof ();
    cx.typing_proof ();
    typing_rule_app g cf.e cx.e ca.t cb.t
  );
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    cx.equiv_proof ();
    equiv_app g ca.t cb.t cf.e cx.e f x
  );
}

let test0_fapp : compile_closed #unit #solve ((fun x y -> y) () ()) = solve
let _ = assert (test0_fapp.e == EUnit)

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


instance compile_exp_if
  g
  (#a:Type) {| ca: compile_typ a |}
  (co:fs_env g -> bool)  {| cco: compile_exp #_ #solve g co |}
  (th:fs_env g -> a)     {| cth: compile_exp #_ #ca g th |}
  (el:fs_env g -> a)     {| cel: compile_exp #_ #ca g el |}
  : compile_exp #_ #ca g (fun fs_s -> if co fs_s then th fs_s else el fs_s) = {
  e = begin
    assume (fv_in_env g (EIf cco.e cth.e cel.e));
    EIf cco.e cth.e cel.e
  end;
  typing_proof = (fun () ->
    cco.typing_proof ();
    cth.typing_proof ();
    cel.typing_proof ();
    typing_rule_if g cco.e cth.e cel.e ca.t
  );
  equiv_proof = (fun () ->
    cco.equiv_proof ();
    cth.equiv_proof ();
    cel.equiv_proof ();
    equiv_if g ca.t cco.e cth.e cel.e co th el
  );
}

let test1_if : compile_closed #(bool -> bool) (fun x -> if x then false else true) = solve
let _ = assert (test1_if.e == ELam (EIf (EVar 0) EFalse ETrue))

let myt = true

let test2_if : compile_closed #bool (if myt then false else true) = solve
let _ = assert (test2_if.e == EIf ETrue EFalse ETrue)
