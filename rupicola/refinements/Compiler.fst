module Compiler

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC
open SyntacticTypes
open EquivRel

class compile_typ (s:Type) = {
  [@@@no_method] t : typ;
  [@@@no_method] r : rtyp t s;
  (** CA: To get rid of the equality, one would have to find different
          definitions for `get_v'`. **)
}

instance compile_typ_unit : compile_typ unit = { t = TUnit; r = RUnit }
instance compile_typ_bool : compile_typ bool = { t = TBool; r = RBool }
instance compile_typ_arrow (s1:Type) (s2:Type) {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 -> s2) = {
  t = TArr c1.t c2.t;
  r = RArr c1.r c2.r }

instance compile_typ_refinement (s1:Type) {| c1:compile_typ s1 |} (p:s1 -> Type0) :
  compile_typ (x:s1{p x}) = {
  t = c1.t;
  r = RRefined c1.r p;
  }

let pack #s (c:compile_typ s) : typsr = (| c.t, s, c.r |)

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
 // [@@@no_method] typing_proof : unit -> Lemma (sem_typing g e ca.t);
  [@@@no_method] equiv_proof : unit -> Lemma (fs_e `equiv (pack ca)` e);
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) {| ca: compile_typ a |} (s:a) =
  compile_exp #a empty (fun _ -> s)

let lemma_compile_closed_in_equiv_rel (#a:Type0) {| ca:compile_typ a |} (fs_e:a) {| cs:compile_closed #a #ca fs_e |}
  : Lemma (pack ca ⦂ (fs_e, cs.e)) =
  cs.equiv_proof ();
  equiv_closed_terms #(pack ca) fs_e cs.e

let lemma_compile_closed_arrow_is_elam #a #b {| ca:compile_typ a |} {| cb:compile_typ b |} (fs_e:a -> b) {| cs:compile_closed #(a -> b) fs_e |}
  : Lemma (ELam? cs.e) = admit ()

instance compile_exp_unit g : compile_exp #unit #solve g (fun _ -> ()) = {
  e = EUnit;
  equiv_proof = (fun () -> equiv_unit g);
}

instance compile_exp_true g : compile_exp #bool #solve g (fun _ -> true) = {
  e = ETrue;
  equiv_proof = (fun () -> equiv_true g);
}

instance compile_exp_false g : compile_exp #bool #solve g (fun _ -> false) = {
  e = EFalse;
  equiv_proof = (fun () -> equiv_false g);
}

let test_unit : compile_closed () = solve
let test_true : compile_closed true = solve
let test_false : compile_closed false = solve

(** get_v' works better with typeclass resolution than get_v **)
[@"opaque_to_smt"] (** not sure if it is the right pragma to prevent F* unfolding get_v during type class resolution **)
val get_v' : #g:env -> fs_env g -> x:var{Some? (g x)} -> a:Type{a == get_Type (Some?.v (g x))} -> a
let get_v' #g fs_s i a =
  get_v #g fs_s i

instance compile_exp_var
  (g:env)
  (a:Type) {| ca:compile_typ a |}
  (x:var{Some? (g x) /\ pack ca == Some?.v (g x)})
  : compile_exp #a #ca g (fun fs_s -> get_v' fs_s x a) = {
    e = EVar x;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g);
      equiv_var g x);
}

let test1_var : compile_exp (extend tunit empty) (fun fs_s -> get_v' fs_s 0 unit) = solve

instance compile_exp_var_shrink1 (** CA: how to make this general? **)
  (g':env)
  (a:Type) {| ca:compile_typ a |}
  (t:typsr)
  (g:env{g' == extend t g})
  (x:var{Some? (g x) /\ pack ca == Some?.v (g x)})
  {| ce:compile_exp g' (fun fs_s -> get_v' #g' fs_s (x+1) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t #g fs_s) x a) = {
    e = ce.e;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof ());
  }

instance compile_exp_var_shrink2 (** CA: how to make this general? **)
  (g':env)
  (a:Type) {| ca:compile_typ a |}
  (t1 t2:typsr)
  (g:env{g' == extend t1 (extend t2 g)})
  (x:var{Some? (g x) /\ pack ca == Some?.v (g x)})
  {| ce:compile_exp g' (fun fs_s -> get_v' #g' fs_s (x+2) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t2 (fs_shrink #t1 fs_s)) x a) = {
    e = ce.e;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof ());
  }

let test2_var : compile_exp (extend tunit (extend tunit empty)) (fun fs_s -> get_v' (fs_shrink fs_s) 0 unit) =
  solve

let test3_var : compile_exp (extend tunit (extend tunit (extend tunit empty))) (fun fs_s -> get_v' (fs_shrink (fs_shrink fs_s)) 0 unit) =
  solve

instance compile_exp_lambda
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (f:fs_env g -> a -> b)
  {| cf: compile_exp #b #cb (extend (pack ca) g) (fun fs_s -> f (fs_shrink #(pack ca) fs_s) (get_v' fs_s 0 a)) |}
  : compile_exp g f = {
  e = begin
    lem_fv_in_env_lam g (pack ca) cf.e;
    ELam cf.e
  end;
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    reveal_opaque (`%get_v') (get_v' #(extend (pack ca) g));
    equiv_lam g (pack ca) cf.e (pack cb) f
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
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (f:fs_env g -> a -> b) {| cf: compile_exp #_ #solve g f |}
  (x:fs_env g -> a)     {| cx: compile_exp #_ #ca g x |}
  : compile_exp #_ #cb g (fun fs_s -> (f fs_s) (x fs_s)) = {
  e = begin
    lem_fv_in_env_app g cf.e cx.e;
    EApp cf.e cx.e
  end;
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    cx.equiv_proof ();
    equiv_app g (pack ca) (pack cb) cf.e cx.e f x
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
  (co:fs_env g -> bool)  {| cco: compile_exp #_ #solve g co |}

  (#a:Type) {| ca: compile_typ a |}
  (th:fs_env g -> a)     {| cth: compile_exp #_ #ca g th |}
  (el:fs_env g -> a)     {| cel: compile_exp #_ #ca g el |}
  : compile_exp #_ #ca g (fun fs_s -> if co fs_s then th fs_s else el fs_s) = {
  e = begin
    lem_fv_in_env_if g cco.e cth.e cel.e;
    EIf cco.e cth.e cel.e
  end;
  equiv_proof = (fun () ->
    cco.equiv_proof ();
    cth.equiv_proof ();
    cel.equiv_proof ();
    equiv_if g (pack ca) cco.e cth.e cel.e co th el
  );
}


let test1_if : compile_closed #(bool -> bool -> bool) (fun x y -> if x then false else y) = solve
let _ = assert (test1_if.e == ELam (ELam (EIf (EVar 1) EFalse (EVar 0))))

let myt = true

let test2_if : compile_closed #bool (if myt then false else true) = solve
let _ = assert (test2_if.e == EIf ETrue EFalse ETrue)

let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  #(compile_typ_arrow _ _ #(compile_typ_arrow _ _ #compile_typ_bool #compile_typ_bool))
  (fun f -> f false) =
  compile_exp_lambda _ _ _ _ #(compile_exp_app _ _ _ (fun fs_s -> get_v' fs_s 0 (bool -> bool)) _)

instance compile_exp_refinement
  g
  (#a:Type) {| ca: compile_typ a |}
  (p:a -> Type0)
  (v:fs_env g -> (x:a{p x}))
  {| cv: compile_exp #a #solve g v |}
  : compile_exp #(x:a{p x}) #solve g (fun fs_s -> v fs_s) = {
  e = cv.e;
  equiv_proof = (fun () ->
    cv.equiv_proof ()
  );
}


let refbool : (t:bool{t == true}) = true

let test1_ref : compile_closed refbool = solve
let _ = assert (test1_ref.e == ETrue)

let test2_ref : compile_closed (fun (x:bool{x == true}) -> x) =
  solve
let _ = assert (test2_ref.e == ELam (EVar 0))

let test3_ref : compile_closed (fun (x:bool{False}) -> x) =
  solve
let _ = assert (test3_ref.e == ELam (EVar 0))

(** The last two examples are equivalent because in the logical relation it quantifies over:
      (forall (v:value) (fs_v:s1). (| _, _, r1 |) ∋ (fs_v, v) ==>

   all F* values of the F* type.

   Which means that for test2 it quantifies over singleton true,
   and for test3 it quantifies over nothing.

   I suppose now there is the question: how do we fix the interface
   so that something this weird cannot happen?
**)


let test7_ref : compile_closed #(x:bool -> y:bool{y == false}) (fun x -> if x then false else false) =
  solve

(** *** Test partiality **)
let ttrue : (x:bool{x == true}) = true
let test_pm3 : compile_closed #bool ttrue = solve

let test_ref_assume (x:bool) : (y:bool{y == true}) = assume (x == true); x
let test_ref_assume' : compile_closed test_ref_assume = solve
let _ = assert (test_ref_assume'.e == ELam (EVar 0))

let test_pm2 : (x:bool -> y:bool{y == false}) = (fun x -> if x then if x then false else true else false)
let test_pm2' : compile_closed test_pm2 = solve
let _ = assert (test_pm2'.e == ELam (EIf (EVar 0) (EIf (EVar 0) EFalse ETrue) EFalse))
  (** why does this work? how did it type `true` to `y:bool{y == false}`?

      My intuition says that it should fail
      because the else branch, `fun _ -> true` has to be typed as `fs_env g -> y:bool{y == false}`,
      which should fail because it tries to do it without knowing that `x == false`, which would produce a
      contradiction with the initial refinement `x == true`.
  **)

let test_ref_precond_f (x:bool{x == true}) : bool = false
let test_ref_precond : compile_closed #(bool -> bool) (fun x -> test_ref_precond_f (test_ref_assume x)) =
  solve
let _ = assert (test_ref_precond.e == ELam EFalse) by (compute (); dump "H")

let test_ref_erasure (x:bool{x == true}) : bool = x

val test_ref_erasure' : compile_closed test_ref_erasure
[@expect_failure]
let test_ref_erasure' = solve (** this fails **)

instance compile_exp_erase_refinement
  g
  (a:Type) {| ca: compile_typ a |}
  (p:a -> Type0)
  (v:fs_env g -> (x:a{p x}))
  {| cv: compile_exp #(x:a{p x}) #(compile_typ_refinement a #ca p) g v |}
  : compile_exp #a #ca g (fun fs_s -> v fs_s) = {
  e = cv.e;
  equiv_proof = (fun () ->
    cv.equiv_proof ()
  );
}

let test_ref_erasure' =
  compile_exp_lambda _ _ _ _
    #(compile_exp_erase_refinement
      _ _
      (fun x -> x == true)
      (fun fs -> get_v' fs 0 (x:bool{x == true})))

let _ = assert (test_ref_erasure'.e == ELam (EVar 0))

let test_pm1 : (x:bool{x == true} -> bool) = (fun x -> if x then false else true)
[@expect_failure]
let test_pm1' : compile_closed test_pm1 = solve (** I suppose this would work if test_ref_erasure works **)



(**
instance compile_exp_subtype
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type{subtype_of a b}) {| cb: compile_typ b |}
  (v:fs_env g -> a)
  {| cv: compile_exp #a #ca g v |}
  : compile_exp #b #cb g (fun fs_s -> v fs_s) = {
  e = cv.e;
  equiv_proof = (fun () ->
    cv.equiv_proof ();
    admit () (** probabbly impossible to prove **)
  );
}

let test_ref_erasure'' : compile_closed test_ref_erasure =
  compile_exp_lambda
    empty
    (x:bool{x == true}) #solve
    bool #solve
    (fun _ x -> x)
    #(compile_exp_subtype
      _
      (x:bool{x == true}) #(compile_typ_refinement bool #compile_typ_bool (fun x -> x == true))
      bool #compile_typ_bool
      (fun fs -> get_v' fs 0 (x:bool{x == true}))
      #(compile_exp_var
        _
        (x:bool{x == true}) #_
        0))
**)


(** Test what phase 1 erases **)

let test1_phase1 : compile_closed #(bool -> unit) (fun x -> assert (x == x)) =
  solve
let _ = assert (test1_phase1.e == ELam EUnit)


let test2_phase1 : compile_closed #(bool -> unit) (fun x -> let y = FStar.Squash.get_proof (x == x) in ()) =
  solve
let _ = assert (test2_phase1.e == ELam EUnit)

let test3_lem () : Lemma (True) = ()
let test3_phase1 : compile_closed #(unit -> unit) (fun _ -> test3_lem ()) =
  solve

let test4_phase1 : compile_closed #(bool -> unit) (fun x -> let y = FStar.Squash.get_proof (x == x) in ()) =
  solve
let _ = assert (test4_phase1.e == ELam EUnit)
