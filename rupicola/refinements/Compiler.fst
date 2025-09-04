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
  [@@@no_method] r : rtyp t s; // before we had: elab_typ t == s
}

instance compile_typ_unit : compile_typ unit = { t = TUnit; r = RUnit }
instance compile_typ_bool : compile_typ bool = { t = TBool; r = RBool }
  (**
instance compile_typ_arrow (s1:Type) (s2:Type) {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 -> s2) = {
  t = TArr c1.t c2.t;
  r = RArr c1.r c2.r }
**)
instance compile_typ_refinement (s1:Type) {| c1:compile_typ s1 |} (p:s1 -> Type0) :
  compile_typ (x:s1{p x}) = {
  t = c1.t;
  r = RRefined c1.r p;
  }

instance compile_typ_arrow_wp (s1:Type) (s2:Type) {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} (wp:s1 -> pure_wp s2) : compile_typ (x:s1 -> PURE s2 (wp x)) = {
  t = TArr c1.t c2.t;
  r = RArrWP c1.r c2.r wp }
(** This istance is redundant with compile_typ_arrow for F* **)

let pack #s (c:compile_typ s) : typsr = (| c.t, s, c.r |)

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.t == TUnit)
let test1 : compile_typ (bool -> unit) = solve
let _ = assert (test1.t == (TArr TBool TUnit))
let test2 : compile_typ ((unit -> bool) -> (bool -> unit)) = solve
let _ = assert (test2.t == TArr (TArr TUnit TBool) (TArr TBool TUnit))


type test3_t  = (x:bool -> PURE bool (FStar.Monotonic.Pure.as_pure_wp (fun p -> p x)))
let test3 : compile_typ test3_t = solve
let _ = assert (test3.t == (TArr TBool TBool))

(** Compiling expressions **)
class compile_exp (#a:Type0) {| ca: compile_typ a |} (g:env) (wp:wp_g g a) (fs_e:fs_oexp a wp) = {
  [@@@no_method] e : (e:exp{fv_in_env g e}); (** expression is closed by g *)

  (** The following two lemmas are indepenent one of the other (we don't use one to prove the other). **)
 // [@@@no_method] typing_proof : unit -> Lemma (sem_typing g e ca.t);
  [@@@no_method] equiv_proof : unit -> Lemma (fs_e `equiv (pack ca) wp` e);
}

(** Just a helper typeclass **)
unfold let compile_closed (#a:Type0) {| ca: compile_typ a |} (s:a) =
  compile_exp #a empty (fun _ -> pure_trivial a) (fun _ -> s)

let lemma_compile_closed_in_equiv_rel (#a:Type0) {| ca:compile_typ a |} (fs_e:a) {| cs:compile_closed #a #ca fs_e |}
  : Lemma (pack ca ⦂ (fs_e, cs.e)) =
  cs.equiv_proof ();
  equiv_closed_terms #(pack ca) fs_e cs.e

let lemma_compile_closed_arrow_is_elam #a #b {| ca:compile_typ a |} {| cb:compile_typ b |} (fs_e:a -> b) {| cs:compile_closed #(a -> b) fs_e |}
  : Lemma (ELam? cs.e) = admit ()

instance compile_exp_unit g (wp:wp_g g unit)
  (_:squash (forall fs_s p. wp fs_s p ==>  p ()))
  : compile_exp #unit #solve g wp (fun _ -> ()) = {
  e = EUnit;
  equiv_proof = (fun () -> admit ()); //equiv_unit g wp);
}

instance compile_exp_true g (wp:wp_g g bool)
  (_:squash (forall fs_s p. wp fs_s p ==>  p true))
  : compile_exp #bool #solve g wp (fun _ -> true) = {
  e = ETrue;
  equiv_proof = (fun () -> admit ()); // equiv_true g pre);
}

instance compile_exp_false g (wp:wp_g g bool)
  (_:squash (forall fs_s p. wp fs_s p ==>  p false))
  : compile_exp #bool #solve g wp (fun _ -> false) = {
  e = EFalse;
  equiv_proof = (fun () -> admit ()); // equiv_false g pre);
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
  (wp:wp_g g a)
  (x:var{Some? (g x) /\ pack ca == Some?.v (g x)})
  (_:squash (forall fs_s p. wp fs_s p ==>  p (get_v' fs_s x a)))
  : compile_exp #a #ca g wp (fun fs_s -> get_v' fs_s x a) = {
    e = EVar x;
    equiv_proof = (fun () -> admit ());

//      reveal_opaque (`%get_v') (get_v' #g);
//      equiv_var g x pre);
}

let test1_var : compile_exp (extend tunit empty) (fun _ -> pure_trivial unit) (fun fs_s -> get_v' fs_s 0 unit) = solve

instance compile_exp_var_shrink1 (** CA: how to make this general? **)
  (g':env)
  (a:Type) {| ca:compile_typ a |}
  (wp':wp_g g' a)
  (t:typsr)
  (g:env{g' == extend t g})
  (x:var{Some? (g x) /\ pack ca == Some?.v (g x)})
  (_:squash (forall fs_s p. wp' fs_s p ==>  p (get_v' #g (fs_shrink #t #g fs_s) x a)))
  (_:squash (forall fs_s p. wp' fs_s p ==>  p (get_v' #g' fs_s (x+1) a)))
  {| ce:compile_exp g' wp' (fun fs_s -> get_v' #g' fs_s (x+1) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' wp' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t #g fs_s) x a) = {
    e = ce.e;
    equiv_proof = (fun () -> admit ());
 //     reveal_opaque (`%get_v') (get_v' #g');
//      reveal_opaque (`%get_v') (get_v' #g);
//      ce.equiv_proof ());
  }

instance compile_exp_var_shrink2 (** CA: how to make this general? **)
  (g':env)
  (a:Type) {| ca:compile_typ a |}
  (wp':wp_g g' a)
  (t1 t2:typsr)
  (g:env{g' == extend t1 (extend t2 g)})
  (x:var{Some? (g x) /\ pack ca == Some?.v (g x)})
  (_:squash (forall fs_s p. wp' fs_s p ==>  p (get_v' #g (fs_shrink #t2 (fs_shrink #t1 fs_s)) x a)))
  (_:squash (forall fs_s p. wp' fs_s p ==>  p (get_v' #g' fs_s (x+2) a)))
  {| ce:compile_exp g' wp' (fun fs_s -> get_v' #g' fs_s (x+2) a) |} (** this is not necessary. I am hoping that it can be modified to be recursive **)
  : compile_exp g' wp' (fun (fs_s:fs_env g') -> get_v' #g (fs_shrink #t2 (fs_shrink #t1 fs_s)) x a) = {
    e = ce.e;
    equiv_proof = (fun () ->
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof ());
  }

let test2_var : compile_exp (extend tunit (extend tunit empty)) (fun _ -> pure_trivial unit) (fun fs_s -> get_v' (fs_shrink fs_s) 0 unit) =
  solve

let test3_var : compile_exp (extend tunit (extend tunit (extend tunit empty))) (fun _ -> pure_trivial unit) (fun fs_s -> get_v' (fs_shrink (fs_shrink fs_s)) 0 unit) =
  solve

(*** Compiling lambdas **)

let get_body_f #g a (#ca:compile_typ a) b (#cb:compile_typ b) wp (wpG:wp_g g (get_Type (mk_arrow_wp (pack ca) (pack cb) wp))) (f:fs_oexp (x:a -> PURE b (wp x)) wpG)
  : fs_oexp #(extend (pack ca) g) b (mk_pre_lam #g #(pack ca) #(pack cb) wp wpG) =
  fun fs_s ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    reveal_opaque (`%get_v') (get_v' #(extend (pack ca) g));
    f (fs_shrink #(pack ca) fs_s) (get_v' fs_s 0 a)

instance compile_exp_lambda_wp
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (wp:a -> pure_wp b)                    (** CA: the wp can depend on things that are in g, so maybe one can make this take a env of fs values? **)
  (wpG:wp_g g (get_Type (mk_arrow_wp (pack ca) (pack cb) wp)))
  (f:fs_oexp (x:a -> PURE b (wp x)) wpG)
  {| cf: compile_exp (extend (pack ca) g) (mk_pre_lam #g #(pack ca) #(pack cb) wp wpG) (get_body_f a b wp wpG f) |}
  : compile_exp #_ #(compile_typ_arrow_wp a b wp) g wpG f  = {
  e = begin
    lem_fv_in_env_lam g (pack ca) cf.e;
    ELam cf.e
  end;
  equiv_proof = (fun () -> admit ());
//    cf.equiv_proof ();
//    reveal_opaque (`%get_v') (get_v' #(extend (pack ca) g));
//    equiv_lam g pre (pack ca) (pack cb) wp cf.e f
//  )
}


let test1_exp : compile_closed (fun (x:unit) -> ()) = solve
let _ = assert (test1_exp.e == ELam (EUnit))

let test2_exp : compile_closed #(unit -> unit) (fun x -> x) = solve
let _ = assert (test2_exp.e == ELam (EVar 0))

let test3_exp : compile_closed #(unit -> unit -> unit) (fun x y -> x) = solve
let _ = assert (test3_exp.e == ELam (ELam (EVar 1)))

let test3_exp' : compile_closed #(unit -> unit -> unit) (fun x y -> y) = solve
let _ = assert (test3_exp'.e == ELam (ELam (EVar 0)))

let test4_exp : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> x) =
  solve
let _ = assert (test4_exp.e == ELam (ELam (ELam (EVar 2))))

let test4_exp' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> y) = solve
let _ = assert (test4_exp'.e == ELam (ELam (ELam (EVar 1))))

let test4_exp'' : compile_closed #(unit -> unit -> unit -> unit) (fun x y z -> z) = solve
let _ = assert (test4_exp''.e == ELam (ELam (ELam (EVar 0))))

let test1_pure : compile_closed #(x:bool -> Pure bool (x == true) (fun r -> r == true)) (fun x -> x) = solve
let _ = assert (test1_pure.e == ELam (EVar 0))

let test2_pure : compile_closed #(x:bool -> Pure bool (x == true) (fun r -> r == false)) (fun x -> false) = solve
let _ = assert (test2_pure.e == ELam EFalse)

let test3_pure : compile_closed #(x:bool -> Pure bool False (fun r -> r == false)) (fun x -> true) = solve
let _ = assert (test3_pure.e == ELam ETrue)

let helper_fapp2
  g
  (a:Type)
  (b:Type)
  (wpG:wp_g g b)
  (wp:a -> pure_wp b)
  (f:fs_oexp (x:a -> PURE b (wp x)) (fun fs_s p -> as_requires (wpG fs_s) /\ (forall r. p r)))
  (x:fs_oexp a (fun fs_s p -> as_requires (wpG fs_s) /\ (forall r. as_requires (wp r) ==> p r)))
  (l:squash (forall fs_s p. FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall (); (wpG fs_s p ==>  wp (x fs_s) p)))
  : fs_oexp b wpG =
  fun fs_s ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let f = helper_fapp (fun fs_s p -> as_requires (wpG fs_s) /\ (forall r. p r)) f fs_s in
    let x = helper_fapp (fun fs_s p -> as_requires (wpG fs_s) /\ (forall r. as_requires (wp r) ==> p r)) x fs_s in
    helper_fapp wp f x

instance compile_exp_app
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (wpG:wp_g g b)
  (wp:a -> pure_wp b)
  (f:fs_oexp (x:a -> PURE b (wp x)) (fun fs_s p -> as_requires (wpG fs_s) /\ (forall r. p r))) {| cf: compile_exp #_ #(compile_typ_arrow_wp a b wp) g _ f |}
  (x:fs_oexp a (fun fs_s p -> as_requires (wpG fs_s) /\ (forall r. as_requires (wp r) ==> p r))) {| cx: compile_exp g _ x |}
  (l:squash (forall fs_s p. FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall (); (wpG fs_s p ==>  wp (x fs_s) p)))
  : compile_exp #b #cb g wpG (helper_fapp2 g a b wpG wp f x l) = {
  e = begin
    lem_fv_in_env_app g cf.e cx.e;
    EApp cf.e cx.e
  end;
  equiv_proof = (fun () -> admit ());
(*    cf.equiv_proof ();
    cx.equiv_proof ();
    equiv_app g pre (pack ca) (pack cb) wp cf.e f cx.e x l
  );*)
}

// TODO: how to test functional application?

let myf : (x:bool -> Pure bool (x == true) (fun r -> r == false)) = fun x -> false

instance compile_exp_myf g pre : compile_exp g pre (fun _ -> myf) = solve

let test0_fapp : compile_closed #unit #solve ((fun x y -> y) () ()) = solve
let _ = assert (test0_fapp.e == EUnit)

val myf2 : unit -> unit -> unit
let myf2 x y = x

let test2_topf : compile_closed (myf2 ()) = solve
let _ = assert (test2_topf.e == ELam EUnit)

(**
let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  (fun f -> f false) =
  compile_exp_lambda_wp
    empty
    (fun _ -> True)
    _
    _
    (fun _ p -> forall r. p r)
    _
    #(compile_exp_app
      _
      _
      bool #solve
      bool #_
      (fun _ p -> forall r. p r)
      (fun fs_s -> get_v' fs_s 0 _) #solve
      (fun _ -> false) #solve
      ())
 **)

instance compile_exp_if
  g
  gpre
  (co:fs_oexp gpre bool)  {| cco: compile_exp g gpre co |}

  (#a:Type) {| ca: compile_typ a |}
  (th:fs_oexp gpre a)     {| cth: compile_exp #_ #ca g gpre th |}
  (el:fs_oexp gpre a)     {| cel: compile_exp #_ #ca g gpre el |}
  : compile_exp #_ #ca g gpre (fun fs_s -> if co fs_s then th fs_s else el fs_s) = {
  e = begin
    lem_fv_in_env_if g cco.e cth.e cel.e;
    EIf cco.e cth.e cel.e
  end;
  equiv_proof = (fun () -> admit ());
 (**   cco.equiv_proof ();
    cth.equiv_proof ();
    cel.equiv_proof ();
    equiv_if g (pack ca) cco.e cth.e cel.e co th el
  );**)
}


let test1_if : compile_closed #(bool -> bool -> bool) (fun x y -> if x then false else y) = solve
let _ = assert (test1_if.e == ELam (ELam (EIf (EVar 1) EFalse (EVar 0))))

let myt = true

let test2_if : compile_closed #bool (if myt then false else true) = solve
let _ = assert (test2_if.e == EIf ETrue EFalse ETrue)

(**
let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  #(compile_typ_arrow _ _ #(compile_typ_arrow _ _ #compile_typ_bool #compile_typ_bool))
  (fun f -> f false) =
  compile_exp_lambda _ _ _ _ #(compile_exp_app _ _ _ (fun fs_s -> get_v' fs_s 0 (bool -> bool)) _)**)

instance compile_exp_refinement
  g gpre
  (#a:Type) {| ca: compile_typ a |}
  (p:a -> Type0)
  (v:fs_oexp gpre (x:a{p x}))
  {| cv: compile_exp #a #ca g (fun fs_s -> gpre fs_s /\ p (v fs_s)) v |} (** CA: Insane! I was throwing the refinement. I have to push it inside **)
  : compile_exp #(x:a{p x}) #solve g gpre v = {
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

(**
val test3_ref : compile_closed (fun (x y:bool{False}) -> y)
let test3_ref = solve

let test3_ref' : compile_closed (fun (x y:bool{False}) -> x) =
  solve

 (**
let _ =
  assert (forall x y. (fun (x y:bool{False}) -> y) x y == (fun (x y:bool{False}) -> x) x y);
  assert ((fun (x y:bool{False}) -> y) == (fun (x y:bool{False}) -> x))
*)
let _ = assert (test3_ref.e == ELam (ELam (EVar 0)))

// Can we prove that ELam (ELam (EVar 1)) is also in relation with test3_ref? Probably yes..
// However, our compiler generates the correct syntax here.

(** The last two examples are equivalent because in the logical relation it quantifies over:
      (forall (v:value) (fs_v:s1). (| _, _, r1 |) ∋ (fs_v, v) ==>

   all F* values of the F* type.

   Which means that for test2 it quantifies over singleton true,
   and for test3 it quantifies over nothing.
**)

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


instance compile_exp_false_elim
  g pre
  (a:Type) {| ca: compile_typ a |}
  : compile_exp g pre (fun _ -> false_elim #a) = {
  e = ELam EUnit;
  equiv_proof = (fun () -> admit ()); (** this should be pretty easy to prove **)
}

(**
instance compile_exp_refinement_intro
  g pre
  (#a:Type) {| ca: compile_typ a |}
  (p:a -> Type0)
  (v:fs_oexp pre a)
  (l:(squash (forall fs_s. pre fs_s ==> p (v fs_s))))
  {| cv: compile_exp #a #ca g pre v |}
  : compile_exp #(x:a{p x}) #solve g pre (fun fs_s -> v fs_s) = {
  e = cv.e;
  equiv_proof = (fun () ->
    cv.equiv_proof ()
  );
}*)

let test_pm_false_elim0 : (x:unit -> Pure bool (requires False) (ensures fun _ -> True)) = (fun x -> false_elim ())
let test_pm_false_elim0' : compile_closed test_pm_false_elim0 =
 compile_exp_lambda_wp _ _ _ _ _ _
   #(compile_exp_app _ _ _ _ _ _ #(compile_exp_false_elim _ _ _) _ _)

(**
 compile_exp_lambda_wp empty
   (fun _ -> l_True)
   unit
   #compile_typ_unit
   bool
   #compile_typ_bool
   (fun _ p -> l_False /\ (forall (pure_result: bool). l_True ==> p pure_result))
   (fun _ -> test_pm_false_elim0)
   #(compile_exp_app
     (extend (pack #unit compile_typ_unit) empty)
     (mk_pre_lam #empty
         (fun _ -> l_True)
         #(pack #unit compile_typ_unit)
         #(pack #bool compile_typ_bool)
         (fun _ p -> l_False /\ (forall (pure_result: bool). l_True ==> p pure_result)))
     _
     _
     _
     _ #(compile_exp_false_elim _ _ _)
     (fun _ -> ()) #(compile_exp_refinement_intro _ _ _ _ ())
     ())
**)

let test_pm_false_elim1 : (x:unit{False} -> Tot bool) = (fun x -> false_elim ())
let test_pm_false_elim1' : compile_closed test_pm_false_elim1 =
 compile_exp_lambda_wp _ _ _ _ _ _
   #(compile_exp_app _ _ _ _ _ _ #(compile_exp_false_elim _ _ _) _ _)

(**
let test_pm_false_elim : (bool -> bool) = (fun x -> if x then if x then false else false_elim () else false)
let test_pm_false_elim' : compile_closed test_pm_false_elim = solve
**)

let test_ref_precond_f (x:bool{x == true}) : bool = false
let test_ref_precond : compile_closed #(bool -> bool) (fun x -> test_ref_precond_f (test_ref_assume x)) =
  solve
let _ = assert (test_ref_precond.e == ELam EFalse)

let test_ref_erasure (x:bool{x == true}) : bool = x

val test_ref_erasure' : compile_closed test_ref_erasure
[@expect_failure]
let test_ref_erasure' = solve (** this fails **)

instance compile_exp_refinement_elim
  g pre
  (a:Type) {| ca: compile_typ a |}
  (p:a -> Type0)
  (v:fs_oexp pre (x:a{p x}))
  {| cv: compile_exp #(x:a{p x}) #(compile_typ_refinement a #ca p) g pre v |}
  : compile_exp #a #ca g pre v = {
  e = cv.e;
  equiv_proof = (fun () ->
    cv.equiv_proof ()
  );
}

let test_ref_erasure' =
  compile_exp_lambda_wp _ _ _ _ _ _
    #(compile_exp_refinement_elim
      _ _ _
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
let _ = assert (test3_phase1.e == ELam EUnit)
