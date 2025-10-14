module Compiler

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC
open TypRel
open ExpRel

class compile_typ (s:Type) = {
  [@@@no_method] r : rtyp s;
}

instance compile_typ_unit : compile_typ unit = { r = RUnit }
instance compile_typ_bool : compile_typ bool = { r = RBool }
instance compile_typ_arrow
  (s1:Type)
  (s2:Type)
  {| c1:compile_typ s1 |}
  {| c2:compile_typ s2 |} :
  compile_typ (s1 -> s2) = { r = RArr c1.r c2.r }
instance compile_typ_pair (s1:Type) (s2:Type) {| c1:compile_typ s1 |} {| c2:compile_typ s2 |} : compile_typ (s1 & s2) = { r = RPair c1.r c2.r }

let pack #s (c:compile_typ s) : typsr = (| s, c.r |)

// Some tests

let test0 : compile_typ (unit) = solve
let _ = assert (test0.r == RUnit)

let test1 : compile_typ (bool -> unit) = solve
let _ = assert (test1.r == (RArr RBool RUnit))

let test2 : compile_typ ((unit -> bool) -> (bool -> unit)) = solve
let _ = assert (test2.r == RArr (RArr RUnit RBool) (RArr RBool RUnit))

(** Compiling expressions **)
class compile_exp (#a:Type0) {| ca: compile_typ a |} (g:env) (fs_e:fs_env g -> a) = { (** using fs_oexp g (pack ca) complicates the instances of the type class **)
  [@@@no_method] e : (e:exp{fv_in_env g e}); (** expression is closed by g *)

  (** The following two lemmas are independent one of the other (we don't use one to prove the other). **)
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

(** fs_hd' works better with typeclass resolution than fs_hd **)
[@"opaque_to_smt"] (** not sure if it is the right pragma to prevent F* unfolding get_v' during type class resolution **)
val fs_hd' : #g:env -> #t:typsr -> fs_env (extend t g) -> a:Type{a == get_Type t} -> a
let fs_hd' #g fsG a =
  fs_hd #g fsG

instance compile_exp_var
  (g:env)
  (a:Type) {| ca:compile_typ a |}
  : compile_exp #a #ca (extend (pack ca) g) (fun fsG -> fs_hd' fsG a) = {
    e = EVar 0;
    equiv_proof = (fun () ->
      admit () (** this needs more refactoring **)
 //     reveal_opaque (`%fs_hd') (fs_hd' #g #(pack ca));
 //     equiv_var (extend (pack ca) g) 0);
   );
}

let test1_var : compile_exp (extend tunit empty) (fun fsG -> fs_hd' fsG unit) = solve

instance compile_exp_var_shrink1 (** CA: how to make this general? **)
  (g:env)
  (a:Type) {| ca:compile_typ a |}
  (t:typsr)
  : compile_exp (extend t (extend (pack ca) g)) (fun fsG -> fs_hd' (fs_tail fsG) a) = {
    e = EVar 1;
    equiv_proof = (fun () -> admit ()
    (**
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof () **)
    );
  }

instance compile_exp_var_shrink2 (** CA: how to make this general? **)
  (a:Type) {| ca:compile_typ a |}
  (t1 t2:typsr)
  (g:env)
  : compile_exp (extend t1 (extend t2 (extend (pack ca) g))) (fun fsG -> fs_hd' (fs_tail (fs_tail fsG)) a) = {
    e = EVar 2;
    equiv_proof = (fun () -> admit ()
      (** This needs more refactoring
      reveal_opaque (`%get_v') (get_v' #g');
      reveal_opaque (`%get_v') (get_v' #g);
      ce.equiv_proof ()); **))
  }

let test2_var : compile_exp (extend tunit (extend tunit empty)) (fun fsG -> fs_hd' (fs_tail fsG) unit) =
  solve

let test3_var : compile_exp (extend tunit (extend tunit (extend tunit empty))) (fun fsG -> fs_hd' (fs_tail (fs_tail fsG)) unit) =
  solve

instance compile_exp_lambda
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (f:fs_env g -> a -> b)
  {| cf: compile_exp #b #cb (extend (pack ca) g) (fun fsG -> f (fs_tail #(pack ca) fsG) (fs_hd' fsG a)) |}
  : compile_exp g f = {
  e = begin
    lem_fv_in_env_lam g (pack ca) cf.e;
    ELam cf.e
  end;
  equiv_proof = (fun () ->
    cf.equiv_proof ();
    reveal_opaque (`%fs_hd') (fs_hd' #g #(pack ca));
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
  : compile_exp #_ #cb g (fun fsG -> (f fsG) (x fsG)) = {
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

  (a:Type) {| ca: compile_typ a |}
  (th:fs_env g -> a)     {| cth: compile_exp #_ #ca g th |}
  (el:fs_env g -> a)     {| cel: compile_exp #_ #ca g el |}
  : compile_exp #_ #ca g (fun fsG -> if co fsG then th fsG else el fsG) = {
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

(** TODO: why does this not work automatically **)
let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  #(compile_typ_arrow _ _ #(compile_typ_arrow _ _ #compile_typ_bool #compile_typ_bool))
  (fun f -> f false) =
  compile_exp_lambda _ _ _ _ #(compile_exp_app _ _ _ (fun fsG -> fs_hd' fsG (bool -> bool)) _)

let _ = assert (test1_hoc.e == ELam (EApp (EVar 0) EFalse))

instance compile_exp_pair
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (l:fs_env g -> a)     {| cl: compile_exp #_ #ca g l |}
  (r:fs_env g -> b)     {| cr: compile_exp #_ #cb g r |}
  : compile_exp #(a & b) g (fun fsG -> (l fsG, r fsG)) = {
  e = begin
    lem_fv_in_env_pair g cl.e cr.e;
    EPair cl.e cr.e
  end;
  equiv_proof = (fun () ->
    cl.equiv_proof ();
    cr.equiv_proof ();
    equiv_pair g (pack ca) (pack cb) cl.e cr.e l r
  );
}

let test1_pair : compile_closed #(bool -> bool -> bool & bool) (fun x y-> (x,y)) = solve
let _ = assert (test1_pair.e == ELam (ELam (EPair (EVar 1) (EVar 0))))

let test2_pair : compile_closed #((bool -> bool) & (bool -> bool -> bool)) ((fun x -> x), (fun y x -> y)) = solve
let _ = assert (test2_pair.e == EPair (ELam (EVar 0)) (ELam (ELam (EVar 1))))

let test3_pair : compile_closed #((bool -> bool) & (bool -> bool)) ((fun x -> x), (fun x -> if x then false else true)) = solve

instance compile_exp_pair_fst
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  : compile_exp #(a & b -> a) #(compile_typ_arrow _ _ #(compile_typ_pair _ _ #ca #cb) #ca) g (fun _ -> fst #a #b) = {
  e = begin
    ELam (EFst (EVar 0))
  end;
  equiv_proof = (fun () ->
    equiv_pair_fst g (pack ca) (pack cb);
    assert (
      (mk_arrow (mk_pair (pack ca) (pack cb)) (pack ca)) ==
      (pack (compile_typ_arrow (a & b) a #(compile_typ_pair a b #ca #cb) #ca))) by (compute ())
  );
}

val test4_pair : compile_closed (fst (true, ()))
let test4_pair = solve

val test5_pair : compile_closed #((bool & bool) -> bool) (fun p -> fst p)
let test5_pair = solve

val test4_pair_fst' : compile_closed #(bool & unit -> bool) (fst #bool #unit)
let test4_pair_fst' = solve

val test4_pair' : compile_closed #bool (fst (true, ()))
let test4_pair' = solve

instance compile_exp_snd
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  : compile_exp #(a & b -> b) #(compile_typ_arrow _ _ #(compile_typ_pair _ _ #ca #cb) #cb) g (fun _ -> snd #a #b) = {
  e = begin
    ELam (ESnd (EVar 0))
  end;
  equiv_proof = (fun () ->
    equiv_pair_snd g (pack ca) (pack cb);
    assert (
      (mk_arrow (mk_pair (pack ca) (pack cb)) (pack cb)) ==
      (pack (compile_typ_arrow (a & b) b #(compile_typ_pair a b #ca #cb) #cb))) by (compute ())
  );
}

val test6_pair : compile_closed #unit (snd (true, ()))
let test6_pair = solve

val test7_pair : compile_closed #((bool & unit) -> unit) (fun p -> snd p)
let test7_pair = solve
