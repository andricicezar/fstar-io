module Compiler

open FStar.Tactics
open FStar.Tactics.Typeclasses
open FStar.Calc
open FStar.List.Tot

open STLC
open TypRel
open ExpRel

type fs_otyp (g:env) =
  fs_env g -> Type

class compile_otyp (g:env) (s:fs_otyp g) = {
  [@@@no_method] r : (fs_s:fs_env g -> rtyp (s fs_s));
}
unfold let compile_typ (s:Type) = compile_otyp empty (fun _ -> s)

let pack #g #ot (c:compile_otyp g ot) : otyp g = fun s -> (| ot s, c.r s |)

instance compile_typ_unit g : compile_otyp g (fun _ -> unit) = { r = fun _ -> RUnit }
instance compile_typ_bool g : compile_otyp g (fun _ -> bool) = { r = fun _ -> RBool }
instance compile_typ_arrow g (s1:fs_otyp g) (s2:fs_otyp g) {| c1:compile_otyp g s1 |} {| c2:compile_otyp g s2 |}
  : compile_otyp g (fun s -> (s1 s) -> (s2 s)) = { r = fun s -> RArr (c1.r s) (c2.r s) }

instance compile_typ_pair g (s1:fs_otyp g) (s2:fs_otyp g) {| c1:compile_otyp g s1 |} {| c2:compile_otyp g s2 |}
  : compile_otyp g (fun s -> (s1 s) & (s2 s)) = { r = fun s -> RPair (c1.r s) (c2.r s) }

// Some tests
let test0 : compile_typ (unit) = solve
let _ = assert (test0.r fs_empty == RUnit)
let test1 : compile_typ (bool -> unit) = solve
let _ = assert (test1.r fs_empty == (RArr RBool RUnit))

instance compile_typ_dpair g (s1:fs_otyp g) (s2:(s:fs_env g -> s1 s -> fs_otyp g)) {| c1:compile_otyp g s1 |} {| c2:(s:fs_env g -> x:s1 s -> compile_otyp g (s2 s x)) |}
  : compile_otyp g (fun s -> x:(s1 s) & (s2 s x s)) = {
    r = fun s -> RDPair (c1.r s) (fun x -> s2 s x s) (fun x -> (c2 s x).r s)
  }

instance compile_typ_dpair' g
  (s1:fs_otyp g) {| c1:compile_otyp g s1 |}
  (s2:(s:fs_env g -> fs_otyp (extend (pack c1 s) g))) {| c2:(s:fs_env g -> compile_otyp (extend (pack c1 s) g) (s2 s)) |}
  : compile_otyp g (fun s -> x:(s1 s) & (s2 s (fs_extend s x))) = {
    r = fun s -> RDPair (c1.r s) (fun x -> s2 s (fs_extend s x)) (fun x -> (c2 s).r (fs_extend s x))
  }

(** To extend g with s1, I need an evaluation environment????

I think we need a different notion of typing environment and evaluation environment to make this work.

val env
val extend : g:env -> (fs_otyp g) -> env


instance compile_typ_dpair''
  g
  (s1:fs_otyp g) {| c1:compile_otyp g s1 |}
  (s2:(fs_otyp (extend s g))) {| c2:compile_otyp (extend s g) s |}
  : compile_otyp g (fun s -> x:(s1 s) & (s2 (fs_extend s x))) = {
    r = fun s -> RDPair (c1.r s) (fun x -> s2 (fs_extend s x)) (fun x -> c2.r (fs_extend s x))
  }

type fs_oexp #g (a:fs_otyp g) =
  s:fs_env g -> a s

class compile_exp (#g:env) (a:fs_otyp g) {| ca: compile_otyp g a |} (fs_e:fs_oexp a) = {
  e : (e:exp{fv_in_env g e}); (** expression is closed by g *)
}

instance compile_exp_dpair
  g
  (a:fs_otyp g)                            {| ca: compile_otyp g a |}
  (b:fs_otyp (extend a g))                 {| c2: compile_otyp (extend a g) b |}
  (l:fs_oexp a)                            {| cl: compile_exp a #ca l |}
  (r:fs_oexp b)                            {| cr: compile_exp b #cb r |} (** this cannot be general because we only have `l fs` **)
  : compile_exp g (fun s -> (x:a s & b (extend s x))) (fun fs_s -> (| l s, r (extend s (l s)) |)) = {
  e = EPair cl.e cr.e
**)


let test_typ_dpair : compile_typ (b:bool & (if b then unit else bool)) =
  compile_typ_dpair
    empty
    (fun _ -> bool)
    (fun _ x _ -> if x then unit else bool)
    #solve
    #(fun _ x -> if x then compile_typ_unit empty else compile_typ_bool empty)

[@expect_failure] // TODO
let test_typ_dpair' : compile_typ (b:bool & (if b then unit else bool)) =
  compile_typ_dpair'
    empty
    (fun _ -> bool)
    (fun _ s -> if get_v s 0 then unit else bool)
    #solve
    #(fun _ -> ({ r = fun s -> if get_v s 0 then RUnit else RBool }))

let test2 : compile_typ ((unit -> bool) -> (bool -> unit)) = solve

let _ = assert (test2.r fs_empty == RArr (RArr RUnit RBool) (RArr RBool RUnit))

(** Compiling expressions **)
class compile_exp (g:env) (#a:fs_otyp g) {| ca: compile_otyp g a |} (fs_e:fs_oexp (pack ca)) = {
  [@@@no_method] e : (e:exp{fv_in_env g e}); (** expression is closed by g *)

  (** The following two lemmas are independent one of the other (we don't use one to prove the other). **)
 // [@@@no_method] typing_proof : unit -> Lemma (sem_typing g e ca.t);
  [@@@no_method] equiv_proof : unit -> Lemma (requires False) (ensures (fs_e `equiv (pack ca)` e));
}

instance compile_exp_dpair
  g
  (a:fs_otyp g)                           {| ca: compile_typ a |}
  (b:(s:fs_env g -> a s -> fs_otyp g))      {| c2:(s:fs_env g -> x:a s -> compile_otyp g (b s x)) |}
  (l:fs_env empty -> a)                    {| cl: compile_exp #_ #ca empty l |}
  (r:(fs:fs_env empty -> b (l fs)))        {| cr: compile_closed #_ #(cb (l fs)) (r fs) |} (** this cannot be general because we only have `l fs` **)
  : compile_exp #(x:a & b x) empty (fun fs_s -> (| l fs_s, r fs_s |)) = {
  e = begin
    EPair cl.e (cr fs_empty).e (** having the F* evaluation environment here, `fs`,
                                   is not possible because of the lambda instance where
                                   we would have to pass an extended environment to get the body,
                                   which we cannot do because we do not have any F* argument there **)
  end;
  equiv_proof = (fun () ->
    admit ()
  );
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

instance compile_exp_true g : compile_exp #bool #compile_typ_bool g (fun _ -> true) = {
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
[@"opaque_to_smt"] (** not sure if it is the right pragma to prevent F* unfolding get_v' during type class resolution **)
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

  (a:Type) {| ca: compile_typ a |}
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

(** TODO: why does this not work automatically **)
let test1_hoc : compile_closed
  #((bool -> bool) -> bool)
  #(compile_typ_arrow _ _ #(compile_typ_arrow _ _ #compile_typ_bool #compile_typ_bool))
  (fun f -> f false) =
  compile_exp_lambda _ _ _ _ #(compile_exp_app _ _ _ (fun fs_s -> get_v' fs_s 0 (bool -> bool)) _)

instance compile_exp_pair
  g
  (a:Type) {| ca: compile_typ a |}
  (b:Type) {| cb: compile_typ b |}
  (l:fs_env g -> a)     {| cl: compile_exp #_ #ca g l |}
  (r:fs_env g -> b)     {| cr: compile_exp #_ #cb g r |}
  : compile_exp #(a & b) g (fun fs_s -> (l fs_s, r fs_s)) = {
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

instance compile_exp_dpair_closed_l
  g
  (a:Type)                                {| ca: compile_typ a |}
  (b:a -> Type)                            {| cb: (x:a -> compile_typ (b x)) |}
  (l:a)                                   {| cl: compile_exp #_ #ca empty (fun _ -> l) |}
  (r:(fs:fs_env g -> b l))                 {| cr: compile_exp #_ #(cb l) g r |}
  : compile_exp #(x:a & b x) g (fun fs_s -> (| l, r fs_s |)) = {
  e = begin
    EPair cl.e cr.e
  end;
  equiv_proof = (fun () ->
    admit ()
  );
}

let function_or_n : (b:bool & (if b then unit else bool)) = (| false, true |)

val test_dp : compile_closed #_ #test_typ_dpair function_or_n
// TODO: why does this not work automatically
let test_dp =
  compile_exp_dpair_closed_l
    _
    _ #solve
    _ #_ // <-- having solve here fails
    _ #solve
    _ #solve

let _ = assert (test_dp.e == EPair EFalse ETrue)

instance compile_exp_dpair
  // g
  (a:Type)                                {| ca: compile_typ a |}
  (b:a -> Type)                            {| cb: (x:a -> compile_typ (b x) g) |}
  (l:fs_env empty -> a)                    {| cl: compile_exp #_ #ca empty l |}
  (r:(fs:fs_env empty -> b (l fs)))        {| cr: compile_closed #_ #(cb (l fs)) (r fs) |} (** this cannot be general because we only have `l fs` **)
  : compile_exp #(x:a & b x) empty (fun fs_s -> (| l fs_s, r fs_s |)) = {
  e = begin
    EPair cl.e (cr fs_empty).e (** having the F* evaluation environment here, `fs`,
                                   is not possible because of the lambda instance where
                                   we would have to pass an extended environment to get the body,
                                   which we cannot do because we do not have any F* argument there **)
  end;
  equiv_proof = (fun () ->
    admit ()
  );
}

val test_dp' : compile_closed #_ #test_typ_dpair function_or_n
let test_dp' =
  compile_exp_dpair
    // empty
    _ #_
    (fun x -> if x then unit else bool) #(fun x -> if x then compile_typ_unit else compile_typ_bool)
    _ #_
    _ #(fun fs -> compile_exp_true empty)

let _ = assert (test_dp.e == EPair EFalse ETrue)
