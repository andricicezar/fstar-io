module PP

open FStar.Ghost
open FStar.Classical
open FStar.Tactics
module T = FStar.Tactics

(* Digression: I think potentially we may be able to write
a non-id function on this type.*)
let genat (b:erased bool) : Type =
  if b then erased nat else unit

(* It currently does not work since F* does not recognize
(if _ then noninf1 else noninf2) as non-informative... but
maybe for no good reason? *)
let succ (b:erased bool) (x : genat b) : genat b =
  let er : erased (genat b) =
    if reveal b
    then
      let n : nat = reveal x in
      hide (hide (n+1 <: nat))
    else
      ()
  in
  admit () // reveal er

(* /Digression *)

let gnat (b:erased bool) : Type =
  if b then nat else unit

(* Cannot write anything else without parametricity-breaking axioms *)
let f (b:erased bool) (x : gnat b) : gnat b = x

let cast (#a:Type) (x:a) (b:Type{a==b}) : b = x

let typ_f  = b:erased bool -> gnat b -> gnat b

let bool_p (s:bool) (x y : bool) : Type0 = squash (x == y)
let nat_p (s:bool) (x y : nat) : Type0 = squash (x == y)

let erased_p (s:bool) (a1 a2 : Type) (ar : a1 -> a2 -> Type) : erased a1 -> erased a2 -> Type =
  fun x1 x2 ->
    if s
    then squash (ar (reveal x1) (reveal x2))
    else squash True

let erased_p_refl (s:bool)
  (a:Type) (aR : a -> a -> Type)
  (x:erased a) (xR : aR (reveal x) (reveal x))
: erased_p s a a aR x x = ()

let gnat_p (s:bool) (b0 b1 : erased bool) (br : erased_p s bool bool (bool_p s) b0 b1) : gnat b0 -> gnat b1 -> Type0 = 
  fun g0 g1 ->
    match reveal b0, reveal b1 with
    | true,  true  -> nat_p s g0 g1
    | false, false -> squash True // trivial relation for unit-unit
    // If we have a gnat true related to a gnat false, we have
    // to be in the 'low' level.
    | _ -> squash (s == false)

let erased_nat_into_nat_t = erased nat -> nat

let erased_nat_into_nat_t_p (f1 f2 :erased nat -> nat) =
  s:bool ->
  x1:erased nat -> x2:erased nat -> xR:(erased_p s nat nat (nat_p s) x1 x2) ->
  nat_p s (f1 x1) (f2 x2)

(* erased nat -> nat must be constant *)
let lem (f : erased nat -> nat) (pf : erased_nat_into_nat_t_p f f) (x0 x1 : erased nat)
  : Lemma (f x0 == f x1) =
  let x : (erased_p false nat nat (nat_p false)) x0 x1 = () in
  let z : nat_p false (f x0) (f x1) = pf false x0 x1 x in
  let zz = Squash.return_squash z in
  assert (nat_p false (f x0) (f x1)); 
  assert (f x0 == f x1) by (compute()) // ouch

let gnat_p_refl (s:bool) (b : erased bool) (x : gnat b) : Lemma (gnat_p s b b (erased_p_refl s bool (bool_p s) b ()) x x) =
  if reveal b then
    let n : nat = x in
    assert (nat_p s n n) by (T.compute ())
  else
    assert_norm (gnat_p s b b (erased_p_refl s bool (bool_p s) b ()) x x) // reduces to True

let pair_p (a1 a2 : Type) (aR : a1 -> a2 -> Type)
   (b1 b2 : Type) (bR : b1 -> b2 -> Type) : (a1 & b1) -> (a2 & b2) -> Type
   =
   //fun (x1, y1) (x2, y2) -> squash (aR x1 x2 /\ bR y1 y2)
   fun p1 p2 -> squash (aR (fst p1) (fst p2) /\ bR (snd p1) (snd p2))

let f_with_secret_t = (nat & erased nat) -> (nat & erased nat)

let f_with_secret_t_p (s:bool) : f_with_secret_t -> f_with_secret_t -> Type =
  fun f0 f1 ->
    p0:(nat & erased nat) -> p1:(nat & erased nat) -> pR:(squash (pair_p nat nat (nat_p s) (erased nat) (erased nat) (erased_p s nat nat (nat_p s)) p0 p1)) ->
    pair_p nat nat (nat_p s) (erased nat) (erased nat) (erased_p s nat nat (nat_p s)) (f0 p0) (f1 p1)

(* The erased nat does not interfere into the pure nat. This is just a consequence
of appying the low principle. *)
let lem1_fst_preserved (f : f_with_secret_t) (pf : (s:bool) -> f_with_secret_t_p s f f)
  : Lemma (forall x y1 y2. fst (f (x, y1)) == fst (f (x, y2)))
  =
    let aux x y1 y2 : Lemma (fst (f (x, y1)) == fst (f (x, y2))) =
        let p0 = x,y1 in
        let p1 = x,y2 in
        assert (p0 == (x,y1));
        assert (p1 == (x,y2));
        assert (pair_p nat nat (nat_p false) (erased nat) (erased nat) (erased_p false nat nat (nat_p false)) p0 p1) by (compute ());
        let pR : squash (pair_p nat nat (nat_p false) (erased nat) (erased nat) (erased_p false nat nat (nat_p false)) p0 p1) = () in
        pf false (x,y1) (x,y2) pR;
        assert (pair_p nat nat (nat_p false) (erased nat) (erased nat) (erased_p false nat nat (nat_p false)) (f p0) (f p1));
        assert (pair_p nat nat (nat_p false) (erased nat) (erased nat) (erased_p false nat nat (nat_p false)) (f p0) (f p1) ==> fst (f p0) == fst (f p1)) by (compute ());
        ()
    in
    Classical.forall_intro_3 aux

(* TODO: a theorem that comes from using both principles, maybe this:

  f : a:Type -> (a & erased a) -> (a & erased a)

    the low principle gives non interference
    the high principle gives that snd (f (x, y)) has to be x or y

  so f (x, y) = (x, y)
   or f (x, x) = (x, x)
*)

let param_typ_f (s:bool) (f0 f1 : typ_f) =
  b0:erased bool ->
  b1:erased bool ->
  bR:(erased_p s bool bool (bool_p s) b0 b1) ->
  g0:gnat b0 ->
  g1:gnat b1 ->
  gR:(gnat_p s b0 b1 bR g0 g1) ->
  (gnat_p s b0 b1 bR (f0 b0 g0) (f1 b1 g1))

(* Cannot really prove this still *)
let erased_cannot_observe (f : typ_f) (pf : (s:bool) -> param_typ_f s f f) (b : erased bool) (x : gnat b)
  : Lemma (f b x == x)
  = 
  let r = f b x in
  if reveal b then begin
    let n : nat = x in
    let r : nat = f b x in
    pf false (hide true) (hide false) () x () ();
    admit ();
    //assert (reveal b == true);
    //pf b (hide true) () x x (gnat_p_refl _ x);
    //assert (gnat_p b b () x x);
    //admit();
    //assert (f b x == x);
    // both x and f b x are gnat true (= nat), but we cannot prove anything about them being equal
    ()
  end else
    ()


type tflag = | AllActions | SomeActions | NoActions

type action = | Read | History

let satisfies a fl =
  match fl with
  | AllActions -> True
  | SomeActions -> a == Read
  | NoActions -> False

type impl (fl : erased tflag) = a: action { a `satisfies` reveal fl }

let ctx_type =
  fl: erased tflag -> impl fl -> impl fl

let tflag_p (s : bool) (fl0 fl1 : tflag) = squash (fl0 == fl1)

let action_p (x y : action) = squash (x == y)

let impl_p (s : bool) fl0 fl1 (flR : erased_p s tflag tflag (tflag_p s) fl0 fl1) (i0 : impl fl0) (i1 : impl fl1) =
  action_p i0 i1 // Is it right? Should it depend on s?

let param_ctx_type (s : bool) (f0 f1 : ctx_type) =
  fl0: erased tflag -> fl1: erased tflag ->
  flR: erased_p s tflag tflag (tflag_p s) fl0 fl1 ->
  i0: impl fl0 -> i1: impl fl1 ->
  iR: impl_p s fl0 fl1 flR i0 i1 ->
  impl_p s fl0 fl1 flR (f0 fl0 i0) (f1 fl1 i1)

let ctx_ni (f : ctx_type) (fR : (s:bool) -> param_ctx_type s f f) fl0 fl1 (i0 : impl fl0) (i1: impl fl1) :
  Lemma (requires i0 == i1) (ensures f fl0 i0 == f fl1 i1)
= fR false fl0 fl1 () i0 i1 ()
