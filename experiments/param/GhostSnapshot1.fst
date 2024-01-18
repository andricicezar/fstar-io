module GhostRefParam2

// A (slightly) more realistic interface for erased, and proving the same result as in 
// GhostRefParam.

noeq
type erased_ix = {
  m : bool -> Type0 -> Type0;
  erased : Type0 -> Type0;

  hide : t:_ -> t -> erased t;
  reveal : t:_ -> erased t -> m true t;
  
  subt : t:_ -> m false t -> m true t;
  ret : a:_ -> a -> m false a;
  bind : a:_ -> b:_ -> f:bool -> m f a -> (a -> m f b) -> m f b;
  // TODO: add? this will invalidate related_any as it is now,
  // but it should be fixable
  run : a:_ -> m false a -> a;
}

open FStar.Classical
open FStar.Tactics
module T = FStar.Tactics
open Param

let int_param = param_of_eqtype int
let bool_param = param_of_eqtype bool

%splice[erased_ix_param; Mkerased_ix_param] (paramd (`%erased_ix))

%splice[__proj__Mkerased_ix__item__erased_param] (paramd (`%__proj__Mkerased_ix__item__erased))

// since an erased_ix provides no way to extract an erased or an m, they are
// all related to each other
// let related_any (ix1 ix2 : erased_ix) : erased_ix_param ix1 ix2 =
//   Mkerased_ix_param
//     ix1.m      ix2.m       (fun b1 b2 bR t1 t2 tR m1 m2 -> squash True)
//     ix1.erased ix2.erased  (fun t1 t2 tR e1 e2 -> squash True)
//     ix1.hide   ix2.hide    (fun t1 t2 tR x1 x2 xR -> ())
//     ix1.reveal ix2.reveal  (fun t1 t2 tR e1 e2 eR -> ())
//     ix1.subt   ix2.subt    (fun t1 t2 tR e1 e2 eR -> ())
//     ix1.ret    ix2.ret     (fun a1 a2 aR x1 x2 xR -> ())
//     ix1.bind   ix2.bind    (fun a1 a2 aR b1 b2 bR f1 f2 fR c1 c2 cR k1 k2 kR -> ())

let erased_ix_irrel : erased_ix = {
  m = (fun b t -> if b then unit else t);
  erased = (fun _ -> unit);
  hide = (fun _ _ -> ());
  reveal = (fun _ _ -> ());
  subt = (fun _ _ -> ());
  ret = (fun _ x -> x);
  bind = (fun a b f x k -> if f then () else k x);
  run = (fun a x -> x);
}

let unit_param = param_of_eqtype unit

let erased_ix_irrel_param : erased_ix_param erased_ix_irrel erased_ix_irrel =
  let ix1 = erased_ix_irrel in
  let ix2 = ix1 in
   Mkerased_ix_param
     ix1.m      ix2.m       (fun b1 b2 bR t1 t2 tR m1 m2 -> if not b1 then (tR m1 m2) else True)
     ix1.erased ix2.erased  (fun t1 t2 tR e1 e2 -> squash True)
     ix1.hide   ix2.hide    (fun t1 t2 tR x1 x2 xR -> ())
     ix1.reveal ix2.reveal  (fun t1 t2 tR e1 e2 eR -> ())
     ix1.subt   ix2.subt    (fun t1 t2 tR e1 e2 eR -> ())
     ix1.ret    ix2.ret     (fun a1 a2 aR x1 x2 xR -> xR)
     ix1.bind   ix2.bind    (fun a1 a2 aR b1 b2 bR f1 f2 fR c1 c2 cR k1 k2 kR ->
            assert (f1 == f2);
            if f1 then
              ()
            else
            kR c1 c2 cR
     )
     ix1.run    ix2.run     (fun a1 a2 aR c1 c2 cR -> 
       cR
     )

// The missing link: we want to use the ix.erased boolean in the type
// and match on it, how can we model that? This is one attempt.. maybe
// it can instead be inside of the erased_ix type, alongside a field
// stating that m f phi ==> phi, or something akin to that.
assume val reveal2 : (#ix:erased_ix) -> #b:Type0 -> ix.erased b -> GTot b
assume val reveal2_inv : (#ix:erased_ix) -> #b:Type0 -> e:(ix.erased b) -> v:b -> Lemma (requires e == ix.hide b v) (ensures reveal2 e == v)

let ty = (ix : erased_ix) -> (b : ix.erased bool) -> x:int -> y:int{if reveal2 b then y==x else True}

#set-options "--print_universes"

// FIXME: universes defaulting to zero
//%splice[ty_param] (paramd (`%ty))

// manually:
let ty_param (f0 f1 : ty) : Type u#1 =
    ix0: erased_ix ->
    ix1: erased_ix ->
    ixR: erased_ix_param ix0 ix1 ->
    b0: Mkerased_ix?.erased ix0 Prims.bool ->
    b1: Mkerased_ix?.erased ix1 Prims.bool ->
    bR: Mkerased_ix?.erased_param ix0 ix1 ixR bool bool bool_param b0 b1 ->
    x0: Prims.int -> x1: Prims.int -> xR: int_param x0 x1 ->
    int_param (f0 ix0 b0 x0) (f1 ix1 b1 x1)

let thm
  (f : ty)
  (f_param : ty_param f f)
  (ix : erased_ix)
  (ix_param : erased_ix_param ix ix)
: Lemma (forall b x. f ix b x == x)
=
  let aux (b : ix.erased bool) x : Lemma (f ix b x == x) =
    f_param ix ix ix_param
            
            b  (ix.hide _ true) ()
            x  x ();
    assert (f ix b x == f ix (ix.hide _ true) x);
    reveal2_inv (ix.hide _ true) true;
    ()
  in
  Classical.forall_intro_3 aux

// maybe easier, via the unit-based IX
let thm2
  (f : ty)
  (f_param : ty_param f f)
: Lemma (forall ix b x. f ix b x == x)
=
  let aux ix b x : Lemma (f ix b x == x) =
    f_param ix erased_ix_irrel (related_any _ _)
            b  ()               ()
            x  x                ();
    assert (f ix b x == f erased_ix_irrel () x);
    assert (f erased_ix_irrel () x == f erased_ix_irrel (erased_ix_irrel.hide bool true) x);
    reveal2_inv #erased_ix_irrel #bool () true;
    ()
  in
  Classical.forall_intro_3 aux
