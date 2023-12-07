module StRel

open FStar.Tactics
open FStar.Classical.Sugar
open FStar.Calc

(** *** computational state monad **)
type state = bool -> int (** high and low locations **)

type st (a:Type) = state -> a * state
let ret_st (x:'a) : st 'a = fun s -> (x,s)
let bind_st (m:st 'a) (f:'a -> st 'b) : st 'b = fun s -> let (x,s') = m s in f x s'
let st_get l : st int = fun s -> (s l, s)
let st_upd (s:state) l v : state = (fun l' -> if l = l' then v else s l')
let st_put l v : st unit = fun s -> ((), st_upd s l v)

let st_monad_law1 #a (m:st a) : Lemma (forall s. bind_st m ret_st s == m s) = ()
let st_monad_law2 #a #b (f:a -> st b) (x:a) : Lemma (forall s. bind_st (ret_st x) f s == f x s) = ()
let st_monad_law3 (#a #b #c:Type) (m:st a) (f:a -> st b) (g:b -> st c) : Lemma (
  forall s. bind_st (bind_st m f) g s == bind_st m (fun r -> bind_st (f r) g) s
) = ()

(** *** specification state monad **)
type wst0 (a:Type) = (a * state -> Type0) -> (state -> Type0)
unfold let wst_monotonic (wp:wst0 'a) = (forall p1 p2. (forall r. p1 r ==> p2 r) ==> (forall s0. wp p1 s0 ==> wp p2 s0))
type wst (a:Type) = wp:(wst0 a){wst_monotonic wp}
unfold let ret_wst (x:'a) : wst 'a = fun p s0 -> p (x,s0)
unfold let bind_wst (m:wst 'a) (f:'a -> wst 'b) : wst 'b = fun p s0 -> m (fun (x,s1) -> f x p s1) s0

let get_wst l : wst int = 
  fun p s0 -> p (s0 l, s0)

let put_wst l v : wst unit =
  fun p s0 -> p ((), st_upd s0 l v)

let wst_leq (wp1:wst 'a) (wp2:wst 'a) : Type0 =
  forall p s0. wp2 p s0 ==> wp1 p s0

unfold
let wst_if_then_else (wp1 wp2:wst 'a) (b:bool) : wst 'a =
  fun p s0 -> (b ==> wp1 p s0) /\ ((~b) ==> wp2 p s0)

val theta_st : st 'a -> wst 'a
let theta_st m = fun p s0 -> p (m s0)

let lemma_theta_morphism (m:st 'a) (f:'a -> st 'b) : Lemma (
  forall s0 p. theta_st (bind_st m f) p s0 <==> bind_wst (theta_st m) (fun x -> theta_st (f x)) p s0
) = ()

(** ** Relational Specification State Monad **)
let wstrel_post a = a * state -> a * state -> Type0
let wstrel_pre = state -> state -> Type0
type wstrel0 a = wstrel_post a -> wstrel_pre

unfold let wstrel_monotonic (wp:wstrel0 'a) =
  forall (p1 p2:wstrel_post 'a). (forall r1 r2. p1 r1 r2 ==> p2 r1 r2) ==> (forall s0 s1. wp p1 s0 s1 ==> wp p2 s0 s1)
type wstrel a = wp:(wstrel0 a){wstrel_monotonic wp}

(** *** Relative monad **)
unfold let bret_wstrel (x:'a) (y:'a) : wstrel 'a = fun p s0 s1 -> p (x,s0) (y,s1) 
unfold let bbind_wstrel (wm:wstrel 'a) (wf:'a -> 'a -> wstrel 'b) : wstrel 'b =
  fun p -> wm (fun (x0,s0') (x1,s1') -> wf x0 x1 p s0' s1')

val btheta_wstrel : st 'a -> st 'a -> wstrel 'a
let btheta_wstrel m1 m2 = fun p s1 s2 -> p (m1 s1) (m2 s2)
let theta_wstrel m = btheta_wstrel m m
  
(** *** Conventional monad **)
unfold let (⊗) (wx:wst 'a) (wy:wst 'a) : wstrel 'a =
  fun p s0 s1 -> wx (fun rx -> wy (p rx) s1) s0

unfold let lift_rel (wm:wst 'a) : wstrel 'a = wm ⊗ wm

(**let deterministic (wm:wstrel 'a) : Type0 = forall s. wm (==) s s
let is_pure (wm:wstrel 'a) : Type0 = forall s1 s2. wm (fun (x, _) (y, _) -> x == y) s1 s2**)

unfold let elim_rel (wm:wstrel 'a) : wst 'a = //Pure (wst 'a) (requires (deterministic wm)) (ensures (fun _ -> True)) =
  fun p s -> wm (fun _ -> p) s s

unfold let ret_wstrel (x:'a) : wstrel 'a = bret_wstrel x x
unfold let bind_wstrel (#a #b:Type) (wm : wstrel a) (wf : a -> wstrel b) : wstrel b =
  bbind_wstrel wm (fun x0 x1 -> elim_rel (wf x0) ⊗ elim_rel (wf x1))
(**
unfold let bind_wstrel (#a #b:Type) (wm : wstrel a) (wf : a -> wstrel b) : wstrel b =
  bbind_wstrel wm (fun x0 x1 p s0 s1 ->
    (x0 == x1 ==> wf x0 p s0 s1) /\
    (x0 =!= x1 ==> (elim_rel (wf x0) ⊗ elim_rel (wf x1)) p s0 s1))**)

let get_wstrel l : wstrel int = 
  fun p s0 s1 -> p (s0 l, s0) (s1 l, s1)

let put_wstrel l v : wstrel unit =
  fun p s0 s1 -> p ((), st_upd s0 l v) ((), st_upd s1 l v)

let (====) #a (w1:wstrel a) (w2:wstrel a) =
  forall p s1 s2 . w1 p s1 s2 <==> w2 p s1 s2

(** Not needed in proving the monad morphism? **)
let wstrel_monad_law1 #a (w:wstrel a) : Lemma
  (bind_wstrel w ret_wstrel ==== w) = ()

let wstrel_monad_law2 #a #b (wf:a -> wstrel b) (x:a) : Lemma
  (bind_wstrel (ret_wstrel x) wf ==== wf x) by (compute ()) =
  admit ()
  
let wstrel_monad_law3 (#a #b #c:Type) (wm:wstrel a) (wf:a -> wstrel b) (wg:b -> wstrel c) : Lemma (
  bind_wstrel (bind_wstrel wm wf) wg ==== bind_wstrel wm (fun r -> bind_wstrel (wf r) wg)
) = admit ()

unfold let (⊑) (wp1 wp2: wstrel 'a): Type0 =
  forall p s0 s1. wp2 p s0 s1 ==> wp1 p s0 s1

let lemma_theta_rel_morphism #a #b (m:st a) (f:a -> st b) : Lemma (
  forall p s0 s1. theta_wstrel (bind_st m f) p s0 s1 <==> bind_wstrel (theta_wstrel m) (fun x -> theta_wstrel (f x)) p s0 s1
) =
  introduce forall p s0 s1. (theta_wstrel (bind_st m f) p s0 s1 <==> bind_wstrel (theta_wstrel m) (fun x -> theta_wstrel (f x)) p s0 s1)
with begin
     calc (<==>) {
       theta_wstrel (bind_st m f) p s0 s1;
       <==> { _ by (
         norm [delta_only [`%theta_wstrel];zeta];
         compute ()) }
       bind_wstrel (theta_wstrel m) (fun x -> theta_wstrel (f x)) p s0 s1;
     }
  end

type dm (a:Type) (w:wstrel a) =
  m:(st a){theta_wstrel m ⊑ w}

let ret_dm (a:Type) (x:a) : dm a (ret_wstrel x) = ret_st x

let bind_dm (a:Type) (b:Type)
            (wm:wstrel a) (wf:a -> wstrel b)
            (m:dm a wm) (f:(x:a -> dm b (wf x))) :
            dm b (bind_wstrel wm wf) =
  calc (⊑) {
    theta_wstrel (bind_st m f);
    ⊑ { lemma_theta_rel_morphism m f } 
    bind_wstrel (theta_wstrel m) (fun x -> theta_wstrel (f x));
    ⊑ {
      assert (theta_wstrel m ⊑ wm)
    }
    bind_wstrel wm (fun x -> theta_wstrel (f x));
    ⊑ {}
    bind_wstrel wm wf;
  };
  bind_st m f

let subcomp_dm (a:Type) (wp1 wp2:wstrel a) (m : dm a wp1) : Pure (dm a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) = m

unfold
let wstrel_if_then_else (wp1 wp2:wstrel 'a) (b:bool) : wstrel 'a =
  fun p s0 s1 -> (b ==> wp1 p s0 s1) /\ ((~b) ==> wp2 p s0 s1)

let dm_if_then_else (a : Type u#a) 
  (wp1 wp2: wstrel a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (wstrel_if_then_else wp1 wp2 b)

total
reifiable
reflectable
effect {
  StRelWp (a:Type) (wp : wstrel a)
  with {
       repr       = dm
     ; return     = ret_dm
     ; bind       = bind_dm
     ; subcomp    = subcomp_dm
     ; if_then_else = dm_if_then_else
     }
}
  
effect StRel
  (a:Type)
  (pre : state -> state -> Type0)
  (post : state -> state -> a * state -> a * state -> Type0) =
  StRelWp a (fun p s0 s1 -> pre s0 s1 /\ (forall r1 r2. post s0 s1 r1 r2 ==> p r1 r2)) 

unfold
let wp_lift_pure (w : pure_wp 'a) : wstrel 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  (fun p s0 s1 -> w (fun x -> ret_wstrel x p s0 s1))

assume val lift_pure_dm :
  a: Type ->
  w: pure_wp a ->
  f: (eqtype_as_type unit -> PURE a w) ->
  Tot (dm a (wp_lift_pure w))

sub_effect PURE ~> StRelWp = lift_pure_dm

let get l : StRel int (fun _ _ -> True) (fun is0 is1 (x0,s0) (x1,s1) -> is0 == s0 /\ is1 == s1 /\ x0 == s0 l /\ x1 == s1 l) =
  StRelWp?.reflect (st_get l)

let put l v : StRel unit (fun _ _ -> True) (fun is0 is1 (_,s0) (_,s1) -> s0 == st_upd is0 l v /\ s1 == st_upd is1 l v) =
  StRelWp?.reflect (st_put l v)

let test () : StRel unit (fun is0 is1 -> is0 false == is1 false) (fun _ _ (_,s0) (_,s1) -> s0 false == s1 false) =
  let x = get true in
  if x = 1 then put false x else put false 1

[@expect_failure]
let test2 () : StRel unit (fun is0 is1 -> is0 false == is1 false) (fun _ _ (_,s0) (_,s1) -> s0 false <> s1 false) =
  let x = get true in
  if x = 1 then put false x else put false 1
