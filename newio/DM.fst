module DM

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec theta #a
  (m : io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
    hist_bind (io_wps cmd arg) (fun r -> theta (k r))

let lemma_theta_is_monad_morphism_ret v h p :
  Lemma
    (theta (io_return v) == hist_return v) by (compute ()) = ()

(** TODO: remove the admits **)
let rec lemma_theta_is_monad_morphism_bind (m:io 'a) (f:'a -> io 'b) :
  Lemma
    (theta (io_bind m f) == hist_bind (theta m) (fun x -> theta (f x))) = 
  match m with
  | Return x ->
    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Return x) f);
      == {} // unfold io_bind
      theta (f x); 
      == { _ by (tadmit ()) } // unfold hist_bind
      hist_bind (hist_return x) (fun x -> theta (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (theta (Return x)) (fun x -> theta (f x));
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Return x)) (fun x -> theta (f x))
      == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())
  | Call cmd arg k ->
    (** this should be useful later to do a rewrite **)
    introduce forall (r:io_resm cmd). theta (io_bind (k r) f) == hist_bind (theta (k r)) (fun x -> theta (f x)) with begin
      lemma_theta_is_monad_morphism_bind (k r) f
    end;

    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Call cmd arg k) f);
      == { _ by (compute ()) } // unfold io_bind
      theta (Call cmd arg (fun r -> io_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      hist_bind (io_wps cmd arg) (fun r -> theta (io_bind (k r) f));
      == { _ by (tadmit ()) } // rewrite here by applying this lemma again for (k r) and f
      hist_bind (io_wps cmd arg) (fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)));
      == { lemma_hist_bind_associativity (io_wps cmd arg) (fun r -> theta (k r)) (fun x -> theta (f x)) }
      hist_bind (hist_bind (io_wps cmd arg) (fun r -> theta (k r))) (fun x -> theta (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x));
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x))
      == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())

// The Dijkstra Monad
let dm (a:Type) (wp:hist a) =
  (m:(io a){wp `hist_ord` theta m})

let dm_return (a : Type) (x : a) : dm a (hist_return x) =
  io_return x

let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a -> dm b (wp_f x))) :
  Tot (dm b (hist_bind wp_v wp_f)) =
  lemma_theta_is_monad_morphism_bind v f;
  (** hist is monotonic.
  
  assert (theta (io_bind v f) == hist_bind (theta v) (fun x -> theta (f x)));
  assert (wp_v `hist_ord` theta v);
  assert (forall r. wp_f r `hist_ord` theta (f r));
  assert (hist_bind wp_v wp_f `hist_ord` hist_bind (theta v) (fun x -> theta (f x)));

  (** goal: **)
  assert (hist_bind wp_v wp_f `hist_ord` theta (io_bind v f));**)
  io_bind v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (a : Type) (wp1 wp2: hist a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (hist_if_then_else wp1 wp2 b)

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  f ()

(** inspired from fstar/examples/layeredeffects/Alg.fst **)
let lift_pure_dm (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  Pure (dm a (wp_lift_pure_hist w)) (requires w (fun _ -> True)) (ensures fun _ -> True) =
  let r = elim_pure #a #w f in
  let r' : dm a (hist_return r) = dm_return a r in
  dm_subcomp _ (hist_return r) (wp_lift_pure_hist w) r'

////////////////////////////////////////////////////////////////////////////////////////

let l_repr (a:Type) (p:pure_pre) (q:pure_post a) (wp:hist (v:a{q v})) = 
  squash p -> dm (v:a{q v}) wp 

let l_return (a:Type) (x:a) : l_repr a True (fun _ -> True) (hist_return x) = fun () -> dm_return a x

unfold let trivial_pre : pure_pre = True

unfold
let bind_pre (#a:Type) (p1:pure_pre) (q1:pure_post a) (p2:(v:a{q1 v}) -> pure_pre) : pure_pre
  = p1 /\ (forall x. q1 x ==> p2 x)

unfold
let bind_post (#a #b:Type) (q1:pure_post a) (q2:(v:a{q1 v}) -> pure_post b)
  : pure_post b
  = fun y -> exists (x:a{q1 x}). q2 x y

let lemma_recast_wp000
  (a b:Type)
  (q1:pure_post a) (q2:(v:a{q1 v}) -> pure_post b)
  (xwp:(x:a{q1 x}) -> hist (v:b{q2 x v})) 
  (x: a{q1 x})
  (p1 p2 : hist_post (v:b{bind_post q1 q2 v}))
  (h:trace) :
  Lemma
    (requires (p1 `hist_post_ord` p2 /\ xwp x (fun lt r -> p1 lt r) h))
    (ensures (xwp x (fun lt r -> p2 lt r) h)) = ()

let recast_wp
  (a b:Type)
  (q1:pure_post a) (q2:(v:a{q1 v}) -> pure_post b)
  (wp2:(x:a{q1 x}) -> hist (v:b{q2 x v})) 
  (x: a{q1 x}) :
  Tot (hist (v:b{bind_post q1 q2 v})) = 
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_recast_wp000 a b q1 q2 wp2 x));
  fun p -> wp2 x (fun lt (r: b{q2 x r}) -> p lt r)

let recast_dm
  (a b:Type)
  (q1:pure_post a) 
  (q2:(v:a{q1 v}) -> pure_post b)
  (wp:(x:a{q1 x}) -> hist (v:b{q2 x v})) 
  (x: a{q1 x})
  (g: dm (v:b{q2 x v}) (wp x)) :
  Tot (dm (v:b{bind_post q1 q2 v}) (recast_wp a b q1 q2 wp x)) = 
  admit ();
  dm_bind
    (v:b{q2 x v}) (v:b{bind_post q1 q2 v})
    (wp x)
    (fun r -> hist_return r)
    g
    (fun (v:b{q2 x v}) -> 
      let v' : (vv:b{bind_post q1 q2 vv}) = v in
      Return v')
  
  

let l_bind (a b:Type)
  (p1:pure_pre) (q1:pure_post a)
  (p2:(v:a{q1 v}) -> pure_pre) (q2:(v:a{q1 v}) -> pure_post b)
  (wp1:hist (v:a{q1 v})) (wp2:(x:a{q1 x}) -> hist (v:b{q2 x v}))
  (f:l_repr a p1 q1 wp1) (g:(x:a{q1 x} -> l_repr b (p2 x) (q2 x) (wp2 x))) :
  Tot (l_repr b (bind_pre p1 q1 p2) (bind_post q1 q2) (hist_bind wp1 (recast_wp a b q1 q2 wp2))) =
  fun _ -> 
    dm_bind 
      (v:a{q1 v})
      (v:b{bind_post q1 q2 v})
      wp1
      (recast_wp a b q1 q2 wp2)
      (f _)
      (fun (x:a{q1 x}) -> 
        let g' : dm (v:b{q2 x v}) (wp2 x) = g x _ in
        recast_dm a b q1 q2 wp2 x g')

let l_subcomp (a:Type) (p1 p2:pure_pre) (q1 q2:pure_post a) (wp1:hist (v:a{q1 v})) (wp2:hist (v:a{q2 v})) (f:l_repr a p1 q1 wp1)
  : Pure (l_repr a p2 q2 wp2)
    (requires (
      (p2 ==> p1) /\
      (forall x. q1 x ==> q2 x) /\
      (forall (p:hist_post (v:a{q2 v})) h. wp2 p h ==> wp1 (fun lt r -> p lt (r <: (v:a{q2 v}))) h)))
    (ensures fun _ -> True)
  = fun _ ->  (
    admit ();
    f ())

unfold
let l_if_then_else 
  (a : Type)
  (p1 p2: pure_pre)
  (q1 q2: pure_post a)
  (wp1: hist (v:a{q1 v}))
  (wp2: hist (v:a{q2 v}))
  (f : l_repr a p1 q1 wp1)
  (g : l_repr a p2 q2 wp2)
  (b : bool) : Type =
  admit ();
  l_repr (x:a{(b ==> q1 x) /\ ((~b) ==> q2 x)})
    ((b ==> p1) /\ ((~b) ==> p2)) 
    (fun x -> (b ==> q1 x) /\ ((~b) ==> q2 x)) 
    (fun p h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h))

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> p : pure_pre -> q : pure_post a -> wp : hist (v:a{q v}) -> Effect
  with
       repr       = l_repr 
     ; return     = l_return
     ; bind       = l_bind

     ; subcomp      = l_subcomp
     ; if_then_else = l_if_then_else
}


(** inspired from fstar/examples/layeredeffects/Alg.fst **)
let lift_pure_l (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  Pure (l_repr a (wp_lift_pure_hist w) (w (fun _ -> True))) (requires w (fun _ -> True)) (ensures fun _ -> True) =
  let r = elim_pure #a #w f in
  let r'  = l_return a r in
  l_subcomp _ (hist_return r) (wp_lift_pure_hist w) True (w (fun _ -> True)) r'

sub_effect PURE ~> IOwp = lift_pure_l

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a 
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt r. post h lt r ==>  p lt r)) 
    True

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pres cmd argz h))
    (ensures (fun h lt r ->
        lt == [convert_call_to_event cmd argz r])) =
  IOwp?.reflect (fun _ -> io_call cmd argz)

let testStatic2 () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile "../Makefile" in
  if Some? fd then begin (** test if Openfile was successful **)
    let msg = static_cmd Read (Some?.v fd) in
    let _ = static_cmd Close (Some?.v fd) in
    ()
  end else ()

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h lt r -> ~(is_open fd (trace_append h lt))) =
  let _ = static_cmd Close fd in
  ()


assume val p' : prop
assume val pure_lemma (_:unit) : Lemma p'
assume val some_f : unit -> IO unit (requires (fun _ -> p')) (ensures fun _ _ _ -> True)
  
let test () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  assert p'
  
let test' () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

let test'' () : IO unit (fun _ -> True) (fun _ _ _ -> True) by (explode (); dump "H") =
  pure_lemma ();
  assert p';
  some_f ()
