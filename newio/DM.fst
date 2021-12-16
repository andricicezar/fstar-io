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
let dm (a:Type) (wp:hist a) (q:pure_post a) = 
  m:(io (v:a{q v})){wp `hist_ord` theta m}

let dm_return (a : Type) (x : a) : dm a (hist_return x) (fun r -> r == x) =
  io_return x

unfold
let bind_post (#a #b:Type) (q1:pure_post a) (q2:a -> pure_post b)
  : pure_post b
  = fun y -> exists x. q1 x ==> q2 x y

let dm_subcomp
  (q1 q2:pure_post 'a)
  (wp1 wp2 : hist 'a)
  (m: dm 'a wp1 q1) 
  (_:squash (forall x. q1 x ==> q2 x))
  (_:squash (wp1 `hist_ord` wp2)) :
  dm 'a wp2 q2= 
  admit ();
  m 
  
let dm_bind0
  (a b : Type)
  (wp_v : hist a)
  (wp_f:  a -> hist b)
  (post_v: pure_post a)
  (post_f: a -> pure_post b)
  (v : dm a wp_v post_v)
  (f : (x:a{post_v x} -> dm b (wp_f x) (bind_post post_v post_f))) :
  Tot (dm b (hist_bind wp_v wp_f) (bind_post post_v post_f)) =
  admit ();
  lemma_theta_is_monad_morphism_bind v f;

  assert (theta (io_bind v f) == hist_bind (theta v) (fun x -> theta (f x)));
  assert (wp_v `hist_ord` theta v);
  assert (forall r. wp_f r `hist_ord` theta (f r));
  assert (hist_bind wp_v wp_f `hist_ord` hist_bind (theta v) (fun x -> theta (f x)));

  (** goal: **)
  assert (hist_bind wp_v wp_f `hist_ord` theta (io_bind v f));

  io_bind #(x:a{post_v x}) #(x:b{bind_post post_v post_f x}) v f
  
let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (post_v: pure_post a)
  (post_f: a -> pure_post b)
  (v : dm a wp_v post_v)
  (f : (x:a{post_v x} -> dm b (wp_f x) (post_f x))) :
  Tot (dm b (hist_bind wp_v wp_f) (bind_post post_v post_f)) =
  let f' : (x:a{post_v x} -> dm b (wp_f x) (bind_post post_v post_f)) = begin
    fun x -> 
      dm_subcomp (post_f x) (bind_post post_v post_f) (wp_f x) (wp_f x) (f x) _ _
  end in
  dm_bind0 a b wp_v wp_f post_v post_f v f'

////////////////////////////////////////////////////////////////////////////////////////

let l_repr (a:Type) (p:pure_pre) (q:pure_post a) (wp:hist a) = 
  squash p -> dm a wp q

let l_return (a:Type) (x:a) : l_repr a True (fun r -> r == x) (hist_return x) = fun () -> dm_return a x

unfold let trivial_pre : pure_pre = True

unfold
let bind_pre (#a:Type) (p1:pure_pre) (q1:pure_post a) (p2:a -> pure_pre) : pure_pre
  = p1 /\ (forall x. q1 x ==> p2 x)

let l_bind (a b:Type)
  (p1:pure_pre) (q1:pure_post a)
  (p2:a -> pure_pre) (q2:a -> pure_post b)
  (wp1:hist a) (wp2:a -> hist b)
  (f:l_repr a p1 q1 wp1) (g:(x:a) -> l_repr b (p2 x) (q2 x) (wp2 x)) :
  Tot (l_repr b (bind_pre p1 q1 p2) (bind_post q1 q2) (hist_bind wp1 wp2)) =
  fun _ -> dm_bind a b wp1 wp2 q1 q2 (f _) (fun x -> g x _)

let l_subcomp (a:Type) (p1 p2:pure_pre) (q1 q2:pure_post a) (wp1:hist a) (wp2:hist a) (f:l_repr a p1 q1 wp1)
  : Pure (l_repr a p2 q2 wp2)
    (requires (
      (p2 ==> p1) /\
      (forall x. q1 x ==> q2 x) /\
      (wp1 `hist_ord` wp2)))
    (ensures fun _ -> True) =
  fun _ -> dm_subcomp q1 q2 wp1 wp2 (f _) _ _

unfold
let l_if_then_else 
  (a : Type)
  (p1 p2: pure_pre)
  (q1 q2: pure_post a)
  (wp1: hist a)
  (wp2: hist a)
  (f : l_repr a p1 q1 wp1)
  (g : l_repr a p2 q2 wp2)
  (b : bool) : Type =
  l_repr a
    ((b ==> p1) /\ ((~b) ==> p2)) 
    (fun x -> (b ==> q1 x) /\ ((~b) ==> q2 x)) 
    (hist_if_then_else wp1 wp2 b)

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
