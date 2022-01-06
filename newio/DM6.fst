module DM6

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

(** TODO: parameterize the entire file by op and sig **)

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
let dm (a:Type) (wp:hist a) = (m:(io a){wp `hist_ord` theta m})

let dm_return (a : Type) (x : a) : dm a (hist_return x) =
  io_return x

let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : ((x:a) -> dm b (wp_f x))) :
  Tot (dm b (hist_bind wp_v wp_f)) =
  lemma_theta_is_monad_morphism_bind v f;
  io_bind v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (a : Type) (wp1 wp2: hist a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (hist_if_then_else wp1 wp2 b)

////////////////////////////////////////////////////////////////////////////////////////

let io_subcomp (a:Type)
  (q1:pure_post a) (q2:pure_post a)
  (m : io (v:a{q1 v})) :
  Pure (io (v:a{q2 v})) 
    (requires (forall x. q1 x ==> q2 x))
    (ensures (fun r -> True)) =
  admit ();
  m

unfold
let pure_post_return (x:'a) : pure_post 'a = fun y -> x == y

unfold
let pure_post_bind (#a #b:Type) (q1:pure_post a) (q2:a -> pure_post b) : pure_post b =
  fun y -> exists (x:a{q1 x}). q2 x y

unfold
let pure_post_if_then_else (q1 q2:pure_post 'a) (b:bool) : pure_post 'a =
  fun x -> (b ==> q1 x) /\ ((~b) ==> q2 x)

/////////////////////////////////////////////////////////////////////////////////////

(** Later we refine the output type of the dijkstra monad with the pure post condition (q),
which forces us to index the dijkstra monad by a weakest-precondition of type `hist (v:a{q v})`.
For cleanliness reasons, we define a synonym for that called `histq`. **)

unfold
let histq #event a (q:pure_post a) = hist #event (v:a{q v})

unfold
let histq_ord
  (#q1:pure_post 'a) (#q2:pure_post 'a)
  (wp1: histq 'a q1) 
  (wp2: histq 'a q2) :
  Pure Type0
    (requires (forall x. q2 x ==> q1 x))
    (ensures (fun _ -> True)) =
  forall h (p:hist_post (v:'a{q1 v})). 
    wp1 p h ==> wp2 (fun lt (r:'a{q2 r}) -> p lt (r <: (x:'a{q1 x}))) h

unfold
let histq_return (x:'a) : histq 'a (pure_post_return x) =
  hist_return x

let lemma_histq_subcomp_post
  (a b:Type)
  (q1:pure_post a) (q2:a -> pure_post b)
  (wp:(x:a{q1 x}) -> histq b (q2 x)) 
  (x: a{q1 x})
  (p1 p2 : hist_post (v:b{pure_post_bind q1 q2 v}))
  (h:trace) :
  Lemma
    (requires (p1 `hist_post_ord` p2 /\ wp x (fun lt r -> p1 lt r) h))
    (ensures (wp x (fun lt r -> p2 lt r) h)) = ()

unfold
let histq_subcomp_bind
  (a b:Type)
  (q1:pure_post a) (q2:a -> pure_post b)
  (wp2:(x:a) -> histq b (q2 x)) 
  (x: a{q1 x}) :
  Tot (histq b (pure_post_bind q1 q2)) = 
  Classical.forall_intro_3 (Classical.move_requires_3 (lemma_histq_subcomp_post a b q1 q2 wp2 x));
  fun p -> wp2 x (fun lt (r: b{q2 x r}) -> p lt r)

unfold
let histq_if_then_else (q1 q2:pure_post 'a) (wp1:histq 'a q1) (wp2:histq 'a q2) (b:bool) : histq 'a (pure_post_if_then_else q1 q2 b) by (
  explode ()
)=
  admit ();
  (** TODO: show that histq_if_then_else is monotonic **)
  fun (p:trace -> (x:'a{pure_post_if_then_else q1 q2 b x}) -> Type0) h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h)

let dm_subcomp_histq (a:Type) 
  (q1:pure_post a) (q2:pure_post a)
  (wp1: histq a q1) 
  (wp2: histq a q2)
  (f : dm (v:a{q1 v}) wp1) :
  Pure (dm (v:a{q2 v}) wp2)
    (requires ((forall x. q1 x ==> q2 x) /\ wp2 `histq_ord` wp1))
    (ensures fun _ -> True) =
  assert (wp1 `hist_ord` (theta f));
  assert (wp2 `histq_ord` wp1);

  let m = io_subcomp a q1 q2 f in
  assert (wp2 `hist_ord` (theta m));
  m

/////////////////////////////////////////////////////////////////////////////

let dmq (a:Type) (q:pure_post a) (wp:histq a q) = 
  dm (v:a{q v}) wp 

let dmq_return (a:Type) (x:a) : dmq a (pure_post_return x) (histq_return x) = 
  dm_return _ x

let dmq_bind (a b:Type)
  (q1:pure_post a) (q2:a -> pure_post b)
  (wp1:histq a q1) (wp2:(x:a) -> histq b (q2 x))
  (f:dmq a q1 wp1) 
  (g:(x:a{q1 x}) -> dmq b (q2 x) (wp2 x)) :
  Tot (dmq b (pure_post_bind q1 q2) (hist_bind wp1 (histq_subcomp_bind a b q1 q2 wp2))) =
    dm_bind 
      (v:a{q1 v})
      (v:b{pure_post_bind q1 q2 v})
      wp1
      (histq_subcomp_bind a b q1 q2 wp2)
      f
      (fun (x:a{q1 x}) -> 
        dm_subcomp_histq b
         (q2 x) (pure_post_bind q1 q2)
         (wp2 x)
         (histq_subcomp_bind a b q1 q2 wp2 x)
         (g x))

let dmq_subcomp (a:Type) (q1 q2:pure_post a) (wp1:hist (v:a{q1 v})) (wp2:hist (v:a{q2 v})) (f:dmq a q1 wp1) :
  Pure (dmq a q2 wp2)
    (requires (
      (forall x. q1 x ==> q2 x) /\
      (wp2 `histq_ord` wp1)))
    (ensures fun _ -> True) =
  dm_subcomp_histq a q1 q2 wp1 wp2 f

///////////////////////////////////////////////////////////////////////////

let hist_as_requires (wp:hist 'a) = forall h. wp (fun _ _ -> True) h

let pdmq (a:Type) (wp:hist a) = 
  squash (hist_as_requires wp) -> dm a wp 

let pdmq_return (a:Type) (x:a) : pdmq a (hist_return x) =
  fun _ -> dm_return _ x

let pdmq_bind (a b:Type)
  (wp1:hist a) (wp2:(x:a) -> hist b)
  (f:pdmq a wp1) 
  (g:(x:a) -> pdmq b (wp2 x))
  (pre:squash (forall r l p h. wp1 p h /\ (p l r ==> (hist_as_requires (wp2 r))))) :
  Tot (dm b (hist_bind wp1 wp2)) =
  assume (hist_as_requires wp1); (** this should be easy to prove by instantiating pre **)
  dm_bind a b wp1 wp2 (f _) (fun (x:a) -> 
    assert (forall l p h. wp1 p h /\ (p l x ==> (hist_as_requires (wp2 x))));
    assume (exists l. forall p h. wp1 p h /\ p l x);
    assert (hist_as_requires (wp2 x));
    g x _)

let pdmq_subcomp (a:Type) (wp1:hist a) (wp2:hist a) (f:pdmq a wp1) :
  Pure (pdmq a wp2)
    (requires (
      (wp2 `hist_ord` wp1)))
    (ensures fun _ -> True) =
  fun _ -> dm_subcomp a wp1 wp2 (f ())
  
unfold
let pdmq_if_then_else 
  (a : Type)
  (wp1: hist a)
  (wp2: hist a)
  (f : pdmq a wp1)
  (g : pdmq a wp2)
  (b : bool) : Type =
  pdmq a
    (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
effect {
  IOwp (a:Type) (wp : hist #event a) 
  with {
       repr       = pdmq
     ; return     = pdmq_return
     ; bind       = pdmq_bind 
     ; subcomp    = pdmq_subcomp
     ; if_then_else = pdmq_if_then_else
     }
}

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a 
    (fun _ -> True)
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt r. post h lt r ==>  p lt r)) 


unfold let as_requires (#a: Type) (wp: pure_wp a) = wp (fun x -> True)
unfold let as_ensures (#a: Type) (wp: pure_wp a) (x: a) = ~(wp (fun y -> (y =!= x)))

unfold
let histq_for_pure (#event #a:Type) (pre:pure_pre) q : histq #event a q = fun p h -> pre /\ (forall (r:a{q r}). p [] r)

(** histq_for_pure is labeled with unfold, but when trying to prove the lift,
the unfolding confuses
the SMT. Therefore, the following is just a trick to get an automated proof of the lift **)
let histq_for_pure0 (#event #a:Type) = histq_for_pure #event #a
let lift_pure_pdmq0 (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  pdmq a (as_ensures w) (histq_for_pure0 (as_requires w) (as_ensures w)) =
  fun (pre:squash (forall h. histq_for_pure0 #event #a (as_requires w) (as_ensures w) (fun _ _ -> True) h)) ->
    assert (forall h. histq_for_pure0 #event #a (as_requires w) (as_ensures w) (fun _ _ -> True) h); 
    assert ((forall h. histq_for_pure0 #event #a (as_requires w) (as_ensures w) (fun _ _ -> True) h) ==>
        as_requires w) by (
        norm [delta_only [`%histq_for_pure0;`%histq_for_pure]];
        let impl = implies_intro () in
        let impl = instantiate impl (`([])) in
        let lhs, _ = destruct_and impl in
        assumption ()
    );
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let r = f () in
    let r' = dmq_return _ r in
    dmq_subcomp _ _ _ _ _ r'

let lift_pure_pdmq (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) :
  pdmq a (as_ensures w) (histq_for_pure (as_requires w) (as_ensures w)) =
    lift_pure_pdmq0 a w f

sub_effect PURE ~> IOwp = lift_pure_pdmq
  
assume val p : prop
assume val p' : prop
assume val pure_lemma (_:unit) : Lemma p
assume val some_f (_:squash p) : IO unit (fun _ -> True) (fun _ _ _ -> True)
assume val some_f' : unit -> IO unit (requires (fun _ -> p)) (ensures fun _ _ _ -> p')

let test () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

  
let test'' () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ();
  some_f' ();
  assert p'

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pre cmd argz h))
    (ensures (fun h lt r ->
        lt == [convert_call_to_event cmd argz r])) =
  IOwp?.reflect (fun _ -> io_call cmd argz)

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h lt r -> ~(is_open fd (List.rev lt @ h))) =
  let _ = static_cmd Close fd in
  ()

let testStatic2 () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile "../Makefile" in
  if Some? fd then begin (** test if Openfile was successful **)
    let msg = static_cmd Read (Some?.v fd) in
    let _ = static_cmd Close (Some?.v fd) in
    ()
  end else ()
