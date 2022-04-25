module DM3

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist
open DM

(** The repr is indexed by the pure post-condition, and it trie sto encode it in the 
    weakest-precondition. 
    
    This file fails because of two reasons:
    1. lemma_wconj_bind_hist_ord_bind_wconj.
    2. if a pure prop is implied by the weakest-precondition, the prop can not be checked with a 
       pure pre-condition. **)

let wconj (wp:hist 'a) (q:pure_post 'a) : hist 'a =
  fun p -> wp (fun lt r -> q r ==> p lt r)

let dmq (a:Type) (wp:hist a) (q:pure_post a) =
  dm a (wconj wp q)

let dmq_return (a:Type) (x:a) : dmq a (hist_return x) (fun r -> r == x) =
  dm_return a x
  
unfold
let bind_post (#a #b:Type) (q1:pure_post a) (q2:a -> pure_post b) : pure_post b =
  fun y -> exists x. q1 x ==> q2 x y

let lemma_wconj_bind_hist_ord_bind_wconj
 (a b:Type)
 (q1:pure_post a) (q2:a -> pure_post b)
 (wp1:hist a) (wp2:(x:a) -> hist b) :
 Lemma (
   wconj (hist_bind wp1 wp2) (bind_post q1 q2) `hist_ord`
     hist_bind (wconj wp1 q1) (fun x -> wconj (wp2 x) (q2 x))) = 
 admit ();
 assert (forall h p.
   (fun lt r -> wp2 r (fun lt' r' -> (bind_post q1 q2 r') /\ p (lt @ lt') r') (rev lt @ h))
   `hist_post_ord` (fun lt r -> q1 r ==> wp2 r (fun lt' r' -> q2 r r' ==> p (lt @ lt') r') (rev lt @ h)));
 ()


let dmq_bind (a b:Type)
  (q1:pure_post a) (q2:a -> pure_post b)
  (wp1:hist a) (wp2:(x:a) -> hist b)
  (f:dmq a wp1 q1) 
  (g:(x:a) -> dmq b (wp2 x) (q2 x)) :
  Tot (dmq b (hist_bind wp1 wp2) (bind_post q1 q2))  =
  let d = dm_bind a b (wconj wp1 q1) (fun x -> wconj (wp2 x) (q2 x)) f g in
  lemma_wconj_bind_hist_ord_bind_wconj a b q1 q2 wp1 wp2;
  dm_subcomp _ _ _ d

////////////////////////////////////////////////////////

let l_repr (a:Type) (pre:pure_pre) (q:pure_post a) (wp:hist a) = 
  squash pre -> dmq a wp q

let l_return (a:Type) (x:a) : l_repr a True (fun r -> r == x) (hist_return x) = 
  fun () -> dm_return a x

unfold let trivial_pre : pure_pre = True

unfold
let bind_pre (#a:Type) (p1:pure_pre) (q1:pure_post a) (p2:a -> pure_pre) : pure_pre
  = p1 /\ (forall x. q1 x ==> p2 x)

let l_bind (a b:Type)
  (p1:pure_pre) (q1:pure_post a)
  (p2:a -> pure_pre) (q2:a -> pure_post b)
  (wp1:hist a) (wp2:(x:a) -> hist b)
  (f:l_repr a p1 q1 wp1) 
  (g:(x:a) -> l_repr b (p2 x) (q2 x) (wp2 x)) :
  Tot (l_repr b (bind_pre p1 q1 p2) (bind_post q1 q2) (hist_bind wp1 wp2)) =
  fun (pre:squash (bind_pre p1 q1 p2)) -> 
    dmq_bind a b q1 q2 wp1 wp2 (f pre) (fun x ->
      assume (q1 x); g x pre)

let l_subcomp (a:Type) (p1 p2:pure_pre) (q1 q2:pure_post a) (wp1 wp2:hist a) (f:l_repr a p1 q1 wp1)
  : Pure (l_repr a p2 q2 wp2)
    (requires (
      (p2 ==> p1) /\
      (forall x. q1 x ==> q2 x) /\
      (hist_ord wp2 wp1)))
    (ensures fun _ -> True) =
  fun _ -> dm_subcomp a _ _ (f ())

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> p : pure_pre -> q : pure_post a -> wp : hist #event a -> Effect
  with
       repr       = l_repr 
     ; return     = l_return
     ; bind       = l_bind

     ; subcomp      = l_subcomp
}

let trivial_wp (#a:Type) () : hist a = fun p h -> forall r. p [] r
unfold let as_requires (#a: Type) (wp: pure_wp a) = wp (fun x -> True)
unfold let as_ensures (#a: Type) (wp: pure_wp a) (x: a) = ~(wp (fun y -> (y =!= x)))

let lift_pure_pdmq (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : 
  l_repr a (as_requires w) (as_ensures w) (trivial_wp ()) =
  fun _ ->
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let r = f () in
    let r' = dmq_return a r in
    dm_subcomp _ _ _ r'

sub_effect PURE ~> IOwp = lift_pure_pdmq

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a 
    True
    (fun _ -> True)
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt r. post h lt r ==>  p lt r)) 

assume val p : prop
assume val p' : prop
assume val pure_lemma (_:unit) : Lemma p
assume val some_f (_:squash p) : IO unit (fun _ -> True) (fun _ _ _ -> True)
assume val some_f' : unit -> IO unit (requires (fun _ -> p)) (ensures fun _ _ _ -> p')

let test () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

(** The prop p' in the wp of some_f' can not be checked by the assert **)
let test'' () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ();
  some_f' ();
  assert p'


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
