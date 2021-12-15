module DM

open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

(** TODO:
- [ ] prove bind
- [ ] write a test file
**)

type test a =
 | Ret : a -> test a
 | Call' : int -> a -> test a

assume val f : hist 'a -> hist 'a
assume val g : test 'a -> hist 'a 

let testing (m:test 'a) =
  match m with
  | Ret x -> 
    calc (==) {
      f (g (m));
      == {}
      f (g (Ret x));
    }
  | _ -> ()

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

let lemma_theta_is_monad_morphism_bind (#a:Type u#a) (#b:Type u#b) (m:io a) (f:a -> io b) :
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
      == { _ by (tadmit ()) } // fold hist_bind
      hist_bind (hist_return x) (fun x -> theta (f x));
      == { _ by (compute ()) } // fold theta
      hist_bind (theta (Return x)) (fun x -> theta (f x));
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Return x)) (fun x -> theta (f x))
      == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())
  | Call cmd arg k ->
    calc (==) {
      theta (io_bind m f);
      == {}
      theta (io_bind (Call cmd arg k) f);
      == { _ by (compute ()) } // unfold io_bind
      theta (Call cmd arg (fun r -> io_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      hist_bind (io_wps cmd arg) (fun r -> theta (io_bind (k r) f));
      == { (** lemma_theta_is_monad_morphism_bind_cont k f; **) _ by (tadmit ()) } // apply this lemma again for (k r) and f
      hist_bind (io_wps cmd arg) (fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)));
      == { _ by (tadmit ()) } // monad law 3
      hist_bind (hist_bind (io_wps cmd arg) (fun r -> theta (k r))) (fun x -> theta (f x));
      == { _ by (compute ()) } // fold theta
      hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x));
      == { assert (m == Call cmd arg k); _ by (rewrite_eqs_from_context (); tadmit ()) }
      hist_bind (theta m) (fun x -> theta (f x));
    };
    (** this should be inside calc, but for some reason it fails there **)
    assert (hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x))
      == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())

let lemma_theta_is_monad_morphism_bind_cont (#a:Type u#a) (#b:Type u#b) (#c:Type u#c) (k:c -> io a) (f:a -> io b) (r:c) :
  Lemma
    (theta (io_bind (k r) f) == hist_bind (theta (k r)) (fun x -> theta (f x))) = 
  lemma_theta_is_monad_morphism_bind #a #b (k r) f
  
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

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : hist a -> Effect
  with
       repr       = dm 
     ; return     = dm_return
     ; bind       = dm_bind

     ; subcomp      = dm_subcomp
     ; if_then_else = dm_if_then_else
}

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

sub_effect PURE ~> IOwp = lift_pure_dm

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a (fun (p:hist_post a) (h:trace) ->
    pre h /\ (forall lt r. post h lt r ==>  p lt r))

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pres cmd argz h))
    (ensures (fun h lt r ->
        lt == [convert_call_to_event cmd argz r])) =
  IOwp?.reflect (io_call cmd argz)

let testStatic2 () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  let fd = static_cmd Openfile "../Makefile" in
  if Some? fd then (** test if Openfile was successful **)
    let msg = static_cmd Read (Some?.v fd) in
    let _ = static_cmd Close (Some?.v fd) in
    ()
  else ()

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h lt r -> ~(is_open fd (trace_append h lt))) =
  let _ = static_cmd Close fd in
  ()
