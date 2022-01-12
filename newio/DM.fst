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

let rec return_of (x:'a) (f:io 'a) =
  match f with
  | Return x' -> x == x'
  | Call cmd arg k ->
     exists r'. return_of x (k r')


let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a{x `return_of` v} -> dm b (wp_f x))) :
  Tot (dm b (hist_bind wp_v wp_f)) =
  admit ();
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
