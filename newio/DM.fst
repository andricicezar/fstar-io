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

total
reifiable
reflectable
layered_effect {
  IOwp : a:Type -> wp : hist #event a -> Effect
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
