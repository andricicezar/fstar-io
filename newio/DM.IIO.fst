module DM.IIO

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

let iio_wps (cmd:cmds) (arg:iio_sig.args cmd) : hist #event (iio_sig.res cmd) = 
  fun p (h:trace) ->
    match cmd with
    | GetTrace -> io_pre cmd arg h /\ p [] (h <: iio_sig.res GetTrace)
    | _ -> 
      io_pre cmd arg h /\ (forall (r:iio_sig.res cmd). p [convert_call_to_event (cmd <: io_cmds) arg r] r)

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec theta #a
  (m : iio a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
      hist_bind (iio_wps cmd arg) (fun r -> theta (k r))
  
let lemma_theta_is_monad_morphism_ret v h p :
  Lemma (theta (iio_return v) == hist_return v) by (compute ()) = ()

let _hist_bind = hist_bind
let _hist_ord = hist_ord

let another_lemma (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) p h : 
  Lemma 
    (requires ((forall x. (wp2 x) `_hist_ord` (wp3 x)) /\ _hist_bind wp1 wp2 p h))
    (ensures (_hist_bind wp1 wp3 p h)) = ()

let another_lemma' (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) : 
  Lemma 
    (requires ((forall x. (wp2 x) `_hist_ord` (wp3 x))))
    (ensures (_hist_bind wp1 wp2 `_hist_ord` _hist_bind wp1 wp3)) = ()

let rec lemma_theta_is_lax_morphism_bind (m:iio 'a) (f:'a -> iio 'b) :
  Lemma
    (hist_bind (theta m) (fun x -> theta (f x)) `hist_ord` theta (iio_bind m f)) = 
  match m with
  | Return x ->
    calc (hist_ord) {
      hist_bind (theta m) (fun x -> theta (f x));
      == { 
        assert (hist_bind (theta (Return x)) (fun x -> theta (f x))
          == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta (Return x)) (fun x -> theta (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_return x) (fun x -> theta (f x));
      `hist_ord` {} (** here there is an eta that forces us to use `hist_ord` **)
      theta (f x); 
      == {} // unfold io_bind
      theta (iio_bind (Return x) f);
      == {}
      theta (iio_bind m f);
    }
  | Call cmd arg k ->
    calc (hist_ord) {
      hist_bind (theta m) (fun x -> theta (f x)); 
      == {
        assert (hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x))
           == hist_bind (theta m) (fun x -> theta (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta (Call cmd arg k)) (fun x -> theta (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (iio_wps cmd arg) (fun r -> theta (k r))) (fun x -> theta (f x));
      == { lemma_hist_bind_associativity (iio_wps cmd arg) (fun r -> theta (k r)) (fun x -> theta (f x)) }
      hist_bind (iio_wps cmd arg) (fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)));
      `hist_ord` { (** if we get rid of the hist_ord from the other branch, this becomes an equality **)
        let rhs1 : iio_sig.res cmd -> hist 'b = fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)) in
        let rhs2 : iio_sig.res cmd -> hist 'b = fun r -> theta (iio_bind (k r) f) in
        introduce forall (r:iio_sig.res cmd). (rhs1 r) `hist_ord` (rhs2 r) with begin
          lemma_theta_is_lax_morphism_bind (k r) f
        end;
        another_lemma' #event #(iio_sig.res cmd) #'b (iio_wps cmd arg) rhs1 rhs2;
        assert (hist_bind (iio_wps cmd arg) rhs1 `hist_ord #_ #'b` hist_bind (iio_wps cmd arg) rhs2) by (assumption ())
      }
      hist_bind (iio_wps cmd arg) (fun r -> theta (iio_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      theta (Call cmd arg (fun r -> iio_bind (k r) f));
      `hist_ord` { _ by (compute (); dump "H") } // unfold iio_bind
      theta (iio_bind (Call cmd arg k) f);
      == {}
      theta (iio_bind m f);
    }

// The Dijkstra Monad
let dm (a:Type) (wp:hist a) =
  (m:(iio a){wp `hist_ord` theta m})

let dm_return (a : Type) (x : a) : dm a (hist_return x) =
  iio_return x

let dm_bind
  (a b : Type)
  (wp_v : hist a)
  (wp_f: a -> hist b)
  (v : dm a wp_v)
  (f : (x:a -> dm b (wp_f x))) :
  Tot (dm b (hist_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind v f;
  iio_bind v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (a : Type) (wp1 wp2: hist a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (hist_if_then_else wp1 wp2 b)
