module DM.IO

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Free.IO
open Hist

unfold let io_wps (cmd:io_cmds) (arg:io_args cmd) : hist #event (io_resm cmd) = fun p h ->
  match cmd with
 // | GetTrace -> p [] h
  | _ -> io_pre cmd arg h /\ (forall r. p [convert_call_to_event cmd arg r] r)

(** Inspierd from Kenji's thesis (2.4.5) **)
let rec theta #a
  (m : io a) : hist a =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
    hist_bind (io_wps cmd arg) (fun r -> theta (k r))
  
let lemma_theta_is_monad_morphism_ret v h p :
  Lemma (theta (io_return v) == hist_return v) by (compute ()) = ()

let rec lemma_theta_is_lax_morphism_bind (m:io 'a) (f:'a -> io 'b) :
  Lemma
    (hist_bind (theta m) (fun x -> theta (f x)) `hist_ord` theta (io_bind m f)) = 
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
      theta (io_bind (Return x) f);
      == {}
      theta (io_bind m f);
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
      hist_bind (hist_bind (io_wps cmd arg) (fun r -> theta (k r))) (fun x -> theta (f x));
      == { lemma_hist_bind_associativity (io_wps cmd arg) (fun r -> theta (k r)) (fun x -> theta (f x)) }
      hist_bind (io_wps cmd arg) (fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)));
      `hist_ord` { (** if we get rid of the hist_ord from the other branch, this becomes an equality **)
        let rhs1 : io_resm cmd -> hist 'b = fun r -> theta (io_bind (k r) f) in
        let rhs2 : io_resm cmd -> hist 'b = fun r -> hist_bind (theta (k r)) (fun x -> theta (f x)) in
        introduce forall (r:io_resm cmd). (rhs2 r) `hist_ord` (rhs1 r) with begin
          lemma_theta_is_lax_morphism_bind (k r) f
        end;

        assert (hist_bind (io_wps cmd arg) rhs2 `hist_ord` hist_bind (io_wps cmd arg) rhs1)
      }
      hist_bind (io_wps cmd arg) (fun r -> theta (io_bind (k r) f));
      == { _ by (compute ()) } // unfold theta
      theta (Call cmd arg (fun r -> io_bind (k r) f));
      == { _ by (compute ()) } // unfold io_bind
      theta (io_bind (Call cmd arg k) f);
      == {}
      theta (io_bind m f);
    }

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
  lemma_theta_is_lax_morphism_bind v f;
  io_bind v f

let dm_subcomp (a:Type) (wp1 wp2: hist a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (a : Type) (wp1 wp2: hist a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (hist_if_then_else wp1 wp2 b)
