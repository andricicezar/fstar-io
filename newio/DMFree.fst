module DMFree

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
open Hist

type op_wp (op:Type) (s:op_sig op) (event:Type) = (cmd:op) -> (arg:s.args cmd) -> hist #event (s.res cmd arg)

(** Inspierd from Kenji's thesis (2.4.5) **)
val theta : #a:Type -> #op:Type -> #s:op_sig op -> #event:Type -> cmd_wp:op_wp op s event -> free op s a -> hist #event a
let rec theta #a #op #s #event cmd_wp m =
  match m with
  | Return x -> hist_return x
  | Call cmd arg k ->
      hist_bind (cmd_wp cmd arg) (fun r -> theta cmd_wp (k r))
  
let lemma_theta_is_monad_morphism_ret (#op:Type) (#s:op_sig op) (#event:Type) (cmd_wp:op_wp op s event) (v:'a) :
  Lemma (theta cmd_wp (free_return op s 'a v) == hist_return v) by (compute ()) = ()

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

let rec lemma_theta_is_lax_morphism_bind (#op:Type) (#s:op_sig op) (#event:Type) (cmd_wp:op_wp op s event) (m:free op s 'a) (f:'a -> free op s 'b) :
  Lemma
    (hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x)) `hist_ord` theta cmd_wp (free_bind op s _ _ m f)) = 
  match m with
  | Return x ->
    calc (hist_ord) {
      hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x));
      == { 
        assert (hist_bind (theta cmd_wp (Return x)) (fun x -> theta cmd_wp (f x))
          == hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cmd_wp (Return x)) (fun x -> theta cmd_wp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_return x) (fun x -> theta cmd_wp (f x));
      `hist_ord` {} (** here there is an eta that forces us to use `hist_ord` **)
      theta cmd_wp (f x); 
      == {} // unfold io_bind
      theta cmd_wp (free_bind op s 'a 'b (Return x) f);
      == {}
      theta cmd_wp (free_bind op s 'a 'b m f);
    }
  | Call cmd arg k ->
    calc (hist_ord) {
      hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x)); 
      == {
        assert (hist_bind (theta cmd_wp (Call cmd arg k)) (fun x -> theta cmd_wp (f x))
           == hist_bind (theta cmd_wp m) (fun x -> theta cmd_wp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cmd_wp (Call cmd arg k)) (fun x -> theta cmd_wp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (cmd_wp cmd arg) (fun r -> theta cmd_wp (k r))) (fun x -> theta cmd_wp (f x));
      == { lemma_hist_bind_associativity (cmd_wp cmd arg) (fun r -> theta cmd_wp (k r)) (fun x -> theta cmd_wp (f x)) }
      hist_bind (cmd_wp cmd arg) (fun r -> hist_bind (theta cmd_wp (k r)) (fun x -> theta cmd_wp (f x)));
      `hist_ord` { (** if we get rid of the hist_ord from the other branch, this becomes an equality **)
        let rhs1 : s.res cmd arg -> hist 'b = fun r -> hist_bind (theta cmd_wp (k r)) (fun x -> theta cmd_wp (f x)) in
        let rhs2 : s.res cmd arg -> hist 'b = fun r -> theta cmd_wp (free_bind op s _ _ (k r) f) in
        introduce forall (r:s.res cmd arg). (rhs1 r) `hist_ord` (rhs2 r) with begin
          lemma_theta_is_lax_morphism_bind cmd_wp (k r) f
        end;
        another_lemma' #event #(s.res cmd arg) #'b (cmd_wp cmd arg) rhs1 rhs2;
        assert (hist_bind (cmd_wp cmd arg) rhs1 `hist_ord #_ #'b` hist_bind (cmd_wp cmd arg) rhs2) by (assumption ())
      }
      hist_bind (cmd_wp cmd arg) (fun r -> theta cmd_wp (free_bind op s _ _ (k r) f));
      == { _ by (compute ()) } // unfold theta
      theta cmd_wp (Call cmd arg (fun r -> free_bind op s _ _ (k r) f));
      `hist_ord` { _ by (compute ()) } // unfold iio_bind
      theta cmd_wp (free_bind op s _ _ (Call cmd arg k) f);
      == {}
      theta cmd_wp (free_bind op s _ _ m f);
    }

// The Dijkstra Monad
#set-options "--print_universes"
let dm (op:Type0) (s:op_sig op) (event:Type) (cmd_wp:op_wp op s event) (a:Type) (wp:hist #event a) =
  (m:(free op s a){wp `hist_ord` theta cmd_wp m})

let dm_return (op:Type) (s:op_sig op) (event:Type) (cmd_wp:op_wp op s event) (a : Type) (x : a) : dm op s event cmd_wp a (hist_return #a #event x) =
  free_return op s a x

let dm_bind
  (op:Type) (s:op_sig op) (event:Type) (cmd_wp:op_wp op s event)
  (a b : Type)
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : dm op s event cmd_wp a wp_v)
  (f : (x:a -> dm op s event cmd_wp b (wp_f x))) :
  Tot (dm op s event cmd_wp b (hist_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind cmd_wp v f;
  free_bind op s a b v f

let dm_subcomp (op:Type) (s:op_sig op) (event:Type) (cmd_wp:op_wp op s event) (a:Type) (wp1 wp2: hist a) (f : dm op s event cmd_wp a wp1) :
  Pure (dm op s event cmd_wp a wp2)
    (requires hist_ord wp2 wp1)
    (ensures fun _ -> True) =
  f

let dm_if_then_else (op:Type) (s:op_sig op) (event:Type) (cmd_wp:op_wp op s event) (a : Type) 
  (wp1 wp2: hist a) (f : dm op s event cmd_wp a wp1) (g : dm op s event cmd_wp a wp2) (b : bool) : Type =
  dm op s event cmd_wp a (hist_if_then_else wp1 wp2 b)
