module DMFree

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
include Hist

(** cmd_wp maps each command to a hist-based WP over events.
    - cmd: command type (parameterizes the free monad)
    - event: event type (parameterizes the hist monad) *)
let cmd_wp (cmd:Type -> Type) (event:Type) = caller -> #r:Type -> cmd r -> hist #event r

let cmd_wp_sum
  #cmd1 #cmd2
  (#event:Type)
  (cwp1:cmd_wp cmd1 event)
  (cwp2:cmd_wp cmd2 event)
  : cmd_wp (cmd_sum cmd1 cmd2) event =
  fun c op ->
    match op with
    | CmdL op1 -> cwp1 c op1
    | CmdR op2 -> cwp2 c op2

(** Inspired from Kenji Maillard's thesis (2.4.5) **)
let rec theta #a #cmd (#event:Type) (cwp:cmd_wp cmd event) (m:free cmd a) : Tot (hist #event a) (decreases m) =
  match m with
  | Return x -> hist_return x
  | Call c op k ->
      hist_bind (cwp c op) (fun ri -> theta cwp (k ri))

let lemma_theta_is_monad_morphism_ret #cmd (#event:Type) (cwp:cmd_wp cmd event) (v:'a) :
  Lemma (theta cwp (free_return #cmd v) == hist_return v) by (compute ()) = ()

let another_lemma (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) p h :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x)) /\ hist_bind wp1 wp2 p h))
    (ensures (hist_bind wp1 wp3 p h)) = ()

let another_lemma' (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x))))
    (ensures (hist_bind wp1 wp3 ⊑ hist_bind wp1 wp2)) = ()

private let hist_ord wp1 wp2 = wp2 ⊑ wp1

let rec lemma_theta_is_lax_morphism_bind #a #b #cmd (#event:Type) (cwp:cmd_wp cmd event) (m:free cmd a) (f:a -> free cmd b) :
  Lemma
    (theta cwp (free_bind m f) ⊑ hist_bind (theta cwp m) (fun x -> theta cwp (f x))) =
  match m with
  | Return x ->
    calc (hist_ord) {
      hist_bind (theta cwp m) (fun x -> theta cwp (f x));
      == {
        assert (hist_bind (theta cwp (Return x)) (fun x -> theta cwp (f x))
          == hist_bind (theta cwp m) (fun x -> theta cwp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp (Return x)) (fun x -> theta cwp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_return x) (fun x -> theta cwp (f x));
      `hist_ord` {} (** here there is an eta that forces us to use `hist_ord` **)
      theta cwp (f x);
      == {} // unfold free_bind
      theta cwp (free_bind (Return x) f);
      == {}
      theta cwp (free_bind m f);
    }
  | Call c op k ->
    calc (hist_ord) {
      hist_bind (theta cwp m) (fun x -> theta cwp (f x));
      == {
        assert (hist_bind (theta cwp (Call c op k)) (fun x -> theta cwp (f x))
           == hist_bind (theta cwp m) (fun x -> theta cwp (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp (Call c op k)) (fun x -> theta cwp (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (cwp c op) (fun ri -> theta cwp (k ri))) (fun x -> theta cwp (f x));
      `hist_equiv` { lemma_hist_bind_associativity (cwp c op) (fun ri -> theta cwp (k ri)) (fun x -> theta cwp (f x)) }
      hist_bind (cwp c op) (fun ri -> hist_bind (theta cwp (k ri)) (fun x -> theta cwp (f x)));
      `hist_ord` {
        let rhs1 = fun ri -> hist_bind (theta cwp (k ri)) (fun x -> theta cwp (f x)) in
        let rhs2 = fun ri -> theta cwp (free_bind (k ri) f) in
        introduce forall ri. (rhs1 ri) `hist_ord` (rhs2 ri) with begin
          lemma_theta_is_lax_morphism_bind cwp (k ri) f
        end;
        another_lemma' (cwp c op) rhs1 rhs2;
        assert (hist_bind (cwp c op) rhs1 `hist_ord` hist_bind (cwp c op) rhs2) by (assumption ())
      }
      hist_bind (cwp c op) (fun ri -> theta cwp (free_bind (k ri) f));
      == { _ by (compute ()) } // unfold theta
      theta cwp (Call c op (fun ri -> free_bind (k ri) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cwp (free_bind (Call c op k) f);
      == {}
      theta cwp (free_bind m f);
    }

// The Dijkstra Monad
type dm (cmd:Type0 -> Type) (event:Type) (cwp:cmd_wp cmd event) (a:Type) (wp:hist #event a) =
  (m:(free cmd a){theta cwp m ⊑ wp})

let dm_return #cmd (#event:Type) (cwp:cmd_wp cmd event) #a (x : a) : dm cmd event cwp a (hist_return #a #event x) =
  free_return x

let dm_cmd #cmd (#event:Type) (cwp:cmd_wp cmd event) (c:caller) #r (op:cmd r) :
  dm cmd event cwp r (hist_bind (cwp c op) (fun ri -> hist_return ri)) =
  Call c op Return

let dm_bind
  #cmd (#event:Type) (cwp:cmd_wp cmd event)
  #a #b
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : dm cmd event cwp a wp_v)
  (f : (x:a -> dm cmd event cwp b (wp_f x))) :
  Tot (dm cmd event cwp b (hist_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind cwp v f;
  free_bind v f

let dm_subcomp #cmd (#event:Type) (cwp:cmd_wp cmd event) #a (wp1 wp2: hist #event a) (f : dm cmd event cwp a wp1) :
  Pure (dm cmd event cwp a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  f

let dm_if_then_else #cmd (#event:Type) (cwp:cmd_wp cmd event) #a
  (wp1 wp2: hist #event a) (f : dm cmd event cwp a wp1) (g : dm cmd event cwp a wp2) (b : bool) : Type =
  dm cmd event cwp a (hist_if_then_else wp1 wp2 b)