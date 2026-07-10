module DMFree

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics

open Free
include Hist

(** cmd_wp maps each command to a hist-based WP over events.
    - cmd: command type (parameterizes the free monad)
    - event: event type (parameterizes the hist monad) *)
let cmd_wp (cmd:Type -> Type) (event:Type) = #r:Type -> cmd r -> hist #event r

let cmd_wp_sum
  #cmd1 #cmd2
  (#event:Type)
  (cwp1:cmd_wp cmd1 event)
  (cwp2:cmd_wp cmd2 event)
  : cmd_wp (cmd_sum cmd1 cmd2) event =
  fun op ->
    match op with
    | CmdL op1 -> cwp1 op1
    | CmdR op2 -> cwp2 op2

(** WP for the empty command type (used for an unused channel):
    there is no command to give a WP to. *)
let empty_cmd_wp (#event:Type) : cmd_wp empty_cmds event =
  fun #r op -> allow_inversion (empty_cmds r); false_elim ()

(** Inspired from Kenji Maillard's thesis (2.4.5)
    NB: the separate val is needed for extraction: without it, the
    refinements of dm/gdm (where theta appears applied to the two extra
    hist arguments) trip the substitution bug of FStarLang/FStar#490. **)
val theta : #a:Type u#a -> #cmd1:(Type u#0 -> Type u#e) -> #cmd2:(Type u#f -> Type u#g) -> #event:Type ->
  cwp1:cmd_wp cmd1 event -> cwp2:cmd_wp cmd2 event -> m:free cmd1 cmd2 a -> hist #event a
let rec theta #a #cmd1 #cmd2 #event cwp1 cwp2 m =
  match m with
  | Return x -> hist_return x
  | Call1 op k ->
      hist_bind (cwp1 op) (fun ri -> theta cwp1 cwp2 (k ri))
  | Call2 op k ->
      hist_bind (cwp2 op) (fun ri -> theta cwp1 cwp2 (k ri))

let lemma_theta_is_monad_morphism_ret #cmd1 #cmd2 (#event:Type)
  (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) (v:'a) :
  Lemma (theta cwp1 cwp2 (free_return #cmd1 #cmd2 v) == hist_return v) by (compute ()) = ()

let another_lemma (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) p h :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x)) /\ hist_bind wp1 wp2 p h))
    (ensures (hist_bind wp1 wp3 p h)) = ()

let another_lemma' (wp1:hist 'a) (wp2:'a -> hist 'b) (wp3:'a -> hist 'b) :
  Lemma
    (requires ((forall x. (wp3 x) ⊑ (wp2 x))))
    (ensures (hist_bind wp1 wp3 ⊑ hist_bind wp1 wp2)) = ()

private let hist_ord wp1 wp2 = wp2 ⊑ wp1

let rec lemma_theta_is_lax_morphism_bind #a #b #cmd1 #cmd2 (#event:Type)
  (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  (m:free cmd1 cmd2 a) (f:a -> free cmd1 cmd2 b) :
  Lemma
    (theta cwp1 cwp2 (free_bind m f) ⊑ hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x))) =
  match m with
  | Return x ->
    calc (hist_ord) {
      hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x));
      == {
        assert (hist_bind (theta cwp1 cwp2 (Return x)) (fun x -> theta cwp1 cwp2 (f x))
          == hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp1 cwp2 (Return x)) (fun x -> theta cwp1 cwp2 (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_return x) (fun x -> theta cwp1 cwp2 (f x));
      `hist_ord` {} (** here there is an eta that forces us to use `hist_ord` **)
      theta cwp1 cwp2 (f x);
      == {} // unfold free_bind
      theta cwp1 cwp2 (free_bind (Return x) f);
      == {}
      theta cwp1 cwp2 (free_bind m f);
    }
  | Call1 op k ->
    calc (hist_ord) {
      hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x));
      == {
        assert (hist_bind (theta cwp1 cwp2 (Call1 op k)) (fun x -> theta cwp1 cwp2 (f x))
           == hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp1 cwp2 (Call1 op k)) (fun x -> theta cwp1 cwp2 (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (cwp1 op) (fun ri -> theta cwp1 cwp2 (k ri))) (fun x -> theta cwp1 cwp2 (f x));
      `hist_equiv` { lemma_hist_bind_associativity (cwp1 op) (fun ri -> theta cwp1 cwp2 (k ri)) (fun x -> theta cwp1 cwp2 (f x)) }
      hist_bind (cwp1 op) (fun ri -> hist_bind (theta cwp1 cwp2 (k ri)) (fun x -> theta cwp1 cwp2 (f x)));
      `hist_ord` {
        let rhs1 = fun ri -> hist_bind (theta cwp1 cwp2 (k ri)) (fun x -> theta cwp1 cwp2 (f x)) in
        let rhs2 = fun ri -> theta cwp1 cwp2 (free_bind (k ri) f) in
        introduce forall ri. (rhs1 ri) `hist_ord` (rhs2 ri) with begin
          lemma_theta_is_lax_morphism_bind cwp1 cwp2 (k ri) f
        end;
        another_lemma' (cwp1 op) rhs1 rhs2;
        assert (hist_bind (cwp1 op) rhs1 `hist_ord` hist_bind (cwp1 op) rhs2) by (assumption ())
      }
      hist_bind (cwp1 op) (fun ri -> theta cwp1 cwp2 (free_bind (k ri) f));
      == { _ by (compute ()) } // unfold theta
      theta cwp1 cwp2 (Call1 op (fun ri -> free_bind (k ri) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cwp1 cwp2 (free_bind (Call1 op k) f);
      == {}
      theta cwp1 cwp2 (free_bind m f);
    }
  | Call2 op k ->
    calc (hist_ord) {
      hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x));
      == {
        assert (hist_bind (theta cwp1 cwp2 (Call2 op k)) (fun x -> theta cwp1 cwp2 (f x))
           == hist_bind (theta cwp1 cwp2 m) (fun x -> theta cwp1 cwp2 (f x))) by (rewrite_eqs_from_context ())
      }
      hist_bind (theta cwp1 cwp2 (Call2 op k)) (fun x -> theta cwp1 cwp2 (f x));
      == { _ by (compute ()) } // unfold theta
      hist_bind (hist_bind (cwp2 op) (fun ri -> theta cwp1 cwp2 (k ri))) (fun x -> theta cwp1 cwp2 (f x));
      `hist_equiv` { lemma_hist_bind_associativity (cwp2 op) (fun ri -> theta cwp1 cwp2 (k ri)) (fun x -> theta cwp1 cwp2 (f x)) }
      hist_bind (cwp2 op) (fun ri -> hist_bind (theta cwp1 cwp2 (k ri)) (fun x -> theta cwp1 cwp2 (f x)));
      `hist_ord` {
        let rhs1 = fun ri -> hist_bind (theta cwp1 cwp2 (k ri)) (fun x -> theta cwp1 cwp2 (f x)) in
        let rhs2 = fun ri -> theta cwp1 cwp2 (free_bind (k ri) f) in
        introduce forall ri. (rhs1 ri) `hist_ord` (rhs2 ri) with begin
          lemma_theta_is_lax_morphism_bind cwp1 cwp2 (k ri) f
        end;
        another_lemma' (cwp2 op) rhs1 rhs2;
        assert (hist_bind (cwp2 op) rhs1 `hist_ord` hist_bind (cwp2 op) rhs2) by (assumption ())
      }
      hist_bind (cwp2 op) (fun ri -> theta cwp1 cwp2 (free_bind (k ri) f));
      == { _ by (compute ()) } // unfold theta
      theta cwp1 cwp2 (Call2 op (fun ri -> free_bind (k ri) f));
      `hist_ord` { _ by (compute ()) } // unfold free_bind
      theta cwp1 cwp2 (free_bind (Call2 op k) f);
      == {}
      theta cwp1 cwp2 (free_bind m f);
    }

// The Dijkstra Monad
type dm (cmd1:Type -> Type) (cmd2:Type -> Type) (event:Type)
  (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  (a:Type) (wp:hist #event a) =
  (m:(free cmd1 cmd2 a){theta cwp1 cwp2 m ⊑ wp})

let dm_return #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #a (x : a)
  : dm cmd1 cmd2 event cwp1 cwp2 a (hist_return #a #event x) =
  free_return x

let dm_cmd1 #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #r (op:cmd1 r) :
  dm cmd1 cmd2 event cwp1 cwp2 r (hist_bind (cwp1 op) (fun ri -> hist_return ri)) =
  Call1 op Return

let dm_cmd2 #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #r (op:cmd2 r) :
  dm cmd1 cmd2 event cwp1 cwp2 r (hist_bind (cwp2 op) (fun ri -> hist_return ri)) =
  Call2 op Return

#push-options "--z3rlimit 40"
let dm_bind
  #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event)
  #a #b
  (wp_v : hist #event a)
  (wp_f: a -> hist #event b)
  (v : dm cmd1 cmd2 event cwp1 cwp2 a wp_v)
  (f : (x:a -> dm cmd1 cmd2 event cwp1 cwp2 b (wp_f x))) :
  Tot (dm cmd1 cmd2 event cwp1 cwp2 b (hist_bind wp_v wp_f)) =
  lemma_theta_is_lax_morphism_bind cwp1 cwp2 v f;
  free_bind v f
#pop-options

let dm_subcomp #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #a
  (wp1 wp2: hist #event a) (f : dm cmd1 cmd2 event cwp1 cwp2 a wp1) :
  Pure (dm cmd1 cmd2 event cwp1 cwp2 a wp2)
    (requires wp1 ⊑ wp2)
    (ensures fun _ -> True) =
  f

let dm_if_then_else #cmd1 #cmd2 (#event:Type) (cwp1:cmd_wp cmd1 event) (cwp2:cmd_wp cmd2 event) #a
  (wp1 wp2: hist #event a)
  (f : dm cmd1 cmd2 event cwp1 cwp2 a wp1) (g : dm cmd1 cmd2 event cwp1 cwp2 a wp2) (b : bool) : Type =
  dm cmd1 cmd2 event cwp1 cwp2 a (hist_if_then_else wp1 wp2 b)
