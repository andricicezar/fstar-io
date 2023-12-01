module PSt

open FStar.Tactics

open PreCond
open StRel

let (⊑) = wst_leq

type pst (a:Type u#a) : Type u#(max 1 a) = precond (st a)

let ret_pst (x:'a) : pst 'a =
  ret_precond (ret_st x)

let bind_pst (pm:pst 'a) (pf:'a -> pst 'b) : pst 'b =
  bind_precond pm (fun m ->
    (** I suppose here v one needs an implication? **)
    (| (forall (x:'a). pre_of (pf x)), (fun _ -> bind_st m (fun x -> val_of (pf x))) |))

let req_pst (pre:pure_pre) : pst (squash pre) =
  bind_precond (req_precond pre) (fun x -> ret_precond (ret_st x))

let get_pst l : pst int =
  ret_precond (st_get l)

let put_pst l v : pst unit =
  ret_precond (st_put l v)

let theta_pst (pm:pst 'a) : wst 'a =
  (fun p s0 -> (theta_precond pm) (fun m -> theta_st m p s0))

let lemma_theta_morphism (m:pst 'a) (f:'a -> pst 'b) : Lemma (
  forall p s0. theta_pst (bind_pst m f) p s0 <==> bind_wst (theta_pst m) (fun x -> theta_pst (f x)) p s0
) =
  introduce forall p s0. (theta_pst (bind_pst m f) p s0 <==> bind_wst (theta_pst m) (fun x -> theta_pst (f x)) p s0)
with begin
     calc (<==>) {
       theta_pst (bind_pst m f) p s0;
       <==> {}
       theta_precond (bind_pst m f) (fun m -> theta_st m p s0);
       <==> { _ by (compute (); explode (); dump "H") }
 //      (theta_precond m) (fun m -> bind_wst (theta_st m) (fun x -> theta_pst (f x)) p s0);
//       <==> {}
       bind_wst (theta_pst m) (fun x -> theta_pst (f x)) p s0;
     }
  end

type pdm_st (a:Type) (wp:wst a) =
  pm:(pst a){theta_pst pm ⊑ wp}

let ret_pdm_st (a:Type) (x:a) : pdm_st a (ret_wst x) = 
  ret_precond (ret_st x)

let bind_pdm_st (a:Type) (b:Type)
            (wm:wst a) (wf:a -> wst b)
            (m:pdm_st a wm) (f:(x:a -> pdm_st b (wf x))) :
            pdm_st b (bind_wst wm wf) =
    lemma_theta_morphism m f;
    bind_pst m f

let w_req (p : Type0) : wst (squash p) =
  (fun post s0 -> p /\ post ((Squash.get_proof p),s0) )

let req_pdm_st (pre:pure_pre) : pdm_st (squash pre) (w_req pre) =
  req_pst pre
  
let get_pdm_st l : pdm_st int (get_wst l) =
  get_pst l
  
let put_pdm_st l v : pdm_st (unit) (put_wst l v) =
  put_pst l v

let subcomp_pdm_st (a:Type) (wp1 wp2:wst a) (m : pdm_st a wp1) : Pure (pdm_st a wp2) (requires (wp1 ⊑ wp2)) (ensures (fun _ -> True)) = m

let pdm_st_if_then_else (a : Type u#a) 
  (wp1 wp2: wst a) (f : pdm_st a wp1) (g : pdm_st a wp2) (b : bool) : Type =
  pdm_st a (wst_if_then_else wp1 wp2 b)

total
reifiable
reflectable
effect {
  StRelWp (a:Type) (wp : wst a)
  with {
       repr       = pdm_st
     ; return     = ret_pdm_st
     ; bind       = bind_pdm_st
     ; subcomp    = subcomp_pdm_st
     ; if_then_else = pdm_st_if_then_else
     }
}

unfold
let wlift #a (w : pure_wp a) : StRel.wst a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity w;
  fun p s0 -> w (fun r -> p (r,s0))
  
let lift_pure_pstrel (a : Type) 
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> Prims.PURE a w)) : 
  pdm_st a (wlift w) =
  let r = 
  bind_pdm_st _ _ _ _
    (req_pdm_st (as_requires w)) 
    (fun _ -> ret_pdm_st a (elim_pure #a #w f)) in
  lemma_wp_implies_as_requires w;
  subcomp_pdm_st _ _ _ r

sub_effect PURE ~> StRelWp = lift_pure_pstrel

effect StRel
  (a:Type)
  (pre : state -> Type0)
  (post : state -> a * state -> Type0) =
  StRelWp a (fun p s0 -> pre s0 /\ (forall r1. post s0 r1 ==> p r1)) 


let test_assert p : StRel unit (requires (fun _  -> p)) (ensures fun _ _  -> True) =
  assert p

let partial_match (l : list nat) : StRel unit (requires (fun _ -> l <> [])) (ensures fun _ _ -> True) =
  match l with
  | x :: r -> ()

assume val p : Type0
assume val p' : Type0
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : StRel unit (requires fun _  -> True) (ensures fun _ _  -> True)
assume val some_f' : unit -> StRel unit (requires fun _ -> p) (ensures fun _ _ -> p')

let pure_lemma_test () : StRel unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : StRel unit (requires fun _ -> True) (ensures fun _ _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
