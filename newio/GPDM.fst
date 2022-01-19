module GPDM

open FStar.Classical.Sugar
open FStar.List.Tot.Base
open FStar.Tactics


(** a tentative to generalize Partial Dijkstra Monads **)

(** A Dijkstra monad D A w is a monad-like structure that classifies effectful 
computations returning values in A and specified by w : W A. **)

(** In DM4ALL, it is shown that a computational monad M A, a specification monad W A, and a monad
morphism between the two (called theta), give rise to a Dijkstra Monad. **)

assume type m (a:Type)
assume val return_m : a:Type -> x:a -> m a

(** this is new and needed to define a Partial Dijkstra Monad **)
assume val return_of : #a:Type -> x:a -> m a -> Type0
assume val lemma_return_of_return_m : unit -> Lemma (forall a (x:a). x `return_of` return_m _ x)

assume val bind_m : a:Type -> b:Type -> l:(m a) -> k:((x:a{x `return_of` l}) -> m b) -> m b

assume val lemma_return_of_bind_m : 
  a:Type -> 
  b:Type ->
  l:m a ->
  lx:a{lx `return_of` l} -> 
  k:(x:a{x `return_of` l} -> m b) -> 
  Lemma (forall kx. kx `return_of` (k lx) ==> kx `return_of` (bind_m a b l k))

assume type w (a:Type)
assume val return_w : a:Type -> x:a -> w a
assume val bind_w : a:Type -> b:Type -> w a -> (a -> w b) -> w b

assume val ord_w : #a:Type -> wp1:w a -> wp2:w a -> Type0
assume val lemma_ord_w_id : #a:Type -> wp1:w a -> Lemma (wp1 `ord_w` wp1)
assume val lemma_ord_w_transitive : #a:Type -> wp1:w a -> wp2:w a -> wp3:w a -> Lemma (wp1 `ord_w` wp2 /\ wp2 `ord_w` wp3 ==> wp1 `ord_w #a` wp3)

assume val subcomp_w : #a:Type -> #p1:(a -> Type0) -> #p2:(a -> Type0) -> wp:w (x:a{p1 x}) -> 
  Pure (w (x:a{p2 x}))
    (requires (forall x. p1 x ==> p2 x))
    (ensures (fun _ -> True))

assume val lift_pure_pre_to_w : #a:Type -> pure_pre -> w a
assume val lemma_ord_w_lift_pure_pre_to_w : #a:Type -> (x:a) -> Lemma (return_w a x `ord_w` (lift_pure_pre_to_w True))
  
assume val theta : a:Type -> (l:m a) -> w (x:a{x `return_of` l})

assume val lemma_theta_is_monad_morphism_ret : #a:Type -> x:a ->
  Lemma (subcomp_w (theta a (return_m a x)) == return_w a x)

assume val lemma_theta_is_monad_morphism_bind :
  a:Type ->
  b:Type ->
  l:m a ->
  k:(x:a{x `return_of` l} -> m b) ->
  Lemma (theta b (bind_m a b l k) == bind_w (x:a{x `return_of` l}) (x:b{x `return_of` bind_m a b l k}) (theta a l) (fun x -> 
    lemma_return_of_bind_m a b l x k;
    subcomp_w (theta b (k x))))

let dm (a:Type) (wp:w a) = l:(m a){wp `ord_w` (subcomp_w (theta a l))}

let return_dm (a:Type) (x:a) : dm a (return_w a x) = 
  lemma_theta_is_monad_morphism_ret x;
  lemma_ord_w_id (return_w a x);
  return_m a x

#set-options "--print_implicits"

let getref #a #p (x : a { p x }) : Lemma (p x) = ()

(** monotonicity with some type magic (TODO: can we simplify this assumption? **)
val lemma_w_monotonic_bind_magic :
  #a:Type ->
  #b:Type -> 
  lwp:w a ->
  kwp:(a -> w b) ->
  l:dm a lwp ->
  k:(x:a{x `return_of` l} -> dm b (kwp x)) ->
  Lemma (
    bind_w a b lwp kwp `ord_w`
      subcomp_w (bind_w _ (x:b{x `return_of` (bind_m a b l k)}) (theta a l) (fun x -> lemma_return_of_bind_m a b l x k; subcomp_w (theta b (k x)))))
let lemma_w_monotonic_bind_magic #a #b lwp kwp l k =
  (** from the types of l and k **)
  assert (lwp `ord_w` (subcomp_w (theta a l)));
  introduce forall (x:a{x `return_of` l}). (kwp x `ord_w` (subcomp_w #b (theta b (k x)))) with begin
    getref #(m b) #(fun l -> (kwp x) `ord_w` (subcomp_w (theta b l))) (k x)
  end;

  (** this is the correct assumption we should ask for, close to monotonicity **)
  assume (bind_w a b lwp kwp `ord_w`
      bind_w _ b (theta a l) (fun x -> subcomp_w (theta b (k x))));

  (** but, we need this: **)
  assume (bind_w a b lwp kwp `ord_w`
      subcomp_w (bind_w _ (x:b{x `return_of` (bind_m a b l k)}) (theta a l) (fun x -> lemma_return_of_bind_m a b l x k; subcomp_w (theta b (k x)))))


val bind_dm :
  a:Type ->
  b:Type -> 
  lwp:w a ->
  kwp:(a -> w b) ->
  l:dm a lwp ->
  k:(x:a{x `return_of` l} -> dm b (kwp x)) ->
  dm b (bind_w _ _ lwp kwp)
let bind_dm a b lwp kwp l k =
  lemma_w_monotonic_bind_magic lwp kwp l k;

  lemma_theta_is_monad_morphism_bind a b l k;
  (** from the lemma: **)
  assert (bind_w _ _ (theta a l) (fun x -> lemma_return_of_bind_m a b l x k; subcomp_w (theta _ (k x))) == 
    theta b (bind_m a b l k));
  (** we rewrite x == y with subcomp_w x == subcomp_w y, not sure why it works, there is no injectiveness of subcomp required **)
  assert (subcomp_w #b #_ #(fun _ -> True) (bind_w _ (x:b{x `return_of` (bind_m a b l k)}) (theta a l) (fun x -> lemma_return_of_bind_m a b l x k; subcomp_w (theta _ (k x)))) == 
    subcomp_w #b #_ #(fun _ -> True) (theta b (bind_m a b l k)));
  (** We rewrite in bind of monotonicity, with the previous assert **)
  (** goal: **)
  assert (bind_w _ b lwp kwp `ord_w` (subcomp_w (theta b (bind_m a b l k))));
  bind_m a b l k

let subcomp_dm (a:Type) (wp1 wp2: w a) (f : dm a wp1) :
  Pure (dm a wp2)
    (requires wp2 `ord_w` wp1)
    (ensures fun _ -> True) =
  lemma_ord_w_transitive #a wp2 wp1 (subcomp_w (theta a f));
  f




(*** Work in progress: **)

let pdm (a:Type) (wp:w a) = 
  pre : pure_pre { wp `ord_w` (lift_pure_pre_to_w pre) } & (squash pre -> dm a wp)

let get_pre #a #wp (t : pdm a wp) : Pure pure_pre (requires True) (ensures fun r -> wp `ord_w` (lift_pure_pre_to_w r)) =
  let (| pre , f |) = t in pre

let get_fun #a #w (t : pdm a w) : Pure (dm a w) (requires get_pre t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let pdm_return (a:Type) (x:a) : pdm a (return_w a x) =
  lemma_ord_w_lift_pure_pre_to_w x;
  (** TODO: should the True be generalized? **)
  (| True, (fun _ -> return_dm a x) |)

let pdm_bind (a b:Type)
  (wp1:w a) (wp2:a -> w b)
  (f:pdm a wp1) 
  (g:(x:a) -> pdm b (wp2 x)) :
  pdm b (bind_w a b wp1 wp2) =
  assert (wp1 `ord_w` (lift_pure_pre_to_w (get_pre f)));
  assume (lift_pure_pre_to_w (get_pre f) ==> get_pre f);
  assert (wp1 `ord_w` subcomp_w (theta a (get_fun f)));
  assert (forall x. x `return_of` (get_fun f) ==> wp2 x `ord_w` theta b (get_fun (g x)));
  assume (bind_w a b wp1 wp2 `ord_w` (lift_pure_pre_to_w (get_pre f /\ (forall x. x `return_of` (get_fun f) ==> get_pre (g x)))));
  (| (get_pre f /\ (forall x. x `return_of` (get_fun f) ==> get_pre (g x))), 
     (fun _ -> 
       bind_dm a b wp1 wp2 (get_fun f) (fun x -> get_fun (g x))) 
   |)

let pdm_subcomp (a:Type) (wp1:hist a) (wp2:hist a) (f:pdm a wp1) :
  Pure (pdm a wp2)
    (requires (wp2 `hist_ord` wp1))
    (ensures fun _ -> True) =
  (| get_pre f, (fun _ -> dm_subcomp a wp1 wp2 (get_fun f)) |)

unfold
let pdm_if_then_else 
  (a : Type)
  (wp1: hist a)
  (wp2: hist a)
  (f : pdm a wp1)
  (g : pdm a wp2)
  (b : bool) : Type =
  pdm a (hist_if_then_else wp1 wp2 b)

total
reifiable
reflectable
effect {
  IOwp (a:Type) (wp : hist #event a) 
  with {
       repr       = pdm
     ; return     = pdm_return
     ; bind       = pdm_bind 
     ; subcomp    = pdm_subcomp
     ; if_then_else = pdm_if_then_else
     }
}

effect IO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> trace -> a -> Type0) =
  IOwp a 
    (fun (p:hist_post a) (h:trace) -> pre h /\ (forall lt r. post h lt r ==>  p lt r)) 

let lift_pure_pdm (a : Type) 
  (w : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a w)) : 
  pdm a (wp_lift_pure_hist w) =
  lemma_wp_lift_pure_hist_implies_as_requires #a #event w;
  (| as_requires w, (fun _ -> 
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    let r = f () in
    let r' = dm_return _ r in
    dm_subcomp _ _ _ r' ) |)

sub_effect PURE ~> IOwp = lift_pure_pdm
  
assume val p : prop
assume val p' : prop
assume val pure_lemma (_:unit) : Lemma p
assume val some_f (_:squash p) : IO unit (fun _ -> True) (fun _ _ _ -> True)
assume val some_f' : unit -> IO unit (requires (fun _ -> p)) (ensures fun _ _ _ -> p')

let test () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ()

let test'' () : IO unit (fun _ -> True) (fun _ _ _ -> True) =
  pure_lemma ();
  some_f ();
  some_f' ();
  assert p'

let static_cmd
  (cmd : io_cmds)
  (argz : io_args cmd) :
  IO (io_resm cmd)
    (requires (fun h -> io_pre cmd argz h))
    (ensures (fun h lt r ->
        lt == [convert_call_to_event cmd argz r])) =
  IOwp?.reflect (| True,  (fun _ -> io_call cmd argz) |)

let testStatic3 (fd:file_descr) : IO unit (fun h -> is_open fd h) (fun h lt r -> ~(is_open fd (List.rev lt @ h))) =
  let _ = static_cmd Close fd in
  ()


