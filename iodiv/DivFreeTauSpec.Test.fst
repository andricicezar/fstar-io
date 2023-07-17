module DivFreeTauSpec.Test

open FStar.Tactics
open FStar.List.Tot

open DivFreeTauSpec
open IIOSig
open IIOSigSpec

(** 
let dm sg (w_act : action_iwp sg) (a : Type) (w : iwp a) =
  c : m sg a { theta w_act c `ile` w }

**)

let triv #a : iwp a =
  iprepost (fun _ -> True) (fun h r -> True) 

let r_div : iwp unit =
  iprepost (fun _ -> True) (fun h r -> diverges r)

let r_cv : iwp unit =
  iprepost (fun _ -> True) (fun h r -> terminates r)

(** *** Append assert false to divergent code **)

let assert_false : iwp unit =
  iprepost (fun _ -> False) (fun h r -> True)

let _ = assert (i_bind r_div (fun _ -> assert_false) `ile` r_div)
(** This is not surprising taking in consideration the definition of `i_bind`.
   If we unfold it, we obtain something similar to:
   (fun post hist ->
      w (fun r ->
        match r with
        | Cv tr x -> wf x (ishift_post tr post) (rev_acc (to_trace tr) hist)
        | Dv st -> post (Dv st)
        ) hist)

   and here one can see that `wf` (which is `(fun _ -> testfalse)` in our case)
   is not used in the `Dv` branch.

   TODO: is this a problem?
**)


[@expect_failure] (** fails goal 2 that requires to prove False **)
let _ = assert (i_bind r_cv (fun _ -> assert_false) `ile` r_cv) by (norm [delta_only [`%r_cv;`%iprepost]]; explode ();dump "H")


(** *** Actions **)

let _ = assert (i_open "test.txt" `ile` triv)
let _ = assert (i_bind (i_open "test.txt") (fun _ -> i_ret ()) `ile` triv)
let _ = assert (i_bind (i_open "test.txt") (fun _ -> i_ret ()) `ile` r_cv)
  
[@expect_failure]
let _ = assert (i_bind (i_open "test.txt") (fun _ -> i_ret ()) `ile` r_div) by (norm [delta_only [`%r_div;`%iprepost;`%i_ret;`%ishift_post;`%as_iwp;`%ishift_post;`%ret_fin_trace];zeta]; explode (); bump_nth 2; compute ();explode (); dump "H")

(** *** Iter **)
let lift_body (w:iwp 'a) (#index:Type0) : index -> iwp (either index unit) =
  (fun i -> i_bind w (fun _ -> i_ret (Inl i)))

assume val pre0 : trace -> Type0
assume val inv0 : trace -> Type0
assume val pre0_inv0 : unit -> Lemma (forall h lt. pre0 h /\ inv0 lt ==> pre0 (rev_acc lt h))

let body0 : iwp unit = iprepost pre0 (fun h r -> terminates r /\ inv0 (ret_trace r))
let loop0 = iprepost pre0 (fun h r -> diverges r /\ repeat_inv_post inv0 r)

let body0' : iwp unit =
  iprepost pre0 (fun hist r -> terminates r /\ pre0 (rev_acc (ret_trace r) hist) /\ inv0 (ret_trace r))

let _ =
  pre0_inv0 ();
  let body' = lift_body body0 in
  let body_inv = repeat_body_inv #unit (fun _ -> pre0) inv0 in
  assert (body' () `ile` body_inv ());
  i_iter_mono #unit body' body_inv ();
  assert ((i_iter body' ()) `ile` (i_iter body_inv ()));
  repeat_inv_proof (fun _ -> pre0) inv0 () ;
  assert (i_iter body_inv () `ile` repeat_inv (fun _ -> pre0) inv0 ());
  assert (repeat_inv (fun _ -> pre0) inv0 () `ile` loop0);
  assert (i_iter body' () `ile` loop0)

let pre1 (fd:file_descr) : trace -> Type0 = fun h -> is_open fd h
let inv1 (fd:file_descr) : trace -> Type0 = fun tr -> exists s. tr == [ERead fd s]
val pre1_inv1 : (fd:file_descr) -> squash (forall h lt. pre1 fd h /\ inv1 fd lt ==> pre1 fd (rev_acc lt h))
let pre1_inv1 fd = ()

let ibody1 (fd:file_descr) : iwp string = iprepost (pre1 fd) (fun h r -> terminates r /\ inv1 fd (ret_trace r))
let iloop1 (fd:file_descr) : iwp unit = iprepost (pre1 fd) (fun h r -> diverges r /\ repeat_inv_post (inv1 fd) r)

let itest1 (fd:file_descr) : Lemma (i_iter (lift_body (ibody1 fd)) () `ile` (iloop1 fd)) =
  pre1_inv1 fd;
  let body' = lift_body (ibody1 fd) in
  let body_inv = repeat_body_inv (fun _ -> pre1 fd) (inv1 fd) in
  assert (body' () `ile` body_inv ());
  i_iter_mono #unit body' body_inv ();
  assert ((i_iter body' ()) `ile` (i_iter body_inv ()));
  repeat_inv_proof (fun _ -> (pre1 fd)) (inv1 fd) () ;
  assert (i_iter body_inv () `ile` repeat_inv (fun _ -> (pre1 fd)) (inv1 fd) ());
  assert (repeat_inv (fun _ -> (pre1 fd)) (inv1 fd) () `ile` (iloop1 fd));
  assert (i_iter body' () `ile` (iloop1 fd))
