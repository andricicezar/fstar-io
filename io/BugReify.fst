module BugReify 


open FStar.List.Tot
open FStar.Tactics.Typeclasses

(** Working on F* release: 2022.05.06 **)

type free (a:Type u#a) : Type u#(max a 1) =
| Return : a -> free a

(** 
If I assume free, the PoC does not work 
assume type free (a:Type u#a) : Type u#(max a 1) **)

(** *** Spec **)
(** monotonicity seems relevant **)
let hist a = wp:(pure_wp' a){pure_wp_monotonic0 a wp}

unfold
val hist_ord (#a : Type) : hist a -> hist a -> Type0
let hist_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

unfold
let hist_return (x:'a) : hist 'a =
  fun p -> p x

unfold
let hist_bind (#a #b:Type) (w : hist a) (kw : a -> hist b) : hist b =
  fun p -> w (fun r -> kw r p)

unfold
let wp_lift_pure_hist (w : pure_wp 'a) : hist 'a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  w

(** *** Dijkstra Monad **)
assume val theta : #a:Type -> free a -> hist a

let dm_free (a:Type) (wp:hist a) =
  tree:(free a){wp `hist_ord` theta tree} 

assume val dm_free_return : (a:Type) -> (x:a) -> dm_free a (hist_return x)
assume val dm_free_bind  : 
  a: Type ->
  b: Type ->
  wp_v: hist a ->
  wp_f: (_: a -> Tot (hist b)) ->
  v: dm_free a wp_v ->
  f: (x: a -> Tot (dm_free b (wp_f x))) ->
  Tot (dm_free b (hist_bind wp_v wp_f))

(** necessary **)
assume val lift_pure_dm_free :
  a: Type ->
  w: pure_wp a ->
  f: (_: eqtype_as_type unit -> PURE a w) ->
  Tot (dm_free a (wp_lift_pure_hist w))

total
reifiable
reflectable
effect {
  FREEwp (a:Type) (wp : hist a) 
  with {
       repr       = dm_free
     ; return     = dm_free_return
     ; bind       = dm_free_bind 
     }
}

sub_effect PURE ~> FREEwp = lift_pure_dm_free

class compilable (t:Type) = {
  comp_type : Type;
  compile: t -> comp_type
}

instance compile_option (t:Type) {| d1:compilable t |} : compilable (option t) = {
  comp_type = option (d1.comp_type);
  compile = (fun x ->
    match x with
    | Some r -> Some (compile r)
    | None -> None)
}

let test_assert_false
  (t1:Type)
  (t2:Type)
  {| d2:compilable t2 |} 
  (f:(t1 -> FREEwp (option t2) (fun p -> (forall r. p r)))) 
  (x:t1) : 
  Lemma False =
  let _ : dm_free (option d2.comp_type) (hist_bind (fun p -> forall r . p r)
                                                   (fun (r:option t2) -> hist_return (compile #_ #(compile_option t2 #d2) r))) =
       reify (compile #_ #(compile_option t2 #d2) (f x)) in
  assert (False)

(** tried to remove the reify to see if the PoC works, but this fails as expected **)
let other_tests 
  (t1:Type)
  (t2:Type)
  {| d2:compilable t2 |} 
  (f:(t1 -> FREEwp (option t2) (fun p -> (forall r. p r)))) : 
  Lemma False =
  let _ : t1 -> FREEwp (option d2.comp_type) (hist_bind (fun p -> forall r. p r)
                                                   (fun (r:option t2) -> hist_return (compile #(option t2) #(compile_option t2 #d2) r))) =
       fun x -> (compile #(option t2) #(compile_option t2 #d2) (f x)) in
  assert (False)
