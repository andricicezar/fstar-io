module ILang.CompileTo.TLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Hist
open IO.Sig

noeq
type free (a:Type u#a) : Type u#(max a 1) =
| Return : a -> free a

//let dm_free = DMFree.dm free_cmds free_sig event free_wps
//assume type free (a:Type)
assume val theta : #a:Type -> free a -> hist a
let dm_free (a:Type) (wp:hist a) =
  tree:(free a){wp `hist_ord` theta tree} 

assume val dm_free_return : (a:Type) -> (x:a) -> dm_free a (hist_return x)
assume val dm_free_bind  : 
  a: Type ->
  b: Type ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Prims.Tot (Hist.hist b)) ->
  v: dm_free a wp_v ->
  f: (x: a -> Prims.Tot (dm_free b (wp_f x))) ->
  Tot (dm_free b (hist_bind wp_v wp_f))
assume val dm_free_subcomp : 
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_free a wp1 ->
  Pure (dm_free a wp2) (hist_ord wp2 wp1) (fun _ -> True)

assume val lift_pure_dm_free :
  a: Type ->
  w: pure_wp a ->
  f: (_: eqtype_as_type unit -> Prims.PURE a w) ->
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
     ; subcomp    = dm_free_subcomp
     }
}

sub_effect PURE ~> FREEwp = lift_pure_dm_free

type resexn a = either a exn

type monitorable_prop = trace -> trace -> Tot bool
 
class compilable (t:Type) (pi:monitorable_prop) = {
  comp_type : Type;
  compile: t -> comp_type
}

instance compile_resexn (pi:monitorable_prop) (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  comp_type = resexn (d1.comp_type);
  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

effect FREEpi (a:Type) (pi : monitorable_prop) = 
  FREEwp a (fun p h -> (forall r lt. (pi h lt) ==> p lt r))
effect MFREE (a:Type) = 
  FREEwp a (fun p h -> forall lt r. p lt r)

let test_123
  (t1:Type)
  (t2:Type)
  pi
  {| d2:compilable t2 pi |} :
  (** resexn is also necessary for the PoC to work **)
  compilable (t1 -> FREEpi (resexn t2) pi) pi by (
  (** This is needed for it to be unsound, otherwise I get an error **)
  unfold_def (`hist_return)
) = {
  comp_type = t1 -> MFREE (resexn d2.comp_type);
  compile = (fun (f:(t1 -> FREEpi (resexn t2) pi)) (x:t1) ->
   let x : dm_free (resexn d2.comp_type) (hist_bind (fun p h -> forall r (lt: trace). pi h lt ==> p lt r)
      (fun r -> hist_return (compile #_ #pi #(compile_resexn pi t2 #d2) r))) =
     reify (compile #_ #pi #(compile_resexn pi t2 #d2) (f x)) in
   assert (False);
   FREEwp?.reflect x
  );
}
