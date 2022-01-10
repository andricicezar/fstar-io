module PartialDM

assume val wp : Type -> Type
assume val wret : #a:Type -> x:a -> wp a
assume val wbind : #a:Type -> #b:Type -> wp a -> (a -> wp b) -> wp b
assume val wle : #a:Type -> wp a -> wp a -> Type0

assume val dm : a:Type -> w:wp a -> Type
assume val ret : #a:Type -> x:a -> dm a (wret x)
assume val bind : #a:Type -> #b:Type -> w:wp a -> wf:(a -> wp b) -> m:dm a w -> f:(x:a -> dm b (wf x)) -> dm b (wbind w wf)
assume val subcomp : #a:Type -> w0:wp a -> w1:wp a -> dm a w0 -> Pure (dm a w1) (requires w0 `wle` w1) (ensures fun _ -> True)

assume val wconj : #a:Type -> wp a -> wp a -> wp a

assume val r_le_wconj : #a:Type -> w1:wp a -> w2:wp a -> Lemma (w2 `wle` wconj w1 w2)

assume val wlift : #a:Type -> pure_wp a -> wp a

let pdm a (pw : pure_wp a) (w : wp a) =
  squash (pw (fun _ -> True)) -> dm a (wconj (wlift pw) w)

let pret (a : Type) (x : a) : pdm a (pure_return a x) (wret x) =
  fun _ ->
    r_le_wconj (wlift (pure_return a x)) (wret x) ;
    subcomp (wret x) (wconj (wlift (pure_return a x)) (wret x)) (ret x)

let pbind (a b : Type) pw pwf w wf (m : pdm a pw w) (f : (x:a -> pdm b (pwf x) (wf x))) : pdm b (pure_bind_wp a b pw pwf) (wbind w wf) =
  fun _ ->
    assert (pure_bind_wp a b pw pwf (fun _ -> True)) ;
    assume (pw (fun _ -> True)) ;
    assume (forall x. pwf x (fun _ -> True)) ; // Only on returns of m but well...
    assume (wbind (wconj (wlift pw) w) (fun x -> wconj (wlift (pwf x)) (wf x)) `wle` wconj (wlift (pure_bind_wp a b pw pwf)) (wbind w wf)) ;
    subcomp _ _ (bind _ _ (m ()) (fun x -> f x ()))
