module Abstr

// trying a simple interface for erased and proving that
// it cannot be inspected.

noeq
type erased_ix = {
  erased : Type0 -> Type0;
  hide : #t:_ -> t -> erased t;
}

open FStar.Classical
open FStar.Tactics
module T = FStar.Tactics
open Param

let int_param = param_of_eqtype int
let bool_param = param_of_eqtype bool

%splice[erased_ix_param; Mkerased_ix_param] (paramd (`%erased_ix))

%splice[__proj__Mkerased_ix__item__erased_param] (paramd (`%__proj__Mkerased_ix__item__erased))

let erased_ix_irrel : erased_ix = {
  erased = (fun _ -> unit);
  hide = (fun _ -> ());
}
let erased_ix_id : erased_ix = {
  erased = (fun t -> t);
  hide = (fun x -> x);
}

let rel : #ix0:erased_ix -> #ix1:erased_ix -> erased_ix_param ix0 ix1 -> ix0.erased int -> ix1.erased int -> Type0 =
  function Mkerased_ix_param e0 e1 eR _ _ _ -> eR int int (fun x y -> x == y)
  
let unit_param = param_of_eqtype unit

(* must be constant *)
type reveal_int = ix:erased_ix -> ix.erased int -> int

let reveal_int_param (r0 r1 : reveal_int) : Type u#1 =
  (ix0 : erased_ix) -> (ix1 : erased_ix) -> (ixR : erased_ix_param ix0 ix1) ->
  (e0 : ix0.erased int) -> (e1 : ix1.erased int) -> rel ixR e0 e1 ->
  int_param (r0 ix0 e0) (r1 ix1 e1)

// all interfaces are related
let related_any (ix0 ix1 : erased_ix) : erased_ix_param ix0 ix1 =
  Mkerased_ix_param ix0.erased ix1.erased (fun t0 t1 tR e0 e1 -> squash True)
                    ix0.hide   ix1.hide   (fun _ _ _ -> ())


// easy way
let thm (f : reveal_int) (f_param : reveal_int_param f f)
  : Lemma (forall ix ei. f ix ei == f erased_ix_irrel ())
  = let aux (ix0 ix1 : erased_ix) (e0 : ix0.erased int) (e1 : ix1.erased int) : Lemma (f ix0 e0 == f ix1 e1) =
      f_param ix0 ix1 (related_any ix0 ix1) e0 e1 ()
    in
    Classical.forall_intro_4 aux

let related_to_irrel (ix : erased_ix) : erased_ix_param ix erased_ix_irrel =
  Mkerased_ix_param ix.erased (fun _ -> unit) (fun t0 t1 tR e0 e1 -> squash True)
                    ix.hide (fun _ -> ()) (fun _ _ _ -> ())

let related_to_id (ix : erased_ix) : erased_ix_param ix erased_ix_id =
  Mkerased_ix_param ix.erased (fun t -> t) (fun t0 t1 tR e0 e1 -> squash True)
                    ix.hide (fun x -> x) (fun _ _ _ -> ())

  
let reveal_thm (f : reveal_int) (f_param : reveal_int_param f f)
  : Lemma (forall ix ei. f ix ei == f erased_ix_irrel ())
  = let aux (ix:erased_ix) (ei : ix.erased int) : Lemma (f ix ei == f erased_ix_irrel ()) =
      f_param ix erased_ix_irrel (related_to_irrel ix) ei () ()
    in
    Classical.forall_intro_2 aux
