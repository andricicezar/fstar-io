module GhostRefParam

open FStar.Ghost
open FStar.Classical
open FStar.Tactics
module T = FStar.Tactics
open Param

// proving that this func must be the identity..
let ty = (b : erased bool) -> x:int -> y:int{if b then y==x else True}

let int_param = param_of_eqtype int
let bool_param = param_of_eqtype bool

// ..assuming that this is the parametricity principle for erased (i.e. universal relation)
let erased_param (t1 t2 : Type) (tR : t1 -> t2 -> Type0) (e1 : erased t1) (e2 : erased t2) = squash True

%splice[ty_param] (paramd (`%ty))

let thm
  (f : ty)
  (f_param : ty_param f f)
: Lemma (forall b x. f b x == x)
=
  let aux (b:erased bool) (x:int) : Lemma (f b x == x) =
    f_param false true () x x ()
  in
  Classical.forall_intro_2 aux

(* sketch for disallowing constructors *)
noeq
type free (a:Type) =
  | Ret of a
  | A1 : int -> (bool -> free a) -> free a
  | A2 : int -> (int -> free a) -> free a

let rec noa1 (t : free 'a) : Type0 =
  match t with
  | Ret _ -> True
  | A1 _ _ -> False
  | A2 i k -> forall o. noa1 (k o)

// fixme: type0 or plugin fails
type tt (a:Type0) = (b : erased bool) -> t:(free a){not b ==> noa1 t}

%splice[free_param; A2_param] (paramd (`%free))

%splice[tt_param] (paramd (`%tt))

let rec free_param_noa1
  (a1 a2 : Type0) (aR : a1 -> a2 -> Type)
  (t1 : free a1) (t2 : free a2)
  (tR : free_param a1 a2 aR t1 t2)
  : Lemma (requires noa1 t1) (ensures noa1 t2)
=
  match tR with
  | A2_param _ _ _ kk1 kk2 kkr ->
    let aux2 (o:int) : Lemma (noa1 (kk2 o)) =
      assert (noa1 (kk1 o));
      free_param_noa1 a1 a2 aR (kk1 o) (kk2 o) (kkr o o ())
    in
    Classical.forall_intro aux2
  
  | _ -> ()

let thm1 (t : tt int) : Lemma (noa1 (t false)) =
  ()
  
let thm2 (t : tt int) (ft : tt_param int int int_param t t) : Lemma (noa1 (t true)) =
  assert (noa1 (t false));
  free_param_noa1 int int int_param (t false) (t true) (ft false true ());
  ()
