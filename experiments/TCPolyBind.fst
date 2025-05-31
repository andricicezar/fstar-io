module Test

open FStar.Tactics.V2
open FStar.Tactics.Typeclasses


class pbind_tc (m1:Type u#a -> Type u#b) (m2:Type u#c -> Type u#d) (m_out:Type u#c ->Type u#e) = {
  poly_bind : (#a:Type u#a -> #b:Type u#c -> m1 a -> (a -> m2 b) -> m_out b);
}

class usable_pbind (m1:Type u#a -> Type u#b) (m2:Type u#c -> Type u#d) = {
  (let!) : (#a:Type u#a -> #b:Type u#c -> m1 a -> (a -> m2 b) -> m2 b);
}

(** Not helpful:
instance id_usable_bind m2 : usable_pbind id m2 = {
  (let!) = (fun #a #b (x:id a) (f:a -> m2 b) -> f x)
}**)

instance make_pbinds_usable m1 m2 {| pbind_tc m1 m2 m2 |} : usable_pbind m1 m2 = {
  (let!) = (fun #a #b (x:m1 a) (f:a -> m2 b) -> (poly_bind x f) <: m2 b)
}

class monad (m:Type -> Type) = {
   return : (#a:Type -> a -> m a);
   bind   : (#a:Type -> #b:Type -> (f:m a) -> (g:(a -> m b)) -> m b);
}

instance self_bind_is_pbind m {| monad m |} : pbind_tc m m m = {
  poly_bind = (fun v f -> bind v f)
}

class subcomp_tc (m1:Type -> Type) (m2:Type -> Type) = {
  subcomp : (#a:Type -> m1 a -> m2 a)
}

instance subcomp_pbind m1 m2 {| monad m2 |} {| subcomp_tc m1 m2 |} : pbind_tc m1 m2 m2 = {
  poly_bind = (fun v f -> bind (subcomp v) f)
}

instance subcomp_pbind' m1 m2 {| monad m2 |} {| subcomp_tc m1 m2 |} : pbind_tc m2 m1 m2 = {
  poly_bind = (fun v f -> bind v (fun x -> subcomp (f x)))
}

type st (a:Type u#a) = int -> a & int

instance monad_st : monad st = {
  return = (fun #a x s0 -> x, s0);
  bind = (fun #a #b (f:st a) (g:a -> st b) s0 -> let (r, s1) = f s0 in g r s1);
}

type id (a:Type u#a) = a
instance monad_id : monad id = {
  return = (fun #a x -> x);
  bind = (fun #a #b (f:id a) (g:a -> id b) -> g f);
}

instance subcomp_id_st : subcomp_tc id st = {
  subcomp = (fun #a (v:id a) -> return v)
}

let incr (x:int) : id int = x + 1

let get () : st int = fun s -> s, s
let put x : st unit = fun s -> (), s


let mytest () : st unit =
  let! x = get () in
  put (incr x)

let mytest2 () : st unit =
  let x = incr 5 in
  put x

let mytest3 () : st int =
  let! x = get () in
  return x

let untyped_mytest () =
  let! x = get () in
  put (incr x)

let mytest3' () : st int =
  let! x = get () in
  put (incr x) ;!
  let! y = get () in
  return y

let mytestbool () : st bool =
  let! x = get () in
  if! monad_id.return (x < 0) then return false
  else return true

let mytestboolmatch () : st bool =
  let! x = get () in
  match! monad_id.return x with
  | 0 -> return false
  | _ -> return true
