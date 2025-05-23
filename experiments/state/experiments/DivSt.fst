module DivSt

#set-options "--print_universes"

let point t = unit -> t
let dv_point t = unit -> Dv t

let cast (#t: Type u#a) (f: point t) : dv_point t = f
let cast_inj t : squash (Functions.is_inj (cast #t)) = ()

let to_type (#t: Type0) (x: t) : Type0 = y:t { y == x }
let to_type_inj t : squash (Functions.is_inj (to_type #t)) =
  introduce forall (x y: t). to_type x == to_type y ==> x == y with
  introduce _ ==> _ with _.
  let x: to_type x = x in
  let x: to_type y = coerce_eq () x in
  ()

let const #t (x: t) : point t = fun _ -> x
let const_inj t : squash (Functions.is_inj (const #t)) =
  introduce forall (x y: t). const x == const y ==> x == y with
  (assert const x () == x; assert const y () == y)

let f (t: Type u#a) : Type0 = to_type (cast (const t))
let f_inj () : squash (Functions.is_inj u#(1+a) u#1 (f u#a)) =
  to_type_inj (dv_point (Type u#a));
  cast_inj (point (Type u#a));
  const_inj (Type u#a)

let contradiction () : squash False =
  Cardinality.Universes.no_inj_universes_suc f;
  f_inj ()