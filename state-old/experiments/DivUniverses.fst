module DivUniverses

open FStar.Universe

#set-options "--print_universes"

type test_pure_arr (a:Type u#a) (b:Type u#b) : Type u#(max a b) =
  a -> b

type test_pure_123_arr (a:Type u#a) (b:Type u#b) : Type u#(max a b) =
  a -> Pure b (requires (5 > 2)) (ensures fun _ -> True)
  
type test_dv_arr (a:Type u#a) (b:Type u#b) : Type u#a =
  a -> Dv b

(* 
Looks like the representation of Div has to be constant in a universe (desirably 0),
so we're looking for

Dv : Type u#a -> Type u#0
*)

(* Not marking an effect with total, it defines the effect in universe 0,
   even if the representation is not. **)
   
(** Assume the monad transformer exists: **)

assume val m : Type u#a -> Type u#b
assume val m_return : #a:Type u#a -> a -> m u#a u#b a

assume val t : (m:Type u#a -> Type u#b) -> Type u#a -> Type u#0
assume val lift : #a:Type u#a -> m u#a u#b a -> t m a

type my_div (a:Type u#a) : Type u#0 = t (m u#a u#b) a

(** Checking if the existance of such a transformer is unsound (inspired by issue FStarLang/FStar#3659) **)

let point (t:Type u#a) : Type u#b = unit -> m t
let dv_point (t:Type u#a) : Type u#0 = unit -> my_div t

let cast (#t: Type u#a) (f: point u#a u#b t) : dv_point u#a t = fun () -> lift (f ())
let cast_inj (t:Type u#a) : squash (Functions.is_inj (cast u#a u#b #t)) =
  introduce forall f1 f2. cast #t f1 == cast #t f2 ==> f1 == f2 with
    introduce _ ==> _ with _. begin
      let f1' : dv_point t = (fun () -> lift (f1 ())) in
      let f2' : dv_point t = (fun () -> lift (f2 ())) in
      assert (f1' == f2');
      assume (f1' () == f2' ()); (* shouldn't this follow? *)
      assert (lift (f1 ()) == lift (f2 ())); 
      assume (Functions.is_inj (lift #t));
      assert (f1 () == f2 ()); (* function extensionality *)
      assume (f1 == f2)
    end

let to_type (#t: Type0) (x: t) : Type0 = y:t { y == x }
let to_type_inj (t:Type0) : squash (Functions.is_inj (to_type #t)) =
  introduce forall (x y: t). to_type x == to_type y ==> x == y with
    introduce _ ==> _ with _.
      let x: to_type x = x in
      let x: to_type y = coerce_eq () x in
      ()

let const (#t:Type u#a) (x: t) : point u#a u#b t = fun _ -> m_return u#a u#b x

let const_inj (t:Type u#a) : squash (Functions.is_inj u#a u#b (const u#a u#b #t)) =
  introduce forall (x y: t). const x == const y ==> x == y with begin
    assume (Functions.is_inj (m_return #t));
    assert const x () == m_return x;
    assert const y () == m_return y
  end

let f (t: Type u#a) : Type0 =
  to_type (cast u#(a+1) u#b (const u#(a+1) u#b t))

let f_inj () : squash (Functions.is_inj (f u#a u#b)) =
  introduce forall (x1 x2:Type u#a). f x1 == f x2 ==> x1 == x2 with begin
    introduce _ ==> _ with _. begin
      calc (==>) {
        f x1 == f x2;
        ==> {  }
        to_type (cast (const x1)) == to_type (cast (const x2));
        ==> { let _ = to_type_inj (dv_point (Type u#a)) in () }
        cast (const x1) == cast (const x2);
        ==> { let _ = cast_inj (point (Type u#a)) in admit () (* NO IDEA WHY THIS DOESN'T WORK *) }
        const x1 == const x2;
        ==> { let _ = const_inj (Type u#a) in () }
        x1 == x2;
      }
    end
  end

let contradiction () : squash False =
  Cardinality.Universes.no_inj_universes_suc f;
  f_inj ()