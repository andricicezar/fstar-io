module Io_Async_Await

open FStar.Tactics
open FStar.List.Tot.Base
  
type event (e:Type0) =
| Ev : e -> event e
| EAwait : nat -> event e

type trace (e:Type0) = list (event e)

let rec interleave (t1:list 'e) (t2:list 'e) : list (list 'e) =
  match t1, t2 with
  | [], [] -> []
  | _, [] -> [t1]
  | [], _ -> [t2]
  | _, _ -> 
      (map (append [hd t1]) (interleave (tail t1) t2)) @
      (map (append [hd t2]) (interleave t1 (tail t2)))

let product (xs:list 'a) (ys:list 'b) : list ('a * 'b) =
  concatMap (fun x -> map (fun y -> (x, y)) ys) xs

let uncurry2 (f:'a -> 'b -> 'c) ((a,b):('a * 'b)) : 'c = f a b

let product_map (f:'a -> 'a -> list 'a) (l1:list 'a) (l2:list 'a) : list 'a =
  match l1, l2 with
  | [], [] -> []
  | [], l2 -> l2
  | l1, [] -> l1
  | _, _ -> concatMap (uncurry2 f) (product l1 l2)

val (===) : list 'a -> list 'a -> Type0
let (===) l1 l2 = forall e. e `memP` l1 <==> e `memP` l2

let filter_out_join (t:trace 'e) : trace 'e =
  filter (fun ev -> not (EAwait? ev)) t
  
let rec split_trace_join (t:trace 'e) acc : Tot ((trace 'e) * (trace 'e)) (decreases t) =
  match t with
  | [] -> (acc, [])
  | EAwait _ :: tl -> (acc, t)
  | ev :: tl -> split_trace_join tl (acc@[ev])

let interleave_traces (t1:trace 'e) (t2:trace 'e) : list (trace 'e) =
  let t1 = filter_out_join t1 in
  match t1, t2 with
  | [], [] -> []
  | _, [] -> [t1]
  | [], _ -> [t2]
  | _, _ -> 
      let (t2', t2'') = split_trace_join t2 [] in
      map (fun t -> t@t2'') (interleave t1 t2')

let reduce_interleave (l:list (list (trace 'e))) : list (trace 'e) = fold_left (product_map interleave_traces) [] l

type w_post #e (a:Type) = list (trace e) -> a -> Type0
type w_pre #e = list (trace e) -> Type0

type w0 #e (a:Type) = w_post #e a -> w_pre #e

unfold
let w_post_ord (#e:Type) (#a:Type) (p1 p2:w_post #e a) = forall lt (r:a). p1 lt r ==> p2 lt r

let w_monotonic (#e:Type) (#a:Type) (wp:w0 #e a) =
  forall (p1 p2:w_post a). (p1 `w_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

type w (#e:Type) (a:Type) = wp:(w0 #e a){w_monotonic wp}

unfold
let w_ord0 (#e:Type) (#a:Type) (wp1:w #e a) (wp2:w #e a) = forall (p:w_post a) h. wp1 p h ==> wp2 p h
let w_ord = w_ord0
unfold let (⊑) = w_ord

unfold
let w_return0 (#a:Type) (#e:Type) (x:a) : w #e a = 
  fun p h -> p [[]] x
let w_return = w_return0

unfold
let (@@) = fun l1 l2 -> (concatMap (fun t -> map (append t) l2) l1)

let (rev') = map rev

unfold
let w_post_shift (#e:Type) (p:w_post #e 'b) (lt:list (trace e)) : w_post #e 'b =
  fun lt' r' -> p (lt@@lt') r'

unfold
let w_post_bind
  (#e:Type)
  (#a:Type u#a) (#b:Type u#b)
  (h:list (trace e))
  (kw : a -> w #e b)
  (p:w_post #e b) :
  Tot (w_post #e a) =
  fun lt x ->
    kw x (w_post_shift p lt) (rev lt @@ h)


unfold
let w_bind0 (#e:Type) (#a:Type u#a) (#b:Type u#b) (wp : w #e a) (kwp : a -> w #e b) : w #e b =
  fun p h -> wp (w_post_bind h kwp p) h
let w_bind = w_bind0

open FStar.Ghost

noeq
type promise (#e:Type) (a:Type) = | Promise : r:erased a -> lt:erased (list (trace e)) -> promise #e a

noeq
type free (#e:Type) (a:Type u#a) : Type u#(max 1 a) =
| Require : (pre:pure_pre) -> k:((squash pre) -> free u#a #e a) -> free #e a
| Return : a -> free #e a
| Print : (arg:e) -> cont:(unit -> free u#a #e a) -> free #e a 
| Async : #c:Type u#0 -> free #e (Universe.raise_t c) -> k:(promise #e c -> free u#a #e a) -> free #e a
//| Await : #c:Type u#0 -> promise c -> k:(c -> free a) -> free a

let free_return (#e:Type) (#a:Type) (x:a) : free #e a =
  Return x

let rec free_bind
  (#e:Type)
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free #e a)
  (cont : a -> free #e b) :
  free #e b =
  match l with
  | Require pre k ->
      Require pre (fun _ -> free_bind (k ()) cont)
  | Return x -> cont x
  | Print str k -> 
      Print str (fun i -> free_bind (k i) cont)
  | Async f k ->
      Async 
        (free_bind f (fun x -> free_return (Universe.raise_val u#0 u#b (Universe.downgrade_val x))))
        (fun x -> free_bind (k x) cont)
//  | Await pr k ->
//      Await pr (fun x -> free_bind (k x) cont)

let w_require #e (pre:pure_pre) : w #e (squash pre) = 
  let wp' : w0 (squash pre) = fun p h -> pre /\ p [[]] () in
  assume (w_monotonic wp');
  wp'

unfold
let w_print #e (ev:e) : w #e unit =
  fun p _ -> p [[Ev ev]] ()

let rec prefixes (l:trace 'e) : list (trace 'e) =
  match l with
  | [] -> []
  | h :: tl -> [h] :: map (append [h]) (prefixes tl)

let app_prefix (id:nat) (ltf:list (trace 'e)) (hf:list (trace 'e)) : list (trace 'e) = 
  ((concatMap prefixes (map (fun t -> t @ [EAwait id]) ltf)) @@ hf)

val theta : (#e:Type) -> (#a:Type) -> free #e a -> w #e a
let rec theta m =
  match m with
  | Require pre k ->
      w_bind (w_require pre) (fun r -> theta (k r))
  | Return x -> w_return x
  | Print arg k ->
      w_bind (w_print arg) (fun r -> theta (k r))
  | Async f k -> let wp = (fun p hf ->
      (theta f) (fun ltf rf -> 
        theta (k (Promise (Universe.downgrade_val rf) ltf))
          (fun ltk rk -> p (reduce_interleave [ltf;ltk]) rk) (app_prefix 0 ltf hf)) hf) in
    assume (w_monotonic wp);
    wp
 // | Await pr k -> theta (k (Promise?.r pr))

let theta_monad_morphism_ret (v:'a) :
  Lemma (theta (free_return v) == w_return v) = ()

let theta_lax_monad_morphism_bind (#e:Type) (#a:Type) (#b:Type) (m:free a) (km:a -> free b) :
  Lemma (w_bind (theta #e m) (fun x -> theta #e (km x)) ⊑ theta #e (free_bind m km)) = admit ()

let dm (#e:Type) (a:Type u#a) (wp:w #e a) =
  m:(free a){wp ⊑ theta m}

let dm_return (a:Type u#a) (x:a) : dm a (w_return0 x) =
  Return x

let dm_bind
  (#e:Type)
  (a:Type u#a)
  (b:Type u#b)
  (wp:w #e a)
  (kwp:a -> w #e b)
  (c:dm a wp)
  (kc:(x:a -> dm b (kwp x))) :
  dm #e b (w_bind0 wp kwp) =
  theta_lax_monad_morphism_bind #e c kc;
  admit ();
  free_bind c kc

let dm_subcomp
  (#e:Type)
  (a:Type u#a)
  (wp1:w #e a)
  (wp2:w #e a)
  (c:dm a wp1) :
  Pure (dm a wp2)
    (requires (wp2 `w_ord0` wp1))
    (ensures (fun _ -> True)) =
    c 

let w_if_then_else (#e:Type) (#a:Type) (wp1 wp2:w #e a) (b:bool) : w #e a =
  fun p h -> (b ==> wp1 p h) /\ ((~b) ==> wp2 p h)

let dm_if_then_else (#e:Type) (a : Type u#a) 
  (wp1 wp2: w #e a) (f : dm a wp1) (g : dm a wp2) (b : bool) : Type =
  dm a (w_if_then_else wp1 wp2 b)

let dm_partial_return
  (#e:Type)
  (pre:pure_pre) : dm #e (squash pre) (w_require pre) =
  let m = Require pre (Return) in
  assert (w_require pre ⊑ theta #e m);
  m

unfold
let lift_pure_w (#e:Type0) (#a:Type u#a) (wp : pure_wp a) : w #e a =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  (fun (p:w_post a) _ -> wp (fun (r:a) -> p [[]] r))

let lift_pure_w_as_requires (#e:Type) (#a:Type) (wp : pure_wp a) :
  Lemma (forall (p:w_post #e a) h. lift_pure_w wp p h ==> as_requires wp) =
    assert (forall (p:w_post #e a) x. p [[]] x ==> True) ;
    FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    assert (forall (p:w_post #e a). wp (fun x -> p [[]] x) ==> wp (fun _ -> True))
  
unfold let repr' = dm #int
unfold let return' = dm_return #int
unfold let bind' = dm_bind #int
unfold let subcomp' = dm_subcomp #int
unfold let if_then_else' = dm_if_then_else #int


reflectable
reifiable
total
effect {
  CyWP (a:Type) (wp : w #int a)
  with {
       repr       = repr'
     ; return     = return' 
     ; bind       = bind'
     ; subcomp    = subcomp'
     ; if_then_else = if_then_else'
     }
}

let lift_pure_dm 
  (a : Type u#a) 
  (wp : pure_wp a)
  (f:(eqtype_as_type unit -> PURE a wp)) : 
  dm #int a (lift_pure_w wp) =
  lift_pure_w_as_requires #int #a wp;
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  let lhs = dm_partial_return (as_requires wp) in
  let rhs = (fun (pre:(squash (as_requires wp))) -> dm_return a (f ())) in
  let m = dm_bind _ _ _ _ lhs rhs in
  dm_subcomp a _ (lift_pure_w wp) m

sub_effect PURE ~> CyWP = lift_pure_dm

effect Cy
  (a:Type)
  (pre : list (trace int) -> Type0)
  (post : list (trace int) -> a -> list (trace int) -> Type0) =
  CyWP a (fun p h -> pre h /\ (forall lt r. post h r lt ==> p lt r))

(** *** Tests partiality of the effect **)
let test_using_assume (fd:int) : Cy int (requires (fun h -> True)) (ensures fun h r lt -> fd % 2 == 0) =
  assume (fd % 2 == 0) ;
  fd

// A second test to make sure exfalso isn't used
let test_assume #a #pre (f : unit -> Cy a (requires (fun _ -> pre)) (ensures fun _ _ _ -> True)) : Cy a (fun _ -> True) (fun _ _ _ -> True) =
  assume pre ;
  f ()

let test_assert p : Cy unit (requires (fun _ -> p)) (ensures fun _ _ _ -> True) =
  assert p

let partial_match (l : list nat) : Cy unit (requires (fun _ -> l <> [])) (ensures fun _ _ _ -> True) =
  match l with
  | x :: r -> ()

let partial_match_io (l : list int) : Cy int (requires fun _ -> l <> []) (ensures fun _ _ _ -> True) =
  match l with
  | s :: _ -> s + 10 

// Cezar's tests

assume val p : prop
assume val p' : prop
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True)
assume val some_f' : unit -> Cy unit (requires fun _ -> p) (ensures fun _ _ _ -> p')

// TODO: why is this failing?
let pure_lemma_test () : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : Cy unit (requires fun _ -> True) (ensures fun _ _ _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'
(** *** DONE with tests of partiality **)

let print (e:int) : Cy unit (fun _ -> True) (fun _ () lt -> lt == [[Ev e]]) =
  let f : free unit = Print e (Return) in
  assume ((fun p h -> p [[Ev e]] ()) `w_ord` theta f);
  let c : dm unit (fun p h -> p [[Ev e]] ()) = f in
  admit ();
  CyWP?.reflect c

let raise_w (wp:w 'a) : w (Universe.raise_t 'a) =
  let wp' = (fun p -> wp (fun lt r -> p lt (Universe.raise_val r))) in
  wp'

let async00 (#a:Type) (#wp:w a) ($f:unit -> CyWP a wp) : dm (Universe.raise_t a) (raise_w wp) = 
  let f' : dm a wp = reify (f ()) in
  admit ();
  dm_bind _ _ _ _ f' (fun x -> dm_return _ (Universe.raise_val x))

let async0 (#a:Type) (#pre:w_pre) (#post:list (trace int) -> a -> list (trace int) -> Type0) ($f:unit -> Cy a pre post) : dm (promise #int a) (fun p h -> pre h /\ (forall pr. post h (Promise?.r pr) (Promise?.lt pr) ==> p [[]] pr)) =
  let wp' : w (Universe.raise_t a) = raise_w (fun p h -> pre h /\ (forall lt r. post h r lt ==> p lt r)) in
  let f' : dm (Universe.raise_t a) wp' = async00 f in
  let m : free (promise a) = Async f' free_return in
  admit ();
  m

[@"opaque_to_smt"]
let async (#a:Type) (#pre:w_pre) (#post:list (trace int) -> a -> list (trace int) -> Type0) ($f:unit -> Cy a pre post) : Cy (promise a) pre (fun h pr lt -> lt == [[]] /\ post h (Promise?.r pr) (Promise?.lt pr)) =
  CyWP?.reflect (async0 f)

//[@"opaque_to_smt"]
//let await (#a:Type) (pr:promise a) : Cy a True (fun r -> reveal (Promise?.r pr) == r) =
//  CyWP?.reflect (Await pr (free_return))

let return (#a:Type) (x:a) () : Cy a (fun _ -> True) (fun h r lt -> r == x /\ lt == [[Ev 0]]) = print 0; x

let test () : Cy int (fun _ -> True) (fun h r lt -> r == 1 /\ lt == [[Ev 0; Ev 1]; [Ev 1; Ev 0]]) by (explode (); bump_nth 3; 
  rewrite_eqs_from_context (); dump "H") =
  let prx = async (return 2) in
 // let pry = async (return 3) in
  print 1;
  1
 // let x : int = await prx in
 // let y : int = await pry in
//  2 + 3



