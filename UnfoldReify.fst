module UnfoldReify

open FStar.List.Tot
open FStar.Tactics
open FStar.Calc

open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics

// m is a monad. In this particular example, lists
val m (a : Type u#a) : Type u#a
let m a = list a

val m_return (#a : Type) : a -> m a
let m_return x = [x]

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind l f = concatMap f l

// w is an ordered (w_ord) monad with conjunction (w_conj) and actions from prop (w_act_prop)
// In this example, good ol' continuations into prop
val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = w:(w0 a)//{monotonic w}

val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

unfold
val w_return (#a : Type) : a -> w a
unfold
let w_return x = fun p -> p x

unfold
val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
unfold
let w_bind wp1 k =
  fun p -> wp1 (fun x -> k x p)

val interp (#a : Type) : m a -> w a
let interp #a (l:list a) = fun p -> forall x. memP x l ==> p x

val concatlemma (#a:Type) (l1 l2 :list a) (x:a) : Lemma (memP x (l1@l2) <==> memP x l1 \/ memP x l2)
let rec concatlemma #a l1 l2 x =
  match l1 with
  | [] -> ()
  | h::t -> concatlemma t l2 x

val concatmaplemma : (#a:Type) -> (#b:Type) -> l:list a -> (f:(a -> list b)) -> x:b ->
                               Lemma (memP x (concatMap f l) <==> (exists a. memP a l /\ memP x (f a)))
                                     [SMTPat (memP x (concatMap f l))]

let rec concatmaplemma #a #b l f x =
  match l with
  | [] -> ()
  | h::t ->
    concatlemma (f h) (concatMap f t) x;
    concatmaplemma t f x

let dm (a : Type) (wp : w a) : Type = 
  p:(a -> Type0) -> squash (wp p) -> l:(m a){forall x. memP x l ==> p x}
  
let irepr (a : Type) (wp: w a) = dm a wp

let ireturn (a : Type) (x : a) : irepr a (w_return x) = fun _ _ -> [x]

let rec pmap #a #b #pre (#post:b->Type0)
  (f : (x:a -> Pure b (requires (pre x)) (ensures post)))
  (l : list a)
  : Pure (list (v:b{post v}))
         (requires (forall x. memP x l ==> pre x))
         (ensures (fun _ -> True))
  = match l with
    | [] -> []
    | x::xs -> f x :: pmap #_ #_ #pre #post f xs

let rec unref #a #p (l : list (v:a{p v})) : l:(list a){forall x. memP x l ==> p x} =
  match l with
  | [] -> []
  | x :: xs -> x :: unref xs

let mem_memP
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma (ensures (mem x l <==> memP x l))
        [SMTPat (memP x l); SMTPat (mem x l)]
= FStar.List.Tot.Properties.mem_memP x l

val append_memP: #t:Type ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (memP a (l1@l2) <==> (memP a l1 \/ memP a l2)))
let rec append_memP #t l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_memP tl l2 a

let rec flatten_mem_lem #a (l : list (list a)) (x:a)
  : Lemma (memP x (flatten l) <==> (exists l0. memP l0 l /\ memP x l0))
          [SMTPat (memP x (flatten l))]
  = match l with
    | [] -> ()
    | l1::ls -> (append_memP l1 (flatten ls) x; flatten_mem_lem ls x)

let ibind (a : Type) (b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x))) : irepr b (w_bind wp_v wp_f) =
  fun p _ -> let l1 = v (fun x -> wp_f x p) () in
          let l2 = pmap #_ #(list b) #(fun x -> wp_f x p) #(fun l -> forall x. memP x l ==> p x) (fun x -> f x p ()) l1 in
          let l2 = unref l2 in
          let l2f = List.Tot.flatten l2 in
          l2f
 
let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) : Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a=
  fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p)

let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
  irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  ND : a:Type -> wp : w a -> Effect
  with repr         = irepr;
       return       = ireturn;
       bind         = ibind;
       subcomp      = isubcomp; 
       if_then_else = i_if_then_else
}

let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
 //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
 // ^ basically this, requires monotonicity
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f ()

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a wp) (requires True)
                    (ensures (fun _ -> True))
  = fun p _ -> let r = Common.elim_pure f p in [r]

sub_effect PURE ~> ND = lift_pure_nd


opaque
let g (x:int) : option int = Some x

let wrap (f:int -> ND unit (fun p -> True)) (x':int) : ND unit (fun p -> True) =
  match g x' with
  | Some x -> f x
  | None -> f 4


let rewrite_inside_reify
  (f : int -> ND unit (fun p -> True))
  (g : int -> Tot (option int))
  (x' : int) : Tot unit = 

  let f' = wrap f in 
  let l = reify (f' x') (fun (p:unit) -> True) in

  match g x' with
  | Some x -> 
     let ll = reify (f x) (fun (p:unit) -> True) in
     assert (l == ll) by (
       unfold_def (`wrap);
       // This puts in rwr: g x' == Some b
       let rwr = (match (List.Tot.nth (cur_binders ()) 11) with
       | Some y -> y | None -> fail "asdf") in
       l_to_r [`rwr];
       dump "H")
     // The assert ^ fails with the error:
     // "(Error) user tactic failed: Ill-typed reify: this constant must be fully applied"
  | None -> ()


  

  


let reify_bind
  #a #b
  (wp_v : w a) 
  (wp_f: a -> w b) 
  (v : irepr a wp_v)
  (f : (x:a -> irepr b (wp_f x))) : Tot unit =

  let k : irepr b (w_bind wp_v wp_f) =
    ibind a b wp_v wp_f (reify (ND?.reflect v)) (fun x -> reify (ND?.reflect (f x))) in

  let k' : irepr b (w_bind wp_v wp_f) =
    reify (
      let (res : a) = ND?.reflect v in
      ND?.reflect (f res)) in

  assert (forall p. k p  == k' p) by (dump "H")
