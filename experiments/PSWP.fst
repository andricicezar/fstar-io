module PSWP

open FStar.Tactics
open FStar.Universe
open FStar.ST
open FStar.Heap

type idx =
 | P
 | S

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

// GM: Warning: the [unfold]s here are important.

unfold
let p_monotonic #a (wp : pure_wp a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

let p_wp (a:Type) = w:(pure_wp a){p_monotonic w}

unfold
let s_monotonic #a (wp : gst_wp a) =
  forall p1 p2. (forall x s. p1 x s ==> p2 x s) ==> (forall s. wp p1 s ==> wp p2 s)

let s_wp (a:Type) = w:(gst_wp a){s_monotonic w}

let wp (i:idx) : Type -> Type =
  match i with
  | P -> p_wp
  | S -> s_wp

let m (a:Type u#aa) (i:idx) (w : wp i a) : Type u#aa =
  match i with
  | P -> unit -> PURE a w
  | S -> raise_t (unit -> STATE a w)

  (* in reality we need something more like this: *)
  (* free (match i with *)
  (*       | I -> io_sig *)
  (*       | S -> state_sig *)
  (*       | IS -> io_sig `:+:` state_sig) *)
  (* could also be done by carving out of a big signature with refinements *)

let p_return_wp #a (x:a) : wp P a = fun p -> p x
let s_return_wp #a (x:a) : wp S a = fun p -> p x

let return_wp #a (i:idx) : a -> wp i a =
  match i with
  | P -> p_return_wp
  | S -> s_return_wp

let p_return #a (x:a) : m a P (p_return_wp x) = (fun () -> x)
let s_return #a (x:a) : m a S (s_return_wp x) = raise_val (fun () -> x)

let return (a:Type) (x:a) (i:idx) : m a i (return_wp i x) =
  match i with
  | P -> p_return x
  | S -> coerce (s_return x)

unfold
let p_bind_wp #a #b (wc : p_wp a) (wf : a -> p_wp b) : p_wp b =
  fun p -> wc (fun x -> wf x p)

// these two rely on monotonicity since the computed WP is not exactly bind_wp
let p_bind #a #b (#wc : p_wp a) (#wf : a -> p_wp b)
           (c : m a P wc) (f : (x:a -> m b P (wf x))) : m b P (p_bind_wp wc wf) =
  fun () -> f (c ()) ()

unfold
let s_bind_wp #a #b (wc : s_wp a) (wf : a -> s_wp b) : s_wp b =
  fun p -> wc (fun x -> wf x p)

let s_bind #a #b #wc #wf (c : m a S wc) (f : (x:a -> m b S (wf x)))
  : m b S (s_bind_wp wc wf) =
  raise_val (fun () -> let y = downgrade_val c () in // cannot inline this
                    downgrade_val (f y) ())

let bind_wp #a #b (i:idx) : wp i a -> (a -> wp i b) -> wp i b =
  match i with
  | P -> p_bind_wp #a #b
  | S -> s_bind_wp #a #b

let join (i j : idx) : idx =
  match i, j with
  | S, _
  | _, S -> S
  | P, P -> P

let lower (i j : idx) : bool = i `join` j = j

let join_is_P (i j : idx) : Lemma (requires (join i j = P))
                                  (ensures (i = P && j = P)) = ()

let lift_wp #a (i : idx) (j : idx{i `lower` j}) (w : wp i a) : wp j a =
  match i, j with
  | P, S -> 
      let w' : pure_wp a = w in
      (fun p h0 -> w' (fun x -> p x h0)) <: gst_wp a
  | _, _ -> w

let lift_wp_id #a i (w : wp i a) : Lemma (lift_wp i i w == w) = ()

let lift_fwp_id #a #b i (wf : a -> wp i b) :
  Lemma ((fun x -> lift_wp i i (wf x)) == wf) = admit()
  (* this probably requires functional extensionality
     and might need some massaging *)

let lift #a (i : idx) (j : idx{i `lower` j}) #w (c: m a i w)
  : m a j (lift_wp i j w) = admit()

let bind (a b : Type) (i j:idx) (wc:wp i a) (wf:a->wp j b)
  (c : m a i wc) (f : (x:a -> m b j (wf x)))
  : m b (join i j) (bind_wp (join i j) (lift_wp i (join i j) wc)
                            (fun x -> lift_wp j (join i j) (wf x))) =
  match join i j with
  | P -> join_is_P i j; lift_wp_id #a P wc; lift_fwp_id #a #b P wf;
         p_bind #a #b #wc #wf c (fun x -> f x)
  | S -> coerce (s_bind #a #b #(lift_wp i (join i j) wc)
                        #(fun p -> lift_wp j (join i j) (wf p))
                        (coerce (lift #a i (join i j) c))
                        (fun x -> coerce (lift #b j (join i j) (f x))))
