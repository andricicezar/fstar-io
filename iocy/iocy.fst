module Iocy

open FStar.Tactics
open FStar.List.Tot.Base

type trace (e:Type0) = list e

type run 'e (a:Type u#a) =
| Cv : a -> trace 'e -> run 'e a

noeq
type runtree 'e (a:Type u#a) : Type u#a =
| Node : run 'e a -> list (runtree 'e (Universe.raise_t unit)) -> runtree 'e a

let rec univ_ch (t:runtree 'e (Universe.raise_t u#0 u#a unit)) : runtree 'e (Universe.raise_t u#0 u#b unit) =
match t with
| Node (Cv x tl) rts -> Node (Cv (Universe.raise_val (Universe.downgrade_val x)) tl) (univ_change rts)
and univ_change (t:list u#a (runtree 'e (Universe.raise_t u#0 u#a unit))) : list u#b (runtree 'e (Universe.raise_t u#0 u#b unit)) =
  (** map univ_ch t **)
  match t with
  | [] -> []
  | h :: tl -> [univ_ch h]@(univ_change tl)

type hist_post 'e 'a = runtree 'e 'a -> Type0
type hist_pre 'e (a:Type u#a) = list (runtree 'e (Universe.raise_t u#0 u#a unit)) -> trace 'e -> Type0

type hist0 'e 'a = hist_post 'e 'a -> hist_pre 'e 'a

let hist_post_ord (p1 p2:hist_post 'e 'a) = forall r. p1 r ==> p2 r

let hist_wp_monotonic (wp:hist0 'e 'a) =
  forall p1 p2. (p1 `hist_post_ord` p2) ==> (forall ths h. wp p1 ths h ==> wp p2 ths h)

type hist 'e 'a = wp:(hist0 'e 'a){hist_wp_monotonic wp}

let hist_return (#e:Type0) (x:'a) : hist e 'a =
  fun p _ _ -> p (Node (Cv x []) [])

let hist_post_shift (p:hist_post 'e 'b) (rt:runtree 'e 'a) : hist_post 'e 'b =
  fun (rt':runtree 'e 'b) -> 
    match rt, rt' with
    | Node (Cv x lt) trt, Node (Cv x' lt') trt' -> p (Node (Cv x' (lt@lt')) ((univ_change trt) @ trt'))

let hist_post_bind
  (#a:Type u#a) (#b:Type u#b)
  (ths:list (runtree 'e (Universe.raise_t u#0 u#b unit)))
  (h:trace 'e)
  (kw : a -> hist 'e b)
  (p:hist_post 'e b) :
  Tot (hist_post 'e a) =
  fun (rt:runtree 'e a) ->
    match rt with | Node (Cv x lt) rts ->
    kw x (hist_post_shift p rt) ((univ_change rts)@ths) (List.rev lt @ h)

let hist_bind (#a:Type u#a) (#b:Type u#b) (w : hist 'e a) (kw : a -> hist 'e b) : hist 'e b =
  let wp = fun p ths h -> w (hist_post_bind ths h kw p) (univ_change ths) h in
  assume (hist_wp_monotonic wp);
  wp

noeq
type free (a:Type u#a) (e:Type0) : Type u#(max 1 a)=
| Require : (pre:pure_pre) -> cont:((squash pre) -> free u#a a e) -> free a e
| Return : a -> free a e
| Print : (arg:e) -> cont:(unit -> free u#a a e) -> free a e
| Fork : th:(unit -> free (Universe.raise_t unit) e) -> cont:(unit -> free a e) -> free a e
| Wait : nat -> cont:(option unit -> free a e) -> free a e

let free_return (#a:Type) (#e:Type) (x:a) : free a e =
  Return x

let rec free_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (#e:Type)
  (l : free a e)
  (k : a -> free b e) :
  free b e =
  match l with
  | Return x -> k x
  | Print str fnc -> 
      Print str (fun i -> free_bind (fnc i) k)
  | Fork th fnc ->
      Fork
        (fun i -> free_bind #(Universe.raise_t u#0 u#a unit) #(Universe.raise_t u#0 u#b unit) #e (th i) (fun x -> free_return (Universe.raise_val u#0 u#b (Universe.downgrade_val x))))
        (fun _ -> free_bind (fnc ()) k)
  | Require pre fnc ->
      Require pre (fun _ -> free_bind (fnc ()) k)
  | Wait id fnc -> 
      Wait id (fun i -> free_bind (fnc i) k)

let hist_require #e (pre:pure_pre) : hist e (squash pre) = 
  let wp' : hist0 e (squash pre) = fun p _ _ -> pre /\ p (Node (Cv () []) []) in
  assert (forall post1 post2. (hist_post_ord post1 post2 ==> (forall h thrs. wp' post1 thrs h ==> wp' post2 thrs h)));
  assert (hist_wp_monotonic wp');
  wp'

let hist_print (#e:Type) (ev:e) : hist e unit =
  fun p _ _ -> p (Node (Cv () [ev]) [])

let hist_fork (#e:Type u#0) (#a:Type u#a) (hist_th:hist e (Universe.raise_t u#0 u#a unit)) : hist e (Universe.raise_t u#0 u#a unit) =
  let wp = fun p -> hist_th (fun r -> p (Node (Cv (Universe.raise_val ()) []) [r])) in
  assume (hist_wp_monotonic wp);
  wp

val theta : (trace 'e -> runtree 'e (Universe.raise_t unit) -> Type0) -> free 'a 'e -> hist 'e 'a
let rec theta sat m =
  match m with
  | Require pre k ->
      hist_bind (hist_require pre) (fun r -> theta sat (k r))
  | Return x -> hist_return x
  | Print arg k ->
      hist_bind (hist_print arg) (fun r -> theta sat (k r))
  | Fork th k -> (
    let wp = fun p thrs h -> 
      theta sat (th ()) (fun rt -> 
        theta sat (k ()) (fun rt' -> 
          let (Node (Cv x lt) thrs) = rt' in
          p (Node (Cv x []) [rt; (Node (Cv (Universe.raise_val ()) lt) thrs) ])
        ) ((univ_ch rt)::thrs) h
      ) thrs h in
    assume (hist_wp_monotonic wp);
    wp
  )
  | Wait id k -> let wp = (fun p thrds h ->
    match nth thrds id with
    | None -> theta sat (k None) p thrds h 
    | Some rt ->
    (forall lt. lt `sat` (univ_ch rt) ==>
      theta sat (k (Some ())) (fun (Node (Cv x lt') rts) -> p (Node (Cv x (** append event with id**) lt') rts)) thrds (** - rt **) (List.rev lt @ h))) in
    assume (hist_wp_monotonic wp);
    wp



let rec interleave (t1:trace 'e) (t2:trace 'e) : list (trace 'e) =
  match t1, t2 with
  | [], [] -> []
  | _, [] -> [t1]
  | [], _ -> [t2]
  | _, _ -> 
      (map (append [hd t1]) (interleave (tail t1) t2)) @
      (map (append [hd t2]) (interleave t1 (tail t2)))

let _ =
  assert (interleave #int [0] [] == [ [0] ]);
  assert (interleave #int [] [0] == [ [0] ]);
  assert (interleave #int [0] [1;2] == [ [0;1;2]; [1;0;2]; [1;2;0] ]);
  assert (interleave #int [1;2] [0] == [ [1;2;0]; [1;0;2]; [0;1;2] ]);
  assert (flatten (map (interleave [0]) [[]]) == [ [0] ])

let product (xs:list 'a) (ys:list 'b) : list ('a * 'b) =
  concatMap (fun x -> map (fun y -> (x, y)) ys) xs

let uncurry2 (f:'a -> 'b -> 'c) ((a,b):('a * 'b)) : 'c = f a b

let interleave_lists (#e:Type0) l1 l2 : list (trace e) = 
  match l1, l2 with
  | [], [] -> []
  | [], l2 -> l2
  | l1, [] -> l1
  | _, _ -> concatMap (uncurry2 interleave) (product l1 l2)

val (===) : list 'a -> list 'a -> Type0
let (===) l1 l2 = forall e. e `memP` l1 <==> e `memP` l2

let _ =
  assert (interleave_lists [[]; [1;2]] [[]] == [ [1;2] ]);
  assert (interleave_lists [[1;2];[]] [[]] === [ [1;2] ]);
  assert (interleave_lists [[1;2]] [[0]] === [ [1;2;0]; [0;1;2]; [1;0;2] ])

let _ =
  assert (interleave_lists #int [[0;1;2];[0;2;1]] [[5;6]] === [
      [0; 1; 2; 5; 6]; [0; 1; 5; 2; 6]; [0; 1; 5; 6; 2]; [0; 5; 1; 2; 6]; [0; 5; 1; 6; 2];
      [0; 5; 6; 1; 2]; [5; 0; 1; 2; 6]; [5; 0; 1; 6; 2]; [5; 0; 6; 1; 2]; [5; 6; 0; 1; 2];
      [0; 2; 1; 5; 6]; [0; 2; 5; 1; 6]; [0; 2; 5; 6; 1]; [0; 5; 2; 1; 6]; [0; 5; 2; 6; 1];
      [0; 5; 6; 2; 1]; [5; 0; 2; 1; 6]; [5; 0; 2; 6; 1]; [5; 0; 6; 2; 1]; [5; 6; 0; 2; 1]
    ]) by (compute ())

let reduce_interleave (l:list (list (trace 'e))) : list (trace 'e) = fold_left (interleave_lists) [] l

let _ =
  assert (reduce_interleave ([[[2]]]) == [ [2] ]);
  assert (reduce_interleave ([[[]];[[2]]]) == [ [2] ])

let rec as_traces (t:runtree 'e 'a) : list (trace 'e) =
  match t with
  | Node (Cv _ lt) rts -> 
    admit (); (** proof of termination needed **)
    let trs : list (list (trace 'e)) = map as_traces rts in
    let trs : list (trace 'e) = reduce_interleave trs in
    if List.length trs > 0 then map (append lt) trs
    else [lt]

let _ = 
  assert (map (as_traces #unit #int) [
             Node (Cv () [ ]) [];
             Node (Cv () [2]) []] === [[[]];[[2]]]) by (compute ())

let _ =
  assert (
         as_traces #unit #int (Node (Cv () [1])
            [Node (Cv (Universe.raise_val ()) [ ]) [];
             Node (Cv (Universe.raise_val ()) [2]) []])
          === [ [1;2] ])

let _ = 
  assert (
         as_traces #unit #int (Node (Cv () [1])
            [Node (Cv (Universe.raise_val ()) [0]) [];
             Node (Cv (Universe.raise_val ()) [2]) []])
          === [ [1;0;2]; [1;2;0] ]) by (compute ())

let _ =
  assert (
         as_traces #unit #int (Node (Cv () [])
            [Node (Cv (Universe.raise_val ()) [0]) [];
             Node (Cv (Universe.raise_val ()) [1]) [
               Node (Cv (Universe.raise_val ()) [ ]) [];
               Node (Cv (Universe.raise_val ()) [2]) []]])
          === [ [1;0;2]; [1;2;0]; [0;1;2] ]) by (compute ())

let _ = 
  assert (
      as_traces #unit #int (Node (Cv () [])
        [Node (Cv (Universe.raise_val ()) [0])
            [Node (Cv (Universe.raise_val ()) [1]) []; Node (Cv (Universe.raise_val ()) [2]) []];
          Node (Cv (Universe.raise_val ()) [5; 6]) []]) === [
      [5; 6; 0; 2; 1]; [5; 0; 6; 2; 1]; [5; 0; 2; 6; 1]; [5; 0; 2; 1; 6]; [0; 5; 6; 2; 1];
      [0; 5; 2; 6; 1]; [0; 5; 2; 1; 6]; [0; 2; 5; 6; 1]; [0; 2; 5; 1; 6]; [0; 2; 1; 5; 6];
      [5; 6; 0; 1; 2]; [5; 0; 6; 1; 2]; [5; 0; 1; 6; 2]; [5; 0; 1; 2; 6]; [0; 5; 6; 1; 2];
      [0; 5; 1; 6; 2]; [0; 5; 1; 2; 6]; [0; 1; 5; 6; 2]; [0; 1; 5; 2; 6]; [0; 1; 2; 5; 6]]) by (compute ())

let theta' = theta (fun lt rt -> lt `List.memP` as_traces rt)

(** *** Tests **)
let result (r:runtree 'e 'a) : 'a =
  match r with
  | Node (Cv x _) _ -> x
  
let prog0 =  Print 0 (fun () -> Print 1 (fun () -> Print 2 (fun () -> Return 5)))

let _ = assert (theta' prog0 (fun r -> result r == 5 /\ as_traces r === [[0; 1; 2]]) [] [])  by (compute ())

let prog1 = Fork (fun () -> Print 0 (fun () -> Return (Universe.raise_val ()))) 
                 (fun () -> Print 1 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                  (fun () -> Return ())))


let _ = assert (theta' prog1 (fun r -> as_traces r === [[1; 0; 2]; [1; 2; 0]; [0; 1; 2]]) [] []) by (compute ())

let prog2 =  Print 0 
                 (fun () -> Print 1 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                (fun () -> Return 5)))

let _ = assert (theta' prog2 (fun r -> result r == 5 /\ as_traces r === [[0; 1; 2]]) [] [])  by (compute ())


let prog3 = Fork (fun () -> Print 0 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                 (fun () -> Return (Universe.raise_val ()))))
                 (fun () -> Print 1 (fun () -> Return ()))

let _ = assert (theta' prog3 (fun r -> result r == () /\ as_traces r === [[0; 2; 1];[0;1;2];[1;0;2]]) [] []) by (compute ())

(** TODO: extra test, check if the history after Wait can be 0,5 and 5,0, not just 5,0 **)
let prog4 = Fork (fun () -> Print 0 (fun () -> Return (Universe.raise_val ()))) 
                 (fun () -> Print 5 (fun () -> Wait 0 (fun _ -> Print 6 (fun () -> Return ()))))

let _ = assert (theta' prog4 (fun r -> result r == () /\ as_traces r == [[0; 5; 6];[5;0;6]]) [] [])  by (  compute ();
  dump "h";
  tadmit ())

let prog5 = Fork (fun () -> Print 0 (fun () -> Fork (fun () -> Print 1 (fun () -> Return (Universe.raise_val ())))
                                                 (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))))
                 (fun () -> Print 5 (fun () -> Wait 0 (fun _ -> Print 6 (fun () -> Return ()))))


let _ = assert (theta' prog5 (fun r -> result r == () /\ as_traces r == [[0;1;2;5;6];[0;2;1;5;6];[0;2;5;1;6];[0;5;2;1;6];[0;5;2;1;6]]) [] [])  by (
  compute ();
  dump "h")


(** TODO: test Fork followed by Fork **)
