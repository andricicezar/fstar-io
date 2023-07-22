module Iocy

open FStar.Tactics
open FStar.List.Tot.Base

type trace (e:Type0) = list e
  
type run 'e (a:Type u#a) =
| Cv : a -> trace 'e -> run 'e a

noeq
type runtree 'e (a:Type u#a) : Type u#a =
| Node : run 'e a -> list u#a (runtree 'e (Universe.raise_t unit)) -> runtree 'e a

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

let rec reduce (l:list (trace 'e)) (acc:list (trace 'e)) : list (trace 'e) =
  match l with
  | [] -> acc
  | h::tl -> reduce tl (flatten (map (interleave h) acc))

val (===) : list 'a -> list 'a -> Type0
let (===) l1 l2 = forall e. e `memP` l1 <==> e `memP` l2

let _ =
//  assert (reduce #int [[]; [1;2]] [[]] == [ [1;2] ]) by (compute (); dump "h");
  assert (reduce #int [[1;2];[]] [[]] === [ [1;2] ]);
  assert (reduce #int [[1;2]] [[0]] === [ [1;2;0]; [0;1;2]; [1;0;2] ])
  
let rec as_trace (t:runtree 'e 'a) : list (trace 'e) =
  match t with
  | Node (Cv _ lt) rts -> 
    admit ();
    map (append lt) (reduce (filter (fun l -> l <> []) (concatMap as_trace rts)) [[]])


let _ = 
  assert (
         as_trace #unit #int (Node (Cv () [1])
            [Node (Cv (Universe.raise_val ()) [ ]) [];
             Node (Cv (Universe.raise_val ()) [2]) []])
          == [ [1;2] ]) by (compute ());
  assert (
         as_trace #unit #int (Node (Cv () [1])
            [Node (Cv (Universe.raise_val ()) [0]) [];
             Node (Cv (Universe.raise_val ()) [2]) []])
          === [ [1;0;2]; [1;2;0] ]) by (compute ());
  assert (
         as_trace #unit #int (Node (Cv () [])
            [Node (Cv (Universe.raise_val ()) [0]) [];
             Node (Cv (Universe.raise_val ()) [1]) [
               Node (Cv (Universe.raise_val ()) [ ]) [];
               Node (Cv (Universe.raise_val ()) [2]) []]])
          === [ [1;0;2]; [1;2;0]; [0;1;2] ]) by (compute ())

let rec univ_ch (t:runtree 'e (Universe.raise_t u#0 u#a unit)) : runtree 'e (Universe.raise_t u#0 u#b unit) =
match t with
| Node (Cv x tl) rts -> Node (Cv (Universe.raise_val (Universe.downgrade_val x)) tl) (univ_change rts)
and univ_change (t:list u#a (runtree 'e (Universe.raise_t u#0 u#a unit))) : list u#b (runtree 'e (Universe.raise_t u#0 u#b unit)) =
  match t with
  | [] -> []
  | h :: tl -> [univ_ch h]@(univ_change tl)

let rec prepend_rt (lt:list 'e) (rt:runtree 'e 'a) : Tot (runtree 'e 'a) (decreases rt) =
  admit ();
  match rt with
  | Node (Cv x lt') rt -> Node (Cv x (lt@lt')) (map #(runtree 'e (Universe.raise_t unit)) (prepend_rt lt) rt)

type hist_post 'e 'a = runtree 'e 'a -> Type0
type hist_pre 'e = trace 'e -> Type0

type hist0 'e 'a = hist_post 'e 'a -> hist_pre 'e

let hist_post_ord (p1 p2:hist_post 'e 'a) = forall r. p1 r ==> p2 r

let hist_wp_monotonic (wp:hist0 'e 'a) =
  forall p1 p2. (p1 `hist_post_ord` p2) ==> (forall h. wp p1 h ==> wp p2 h)

type hist 'e a = wp:(hist0 'e a){hist_wp_monotonic wp}

let hist_return (#e:Type0) (x:'a) : hist e 'a =
  fun p _ -> p (Node (Cv x []) [])

let hist_post_shift (p:hist_post 'e 'b) (rt:runtree 'e 'a) : hist_post 'e 'b =
  fun (rt':runtree 'e 'b) -> 
    match rt, rt' with
      | Node (Cv x lt) trt, Node (Cv x' lt') trt' -> p (Node (Cv x' (lt@lt')) ((univ_change trt) @ trt'))

let hist_post_bind
  (h:trace 'e)
  (kw : 'a -> hist 'e 'b)
  (p:hist_post 'e 'b) :
  Tot (hist_post 'e 'a) =
  fun (rt:runtree 'e 'a) ->
    let (x,lt) = (match rt with | Node (Cv x lt) _ -> (x,lt)) in
    kw x (hist_post_shift p rt) (List.rev lt @ h)

let hist_bind0 (w : hist 'e 'a) (kw : 'a -> hist 'e 'b) : hist0 'e 'b =
  fun p h -> w (hist_post_bind h kw p) h

let hist_bind (w : hist 'e 'a) (kw : 'a -> hist 'e 'b) : hist 'e 'b =
  let wp =   hist_bind0 w kw in
  assume (hist_wp_monotonic wp);
  wp

val hist_ord : hist 'e 'a -> hist 'e 'a -> Type0
let hist_ord wp1 wp2 = forall h p. wp1 p h ==> wp2 p h

val hist_equiv : hist 'e 'a -> hist 'e 'a -> Type0
let hist_equiv wp1 wp2 = forall h p. wp1 p h <==> wp2 p h

noeq
type free (a:Type u#a) (e:Type0) : Type u#(max 1 a)=
| Return : a -> free a e
| Print : (arg:e) -> cont:(unit -> free u#a a e) -> free a e
| Fork : th:(unit -> free (Universe.raise_t unit) e) -> cont:(unit -> free a e) -> free a e
| Require : (pre:pure_pre) -> cont:((squash pre) -> free u#a a e) -> free a e

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
      Print str (fun i ->
        free_bind (fnc i) k)
  | Fork th fnc ->
      Fork
        (fun i -> free_bind #(Universe.raise_t u#0 u#a unit) #(Universe.raise_t u#0 u#b unit) #e (th i) (fun x -> free_return (Universe.raise_val u#0 u#b (Universe.downgrade_val x))))
        (fun _ -> free_bind (fnc ()) k)
  | Require pre fnc ->
      Require pre (fun _ ->
        free_bind (fnc ()) k)

let hist_require #e (pre:pure_pre) : hist e (squash pre) = 
  let wp' : hist0 e (squash pre) = fun p h -> pre /\ p (Node (Cv () []) []) in
  assert (forall post1 post2. (hist_post_ord post1 post2 ==> (forall h. wp' post1 h ==> wp' post2 h)));
  assert (hist_wp_monotonic wp');
  wp'

let hist_print (#e:Type) (ev:e) : hist e unit =
  fun p _ -> p (Node (Cv () [ev]) [])

let hist_fork0 (#e:Type u#0) (#a:Type u#a) (hist_th:hist e (Universe.raise_t u#0 u#a unit)) : hist0 e (Universe.raise_t u#0 u#a unit) =
  fun p h -> hist_th (fun r -> p (Node (Cv (Universe.raise_val ()) []) [r])) h

let hist_fork (#e:Type u#0) (#a:Type u#a) (hist_th:hist e (Universe.raise_t u#0 u#a unit)) : hist e (Universe.raise_t u#0 u#a unit) =
  let wp = hist_fork0 #e #a hist_th in
  assume (hist_wp_monotonic wp);
  wp

val theta : free 'a 'e -> hist 'e 'a
let rec theta m =
  match m with
  | Return x -> hist_return x
  | Require pre k ->
      hist_bind (hist_require pre) (fun r -> theta (k r))
  | Print arg k ->
      hist_bind (hist_print arg) (fun r -> theta (k r))
  | Fork th k -> (
    let wp = fun p h -> 
      theta (th ()) (fun rt -> 
        theta (k ()) (fun rt' -> 
          let (Node (Cv x lt) thrs) = rt' in
          p (Node (Cv x []) [rt; (Node (Cv (Universe.raise_val ()) lt) thrs) ])
        ) h
      ) h in
    assume (hist_wp_monotonic wp);
    wp
  )
      //hist_bind (hist_fork #string #a (theta (th ()))) (fun _ -> theta (k ()))

#reset-options
let result (r:runtree 'e 'a) : 'a =
  match r with
  | Node (Cv x _) _ -> x
  
let prog0 =  Print 0 (fun () -> Print 1 (fun () -> Print 2 (fun () -> Return 5)))

let _ = assert (theta prog0 (fun r -> result r == 5 /\ as_trace r === [[0; 1; 2]]) [])  by (norm [delta_only [`%prog0; `%theta;`%hist_print;`%hist_bind;`%hist_fork;`%hist_fork0;`%hist_bind0;`%hist_post_bind;`%hist_return;`%hist_post_shift;`%univ_change;`%univ_ch];zeta;iota]; 

  l_to_r [`List.Tot.Properties.append_l_nil;`List.Tot.Properties.append_nil_l];
  compute ())

let prog1 = Fork (fun () -> Print 0 (fun () -> Return (Universe.raise_val ()))) 
                 (fun () -> Print 1 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                  (fun () -> Return ())))


let _ = assert (theta prog1 (fun r -> as_trace r === [[1; 0; 2]; [1; 2; 0]; [0; 1; 2]]) [])  by (norm [delta_only [`%prog1; `%theta;`%hist_print;`%hist_bind;`%hist_fork;`%hist_fork0;`%hist_bind0;`%hist_post_bind;`%hist_return;`%hist_post_shift;`%univ_change;`%univ_ch];zeta;iota]; 

  l_to_r [`List.Tot.Properties.append_l_nil;`List.Tot.Properties.append_nil_l];
  compute ())

let prog2 =  Print 0 
                 (fun () -> Print 1 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                (fun () -> Return 5)))

let _ = assert (theta prog2 (fun r -> result r == 5 /\ as_trace r === [[0; 1; 2]]) [])  by (norm [delta_only [`%prog2; `%theta;`%hist_print;`%hist_bind;`%hist_fork;`%hist_fork0;`%hist_bind0;`%hist_post_bind;`%hist_return;`%hist_post_shift;`%univ_change;`%univ_ch];zeta;iota]; 

  l_to_r [`List.Tot.Properties.append_l_nil;`List.Tot.Properties.append_nil_l];
  compute ())


let prog3 = Fork (fun () -> Print 0 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                 (fun () -> Return (Universe.raise_val ()))))
                 (fun () -> Print 1 (fun () -> Return ()))

let _ = assert (theta prog3 (fun r -> result r == () /\ as_trace r === [[0; 2; 1];[0;1;2];[1;0;2]]) [])  by (norm [delta_only [`%prog2; `%theta;`%hist_print;`%hist_bind;`%hist_fork;`%hist_fork0;`%hist_bind0;`%hist_post_bind;`%hist_return;`%hist_post_shift;`%univ_change;`%univ_ch];zeta;iota]; 

  l_to_r [`List.Tot.Properties.append_l_nil;`List.Tot.Properties.append_nil_l];
  compute ())
