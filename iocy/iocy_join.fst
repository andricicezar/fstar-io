module Iocy_Join

open FStar.Tactics
open FStar.List.Tot.Base

type event (e:Type0) =
| Ev : e -> event e
| EJoin : event e

type trace (e:Type0) = list (event e)

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
| Join : cont:(unit -> free a e) -> free a e

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
        (fun id -> free_bind (fnc id) k)
  | Require pre fnc ->
      Require pre (fun _ -> free_bind (fnc ()) k)
  | Join fnc -> 
      Join (fun i -> free_bind (fnc i) k)

let hist_require #e (pre:pure_pre) : hist e (squash pre) = 
  let wp' : hist0 e (squash pre) = fun p _ _ -> pre /\ p (Node (Cv () []) []) in
  assert (forall post1 post2. (hist_post_ord post1 post2 ==> (forall h thrs. wp' post1 thrs h ==> wp' post2 thrs h)));
  assert (hist_wp_monotonic wp');
  wp'

let hist_print (ev:'e) : hist 'e unit =
  fun p _ _ -> p (Node (Cv () [Ev ev]) [])

let hist_fork (#e:Type u#0) (#a:Type u#a) (hist_th:hist e (Universe.raise_t u#0 u#a unit)) : hist e (Universe.raise_t u#0 u#a unit) =
  let wp = fun p -> hist_th (fun r -> p (Node (Cv (Universe.raise_val ()) []) [r])) in
  assume (hist_wp_monotonic wp);
  wp

val theta : (trace 'e -> list (runtree 'e (Universe.raise_t unit)) -> Type0) -> free 'a 'e -> hist 'e 'a
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
  | Join k -> let wp = (fun p thrds h ->
    (forall lt. lt `sat` (univ_change thrds) ==>
      theta sat (k ()) (fun (Node (Cv x lt') rts) -> p (Node (Cv x (EJoin::lt')) rts)) [] (List.rev lt @ EJoin :: h))) in
    assume (hist_wp_monotonic wp);
    wp


let rec interleave (t1:list 'e) (t2:list 'e) : list (list 'e) =
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

let filter_out_join (t:trace 'e) : trace 'e =
  filter (fun ev -> not (EJoin? ev)) t
  
let rec split_trace_join (t:trace 'e) acc : Tot ((trace 'e) * (trace 'e)) (decreases t) =
  match t with
  | [] -> (acc, [])
  | EJoin :: tl -> (acc, t)
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

let _ =
  assert (interleave_traces [Ev 1;Ev 2] [Ev 3;EJoin;Ev 4] == [ [Ev 1;Ev 2;Ev 3;EJoin;Ev 4]; [Ev 1;Ev 3;Ev 2;EJoin; Ev 4]; [Ev 3;Ev 1;Ev 2;EJoin;Ev 4] ]);
  assert (interleave_traces [EJoin;Ev 1;Ev 2] [Ev 3] == [ [Ev 1;Ev 2;Ev 3]; [Ev 1;Ev 3;Ev 2;]; [Ev 3;Ev 1;Ev 2] ]);
  assert (interleave_traces [Ev 0] [Ev 1;Ev 2] == [ [Ev 0;Ev 1;Ev 2]; [Ev 1;Ev 0;Ev 2]; [Ev 1;Ev 2;Ev 0] ])

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

let _ =
  assert (product_map interleave [[]; [1;2]] [[]] === [ [1;2] ]);
  assert (product_map interleave [[1;2];[]] [[]] === [ [1;2] ]);
  assert (product_map interleave [[1;2]] [[0]] === [ [1;2;0]; [0;1;2]; [1;0;2] ])

let _ =
  assert (product_map interleave [[0;1;2];[0;2;1]] [[5;6]] === [
      [0; 1; 2; 5; 6]; [0; 1; 5; 2; 6]; [0; 1; 5; 6; 2]; [0; 5; 1; 2; 6]; [0; 5; 1; 6; 2];
      [0; 5; 6; 1; 2]; [5; 0; 1; 2; 6]; [5; 0; 1; 6; 2]; [5; 0; 6; 1; 2]; [5; 6; 0; 1; 2];
      [0; 2; 1; 5; 6]; [0; 2; 5; 1; 6]; [0; 2; 5; 6; 1]; [0; 5; 2; 1; 6]; [0; 5; 2; 6; 1];
      [0; 5; 6; 2; 1]; [5; 0; 2; 1; 6]; [5; 0; 2; 6; 1]; [5; 0; 6; 2; 1]; [5; 6; 0; 2; 1]
    ]) by (compute ())

let reduce_interleave (l:list (list (trace 'e))) : list (trace 'e) = fold_left (product_map interleave_traces) [] l

let _ =
  assert (reduce_interleave ([[[Ev 2]]]) == [ [Ev 2] ]);
  assert (reduce_interleave ([[[]];[[Ev 2]]]) == [ [Ev 2] ])

(** The tree is traversed Deep First and post-order **)
let rec as_traces (t:runtree 'e 'a) : list (trace 'e) =
  match t with
  | Node (Cv _ lt) rts -> 
    let trs = as_traces_threads rts in
    if List.length trs > 0 then map (append lt) trs
    else [lt]
and as_traces_threads (rts:list (runtree 'e 'a)) : list (trace 'e) =
  admit (); (** proof of termination needed **)
  let trs : list (list (trace 'e)) = map as_traces rts in
  let trs : list (trace 'e) = reduce_interleave trs in
  trs

let as_simpl_traces (t:runtree 'e 'a) : list (list 'e) =
  map (map (fun (x:event 'e) -> match x with | Ev ev -> ev | EJoin -> admit ()))
    (map (fun (t1:trace 'e) -> filter_out_join t1) (as_traces t))

let as_simpl_traces' (t:list (runtree 'e 'a)) : list (list 'e) =
  map (map (fun (x:event 'e) -> match x with | Ev ev -> ev | EJoin -> admit ()))
    (map (fun (t1:trace 'e) -> filter_out_join t1) (as_traces_threads t))

let _ = 
  assert (map (as_traces #unit #int) [
             Node (Cv () [ ]) [];
             Node (Cv () [Ev 2]) []] === [[[]];[[Ev 2]]]) by (compute ())

let _ =
  assert (
         as_traces #unit #int (Node (Cv () [Ev 1])
            [Node (Cv (Universe.raise_val ()) [ ]) [];
             Node (Cv (Universe.raise_val ()) [Ev 2]) []])
          === [ [Ev 1;Ev 2] ])

let _ = 
  assert (
         as_traces #unit #int (Node (Cv () [Ev 1])
            [Node (Cv (Universe.raise_val ()) [Ev 0]) [];
             Node (Cv (Universe.raise_val ()) [Ev 2]) []])
          === [ [Ev 1;Ev 0;Ev 2]; [Ev 1;Ev 2;Ev 0] ]) by (compute ())

let _ = 
  assert (
         as_traces #unit #int (Node (Cv () [Ev 1])
            [Node (Cv (Universe.raise_val ()) [Ev 2;Ev 3]) [];
             Node (Cv (Universe.raise_val ()) [Ev 4;EJoin;Ev 5]) []])
          == [
      [Ev 1; Ev 2; Ev 3; Ev 4; EJoin; Ev 5];
      [Ev 1; Ev 2; Ev 4; Ev 3; EJoin; Ev 5];
      [Ev 1; Ev 4; Ev 2; Ev 3; EJoin; Ev 5]
    ]) by (compute (); dump "H")

let _ =
  assert (
         as_traces #unit #int (Node (Cv () [])
            [Node (Cv (Universe.raise_val ()) [Ev 0]) [];
             Node (Cv (Universe.raise_val ()) [Ev 1]) [
               Node (Cv (Universe.raise_val ()) [ ]) [];
               Node (Cv (Universe.raise_val ()) [Ev 2]) []]])
          === [ [Ev 1;Ev 0;Ev 2]; [Ev 1;Ev 2;Ev 0]; [Ev 0;Ev 1;Ev 2] ]) by (compute ())

let _ = 
  assert (
      as_simpl_traces #unit #int (Node (Cv () [])
        [Node (Cv (Universe.raise_val ()) [Ev 0])
            [Node (Cv (Universe.raise_val ()) [Ev 1]) []; Node (Cv (Universe.raise_val ()) [Ev 2]) []];
          Node (Cv (Universe.raise_val ()) [Ev 5; Ev 6]) []]) === [
      [5; 6; 0; 2; 1]; [5; 0; 6; 2; 1]; [5; 0; 2; 6; 1]; [5; 0; 2; 1; 6]; [0; 5; 6; 2; 1];
      [0; 5; 2; 6; 1]; [0; 5; 2; 1; 6]; [0; 2; 5; 6; 1]; [0; 2; 5; 1; 6]; [0; 2; 1; 5; 6];
      [5; 6; 0; 1; 2]; [5; 0; 6; 1; 2]; [5; 0; 1; 6; 2]; [5; 0; 1; 2; 6]; [0; 5; 6; 1; 2];
      [0; 5; 1; 6; 2]; [0; 5; 1; 2; 6]; [0; 1; 5; 6; 2]; [0; 1; 5; 2; 6]; [0; 1; 2; 5; 6]]) by (compute ())

let theta' = theta (fun lt rt -> lt `List.memP` as_traces_threads rt)

(** *** Tests **)
let result (r:runtree 'e 'a) : 'a =
  match r with
  | Node (Cv x _) _ -> x
  
let prog0 =  Print 0 (fun () -> Print 1 (fun () -> Print 2 (fun () -> Return 5)))

let _ = assert (theta' prog0 (fun r -> result r == 5 /\ as_simpl_traces r === [[0; 1; 2]]) [] [])  by (compute ())

let prog1 = Fork (fun () -> Print 0 (fun () -> Return (Universe.raise_val ()))) 
                 (fun () -> Print 1 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                  (fun () -> Return ())))


let _ = assert (theta' prog1 (fun r -> as_simpl_traces r === [[1; 0; 2]; [1; 2; 0]; [0; 1; 2]]) [] []) by (compute ())

let prog2 =  Print 0 
                 (fun () -> Print 1 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                (fun () -> Return 5)))

let _ = assert (theta' prog2 (fun r -> result r == 5 /\ as_simpl_traces r === [[0; 1; 2]]) [] [])  by (compute ())


let prog3 = Fork (fun () -> Print 0 (fun () -> Fork (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))
                                                 (fun () -> Return (Universe.raise_val ()))))
                 (fun () -> Print 1 (fun () -> Return ()))

let _ = assert (theta' prog3 (fun r -> result r == () /\ as_simpl_traces r === [[0; 2; 1];[0;1;2];[1;0;2]]) [] []) by (compute ())

(** TODO: extra test, check if the history after Wait can be 0,5 and 5,0, not just 5,0 **)
let prog4 = Fork (fun () -> Print 0 (fun () -> Return (Universe.raise_val ()))) 
                 (fun () -> Print 1 (fun () -> Join (fun _ -> Print 2 (fun () -> Return ()))))

let _ = assert (theta' prog4 (fun r -> result r == () /\ as_traces r == [[Ev 0; Ev 1;EJoin; Ev 2];[Ev 1;Ev 0;EJoin;Ev 2]]) [] [])  by (  compute ();
  dump "h")

let prog5 = Fork (fun () -> Print 0 (fun () -> Fork (fun () -> Print 1 (fun () -> Return (Universe.raise_val ())))
                                                 (fun () -> Print 2 (fun () -> Return (Universe.raise_val ())))))
                 (fun () -> Print 5 (fun () -> Join (fun _ -> Print 6 (fun () -> Return ()))))

let _ = assert (theta' prog5 (fun r -> result r == () /\ as_simpl_traces r == [
        [0; 1; 2; 5; 6];
        [0; 1; 5; 2; 6];
        [0; 5; 1; 2; 6];
        [5; 0; 1; 2; 6];
        [0; 2; 1; 5; 6];
        [0; 2; 5; 1; 6];
        [0; 5; 2; 1; 6];
        [5; 0; 2; 1; 6]
      ]
) [] []) by (compute ())

let prog6 = Fork (fun () -> Print 0 (fun () -> Fork (fun () -> Print 1 (fun () -> Return (Universe.raise_val ())))
                                                (fun () -> Join (fun () -> Print 2 (fun () -> Return (Universe.raise_val ()))))))
                 (fun () -> Print 5 (fun () -> Join (fun _ -> Print 6 (fun () -> Return ()))))
    
let _ = assert (theta' prog6 (fun r -> result r == () /\ as_simpl_traces r == 
[
        [0; 1; 2; 5; 6];
        [0; 1; 5; 2; 6];
        [0; 5; 1; 2; 6];
        [5; 0; 1; 2; 6]
      ]
) [] [])  by (compute ())

(** TODO: test Fork followed by Fork **)

let prog11 () = Fork (fun () -> Print 110 (fun () -> Fork (fun () -> Print 111 (fun () -> Return (Universe.raise_val ())))
                                                       (fun () -> Print 112 (fun () -> Return (Universe.raise_val ())))))
                     (fun id -> Print 120 (fun () -> Fork (fun () -> Print 121 (fun () -> Return (Universe.raise_val ())))
                                                      (fun () -> Print 122 (fun () -> Return (Universe.raise_val ())))))
let prog12 () = Fork (fun () -> Print 210 (fun () -> Fork (fun () -> Print 211 (fun _ -> Return (Universe.raise_val ())))
                                                      (fun () -> Join (fun () -> Print 212 (fun () -> Return (Universe.raise_val ()))))))
                     (fun id -> Print 220 (fun () -> Fork (fun () -> Print 221 (fun () -> Return (Universe.raise_val ())))
                                                       (fun id -> Join (fun () -> Print 222 (fun () -> Return ())))))

let prog7 = Print 0 (fun () -> Fork (fun () -> Print 100 prog11) (fun () -> Print 200 prog12))

// let _ = assert (theta' (prog12 ()) (fun r -> as_simpl_traces r == []) [] []) by (compute (); dump "foo")

/// Quantified Linear Temporal logic on sets of finite traces [trs: list (list s)]
///
/// We define the quantifier [quant] and ltl syntax [ltl_syntax].
type quant =
| Forall
| Exists

unopteq
type ltl_syntax (s:Type0) =
| Eventually : ltl_syntax s -> ltl_syntax s
| Always: ltl_syntax s -> ltl_syntax s
| And: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Or: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Impl: ltl_syntax s -> ltl_syntax s -> ltl_syntax s
| Now: (s -> Type0) -> ltl_syntax s

let rec suffixes_of (l:list 'a) : list (list 'a) =
match l with
| [] -> []
| h::tl -> [l] @ (suffixes_of tl)

/// Give the denotation of an ltl formula [form] given a finite trace [tr: list s]
let rec ltl_denote (#s: Type0)(form: ltl_syntax s)(tr: list s): Type0 =
  match form with
  | Now p -> ~(tr == []) /\ p (hd tr)
  //| Eventually p -> exists (i: nat). i <= length tr /\ ltl_denote p (snd (splitAt i tr))
  //| Always p -> forall (i: nat). i <= length tr ==> ltl_denote p (snd (splitAt i tr))
  | Eventually p -> exists (tl:list s). tl `memP` suffixes_of tr /\ ltl_denote p tl
  | Always p -> forall (tl:list s). tl `memP` suffixes_of tr ==> ltl_denote p tl
  | And p q -> ltl_denote p tr /\ ltl_denote q tr
  | Or p q -> ltl_denote p tr /\ ltl_denote q tr
  | Impl p q -> ltl_denote p tr ==> ltl_denote q tr

/// Quantified LTL formula
type qltl_formula s = quant * ltl_syntax s

/// Satisfiability of a QLTL formula over sets of finite traces [trs] (non-empty)
let rec qltl_denote (#t: Type0)(form: qltl_formula t)(trs: list (list t)): Type0 =
  match form, trs with
 // | (Forall, p), [] -> True
 // | (Forall, p), t::tl -> ltl_denote p t /\ qltl_denote form tl
  | (Forall, p), _ -> forall t. t `memP` trs ==> ltl_denote p t
  | (Exists, p), [] -> False
  | (Exists, p), t::trs' -> ltl_denote p t \/ qltl_denote form trs'

 // match form with
 // | (Forall, p) -> forall t. t `memP` trs ==> ltl_denote p t
 // | (Exists, p) -> exists t. t `memP` trs /\ ltl_denote p t

// Some assertions, SMT is getting stuck on quantifiers I think
let _ = assert(qltl_denote (Forall, Eventually (Now (fun n -> n % 2 == 1))) [[0; 1]; [3]])
let _ = assert(qltl_denote (Forall, Always (Now (fun n -> n % 2 == 1))) [[1]; [3]]) 
let _ = assert(qltl_denote (Exists, Always (Now (fun n -> n % 2 == 1))) [[4]; [6]; [2]; [1]; [2]])
