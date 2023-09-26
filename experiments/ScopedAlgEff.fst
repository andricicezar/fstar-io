module ScopedAlgEff

noeq
type signature = {
  act : Type0 ;
  arg : a:act -> Type0 ;
  res : #a:act -> arg a -> Type0 ;
}

type io_act = | Read | Write

let io_arg ac =
  match ac with
  | Read -> unit 
  | Write -> string

let io_res #ac (x : io_arg ac) =
  match ac with
  | Read -> string
  | Write -> unit

let io_sig : signature = { act = io_act ; arg = io_arg ; res = io_res }

assume type label_typ
type fid_typ = nat

//type labeled_signature = signature * label_typ
type labeled_signature = label_typ
type dirt = list (either labeled_signature fid_typ)

noeq
type fnc_typ = {
  a : Type u#0; 
  b : Type u#0; 
  d : dirt;
  m : a -> Type u#0 -> dirt -> Type u#0;
  t : x:a -> m x b d
}

noeq
type store = {
  n : fid_typ;
  get : (id:fid_typ{id < n} -> fnc_typ);
}//{forall i. i >= n ==> get i == None}

noeq
type free (s:signature) (st:store) (a:Type u#a) : Type u#a = 
| Return : a -> free s st a
| Op : l:label_typ -> op:s.act -> arg:s.arg op -> (s.res arg -> free s st a) -> free s st a
| Scope : fid:fid_typ{fid < st.n} -> (st.get fid).a -> ((st.get fid).b -> free s st a) -> free s st a
// | Require : (pre:pure_pre) -> cont:((squash pre) -> free s st a) -> free s st a

let empty_store = { n = 0; get = (fun id -> match id with) }

let ___test_st0 : fnc_typ = {
  a = int;
  b = int;
  d = [];
  m = (fun _ b d -> free io_sig empty_store b);
  t = (fun x -> Return (x+42))
}


let rec free_bind
  (#s:signature)
  (#st:store)
  (#a:Type u#a)
  (#b:Type u#b)
  (l : free s st a)
  (k : a -> free s st b) :
  free s st b =
  match l with
  | Return x -> k x
  | Op l op arg fnc ->
      Op l op arg (fun i -> free_bind (fnc i) k)
  | Scope fid x fnc ->
      Scope fid x (fun i -> free_bind (fnc i) k)


open FStar.List.Tot.Base

let (++) (d1 d2:dirt) : dirt = append d1 d2

let rec (<<=) (d1 d2:dirt) : Type0 =
  match d1 with
  | [] -> true
  | h :: tl -> memP h d2 /\ tl <<= d2

let rec satisfies (m:free 's 'st 'a) (d:dirt) =
  match m with
  | Return _ -> True
  | Scope fid x k -> Inr fid `memP` d /\ (forall x. (k x) `satisfies` d)
  | Op l op arg fnc -> Inl l `memP` d /\ (forall x. (fnc x) `satisfies` d)

type mon s st a d =
  m:(free s st a){m `satisfies` d}

let mon_bind
  (#s:signature)
  (#st:store)
  (#a:Type u#a)
  (#b:Type u#b)
  (#d_l #d_k:dirt)
  ($l : mon s st a d_l)
  (k : a -> mon s st b d_k) :
  mon s st b (d_l ++ d_k) =
  admit ();
  free_bind l k

let lemma (#a:Type u#0) (#b:Type u#0) s st fid x k d : Lemma
  (requires (Scope fid x k `satisfies #_ #s #st` d /\ ~((Inr fid) `memP` d)))
  (ensures (False)) = ()
  
let ___test_st1 : fnc_typ = {
  a = int;
  b = int;
  d = [];
  m = (fun _ b d -> mon io_sig empty_store b d);
  t = (fun x -> Return (x+42))
}

open FStar.Tactics
  
let make_store (#a:Type u#0) (#st_c:a -> store) #sig (#b:Type u#0) (#d:dirt) ($c:(x:a -> mon sig (st_c x) b d)) : store = {
 n = 1;
 get = (fun fid ->
   match fid with
   | 0 -> { a = a; b = b; d = d; m = (fun x b d -> mon sig (st_c x) b d); t = c })
}


val prog : c:(unit -> mon io_sig empty_store unit []) -> mon io_sig (make_store c) unit [Inr 0]
let prog c =
  Scope 0 () Return
  
val prog1 : c:(int -> mon io_sig empty_store int []) -> mon io_sig (make_store c) int [Inr 0]
let prog1 c =
  Scope 0 5 Return

type cb_typ2 = unit -> mon io_sig empty_store unit []
type c_typ2 = cb:cb_typ2 -> mon io_sig (make_store cb) int []
val prog2 : c:c_typ2 -> mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inr 0]
let prog2 c =
  let cb : cb_typ2 = (fun () -> Return ()) in
  Scope 0 cb Return

assume val l_p : label_typ
assume val l_c : label_typ

type cb_typ3 = unit -> mon io_sig empty_store unit [Inl l_p]

type c_typ3 = cb:cb_typ3 -> mon io_sig (make_store cb) int [Inl l_c; Inr 0]

let act (#st:store) (l:label_typ) (op:io_sig.act) (arg:io_sig.arg op) : mon io_sig st (io_sig.res arg) [Inl l] =
  Op l op arg Return

let scope (#sig:signature) (#st:store) (fid:fid_typ{fid < st.n}) (arg:(st.get fid).a) : mon sig st (st.get fid).b [Inr fid] =
  Scope fid arg Return

val prog3 : c:c_typ3 -> mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0]
let prog3 c : mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0] =
  let cb : cb_typ3 = (fun () -> act l_p Write "Test") in
  mon_bind (act l_p Write "Test2") (fun () -> scope 0 cb)

val prog3' : c:c_typ3 -> mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0]
let prog3' c =
  let cb : cb_typ3 = (fun () -> act l_p Write "Test") in
  mon_bind (scope 0 cb) (fun _ -> prog3 c) 

val prog3'' : c:c_typ3 -> mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0]
[@expect_failure] // c does effects labeled with l_c, but prog3'' can only have effects labeled with l_p
let prog3'' c =
  let cb : cb_typ3 = (fun () -> act l_p Write "Test") in
  c cb

val prog3''' : c:c_typ3 -> mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0]
[@expect_failure] // cb does effects labeled with l_c, while its type allows only effects labeled with l_p
let prog3''' c =
  let cb : cb_typ3 = (fun () -> act l_c Write "Test") in
  scope 0 cb

let mon_return #st #b (x:b) : mon io_sig st b [] = Return x


type cb_typ4 = unit -> mon io_sig empty_store unit [Inl l_c]
type c_typ4 = unit -> mon io_sig empty_store (cb_typ4) [Inl l_c]

val prog4 : c:c_typ4 -> mon io_sig (make_store c) unit [Inr 0]
[@expect_failure]
let prog4 c =
  mon_bind (scope 0 ()) (fun (cb:cb_typ4) -> cb ())

// TODO: add ability to call/scope the callback
val prog4' : c:c_typ4 -> mon io_sig (make_store c) unit [Inr 0]
[@expect_failure]
let prog4' c =
  mon_bind (scope 0 ()) (fun (cb:cb_typ4) -> cb ())

(* Folding a computation tree. The folding operation `h` need only be
defined for the operations in the tree. We also take a value case
so this essentially has a builtin 'map' as well. *)
val fold_with (#a #b:_) (#sig:_) (#st:_) (#d:dirt)
  (f:mon sig st a d)
  (v : a -> b)
            // This may become (o:sig.act{Inl (sig,l) `memP` d}) 
  (h  : ((l:label_typ) -> (o:sig.act{Inl l `memP` d}) -> ar:sig.arg o -> (sig.res ar -> b) -> b))
  (hs : (fid:fid_typ{fid < st.n /\ Inr fid `memP` d} -> x:(st.get fid).a -> 
         (c:Type & 
         handle_fid : c &
         combine:(c -> ((st.get fid).b -> b) -> b))
         ))
  : b

let rec fold_with #a #b #sig #st #d f v h hs =
  match f with
  | Return x -> v x
  | Scope fid x k ->
    let f = (st.get fid).t in
    let k' (o : (st.get fid).b) : b =
      fold_with #_ #_ #sig #st #d (k o) v h hs in

    let (| c , handle_fid, combine |) = hs fid x in
    combine handle_fid k'
  | Op l act x k ->
    let k' (o : sig.res x) : b =
       fold_with #_ #_ #sig #st #d (k o) v h hs
    in
    h l act x k'

let handler_tree_op #sig #st (l:label_typ) (o:sig.act) (b:Type) (d:dirt) =
  x:sig.arg o -> (sig.res x -> mon sig st b d) -> mon sig st b d

let handler_tree #sig #st (d0 : dirt) (b:Type) (d1 : dirt) : Type =
  l:label_typ -> o:sig.act{Inl l `memP` d0} -> handler_tree_op #sig #st l o b d1

assume val lemma_memP_append : l1:list 'a -> l2:list 'a -> x:'a -> 
  Lemma (requires (x `memP` (l1 @ l2))) (ensures (x `memP` l1 \/ x `memP` l2))
  [SMTPat (x `memP` (l1@l2))]

let rec lemma_satisfies (t:free 'sig 'st 'a) d : Lemma (requires (t `satisfies` (d++d))) (ensures (t `satisfies` d))
  [SMTPat (t `satisfies` (d++d))] =
  match t with
  | Return _ -> ()
  | Scope fid x k -> begin
      introduce forall x. (k x) `satisfies` (d++d) ==> (k x) `satisfies` d with
        lemma_satisfies (k x) d;
      assert (Inr fid `memP` (d++d));
      lemma_memP_append d d (Inr fid);
      assert (Inr fid `memP` d);
      ()
  end
  | Op l op arg k -> begin
      introduce forall x. (k x) `satisfies` (d++d) ==> (k x) `satisfies` d with
        lemma_satisfies (k x) d;
      assert (Inl l `memP` (d++d));
      lemma_memP_append d d (Inl l);
      assert (Inl l `memP` d);
      ()
  end

val user_handle (#a #b:_) (#sig:_) (#st:_) (#d0 #d1 : dirt) (#c1:squash (forall x. Inr x `memP` d0 ==> Inr x `memP` d1))
           ($f : mon sig st a d0)
           (v : a -> mon sig st b d1)
           (h : handler_tree #sig #st d0 b d1)
           : mon sig st b d1
let user_handle #a #b #sig #st #d0 #d1 #c1 f v h = 
  fold_with f v h (fun fid x ->
      (| mon sig st (st.get fid).b d1, scope fid x, (fun (t:mon sig st (st.get fid).b d1) k -> mon_bind t k) |))


(**
type store_mon (sig:signature) (d:dirt) = st:store{forall (i:nat). i < st.n ==> (forall x. (st.get i).m x (st.get i).b (st.get i).d == mon sig st (st.get i).b d)}
val handle_tree (#a #b:_) (#sig:_) (#d0 #d1 : dirt) (#st:store_mon sig d1) (#c1:squash (forall x. Inr x `memP` d0 ==> Inr x `memP` d1))
           ($f : mon sig st a d0)
           (v : a -> mon sig st b d0)
           : mon sig st b d0

let handle_tree #a #b #sig #d0 #d1 #st f v = 
  fold_with #a #(mon sig st b d0) #sig #st #d0 f v
    (fun l op arg k -> Op l op arg k)
    (fun fid x -> admit ())
//       (| mon sig st (st.get fid).b d0, handle_scope ((st.get fid).t x), (fun (t:mon sig st (st.get fid).b d0) k -> mon_bind t k) |))

assume val run_check : (#sig:_) -> (#st:_) -> (l:label_typ) -> (op:sig.act) -> (arg:sig.arg op) -> #d:dirt -> #b:Type -> mon sig st b d

and handle_scope #a #b #sig #d0 #d1 #(st:store_mon sig d0) (f:mon sig st a d1) : mon sig st a d0 =
  fold_with #a #(mon sig st a d0) #sig #st #d0 f (fun x -> mon_return x)
    (fun l op arg k -> mon_bind (run_check l op arg) k)
    (fun fid x -> handle_tree (
**)

assume val l_v : label_typ

type cb_typ5 = int -> mon io_sig empty_store int [Inl l_p]
type c_typ5 = cb:cb_typ5 -> mon io_sig (make_store cb) int [Inl l_c; Inr 0]

val ctx5 : c_typ5
let ctx5 cb =
  mon_bind (act l_c Write "Ctx") (fun () -> scope 0 5)

let st5' (cb:cb_typ5) = make_store cb
let st5 = (make_store #_ #st5' ctx5)

let handle_cb5 (cb:cb_typ5) (x:int) : mon io_sig st5 int [Inl l_p] = 
  fold_with #_ #(mon io_sig st5 int [Inl l_p]) #io_sig #empty_store #[Inl l_p] (cb x)
    (fun x -> mon_return x)
    (fun l op arg k -> mon_bind (act l op arg) k)
    (fun fid x -> match fid with)
  
let lemma_satisfies' (t:free 'sig 'st 'a) e2 e3 : Lemma (requires (t `satisfies` ([Inl e2]++[Inl e2;Inl e3]))) (ensures (t `satisfies` [Inl e2;Inl e3]))
  [SMTPat (t `satisfies` ([Inl e2]++[Inl e2;Inl e3]))] = admit ()

let handle_ctx5 (ctx:c_typ5) (cb:cb_typ5) : mon io_sig st5 int [Inl l_p; Inl l_v] =
  fold_with #_ #(mon io_sig st5 int [Inl l_p; Inl l_v]) #io_sig #(st5' cb) #[Inl l_c; Inr 0] (ctx cb)
    (fun x -> mon_return x)
    (fun l op arg k -> mon_bind (act l_v op arg) k)
    (fun fid x ->
      let cb' : mon io_sig st5 int [Inl l_p] = handle_cb5 (((st5' cb).get fid).t) x in
      (| mon io_sig st5 ((st5' cb).get fid).b [Inl l_p], cb', (fun t k -> mon_bind t k) |))

let handle_prog5 (prog : mon io_sig st5 int [Inl l_p; Inr 0]) : mon io_sig st5 int [Inl l_p; Inl l_v] = 
  fold_with #_ #(mon io_sig st5 int [Inl l_p; Inl l_v]) #io_sig #st5 #[Inl l_p; Inr 0] prog
    (fun x -> mon_return x)
    (fun l op arg k -> mon_bind (act l op arg) k)
    (fun fid x -> (| 
      mon io_sig st5 (st5.get fid).b [Inl l_p;Inl l_v],
      (handle_ctx5 (st5.get fid).t x),
      (fun t k -> mon_bind t k)
      |) )

val prog5 : c:c_typ5 -> mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0]
let prog5 c : mon io_sig (make_store #_ #(fun cb -> make_store cb) c) int [Inl l_p; Inr 0] =
  let cb : cb_typ5 = (fun x -> mon_bind (act l_p Write "Callback") (fun () -> mon_return (x+10))) in
  mon_bind (act l_p Write "Program") (fun () -> scope 0 cb)


let _ = assert (handle_prog5 (prog5 ctx5) == 
            Op l_p Write "Program" (fun _ ->
             (Op l_v Write "Ctx" (fun _ ->
                Op l_p Write "Callback" (fun _ -> Return 15))))) by (compute ())
