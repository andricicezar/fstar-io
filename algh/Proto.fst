module Proto

#reset-options

noeq
type signature = {
  act : Type0 ;
  arg : a:act -> Type0 ;
  res : #a:act -> arg a -> Type0 ;
}

type io_act =
| Read
| Write

let io_arg ac =
  match ac with
  | Read -> unit 
  | Write -> string

let io_res #ac (x : io_arg ac) =
  match ac with
  | Read -> string
  | Write -> unit

let io_sig : signature = {
  act = io_act ;
  arg = io_arg ;
  res = io_res
}

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

let rec (<=) (d1 d2:dirt) : Type0 =
  match d1 with
  | [] -> true
  | h :: tl -> memP h d2 /\ tl <= d2


(**[@"opaque_to_smt"]
let downgrade_f (#a:Type u#0) (#b:Type u#0) (f:a -> free 's 'st b) : (a -> free 's (Universe.raise_t u#0 u#a b)) =
  fun x -> free_bind (f x) (fun x -> Return (Universe.raise_val u#0 u#a x))**)

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

let scope (#st:store) (fid:fid_typ{fid < st.n}) (arg:(st.get fid).a) : mon io_sig st (st.get fid).b [Inr fid] =
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
let prog4' c =
  mon_bind (scope 0 ()) (fun (cb:cb_typ4) -> cb ())
