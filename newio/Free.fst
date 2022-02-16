module Free

noeq
type op_sig (op:Type u#a) = {
  args : op -> Type u#a;
  res : op -> Type u#a;
}

noeq
type free (op:Type0) (s:op_sig op) (a:Type) : Type =
| Call : (l:op) -> s.args l -> cont:(s.res l -> free op s a) -> free op s a
| PartialCall : (pre:pure_pre) -> cont:((squash pre) -> free op s a) -> free op s a
| Return : a -> free op s a

let free_return (op:Type) (s:op_sig op) (a:Type) (x:a) : free op s a =
  Return x

let rec return_of (x:'a) (f:free 'op 's 'a) =
  match f with
  | Return x' -> x == x'
  | Call cmd arg k ->
     exists r'. return_of x (k r')
  | PartialCall pre k ->
     pre ==> return_of x (k ())

let rec free_bind
  (op:Type)
  (s:op_sig op)
  (a:Type)
  (b:Type)
  (l : free op s a)
  (k : a -> free op s b) :
  Tot (free op s b) =
  match l with
  | Return x -> k x
  | Call cmd args fnc ->
      Call cmd args (fun i ->
        free_bind op s a b (fnc i) k)
  | PartialCall pre fnc ->
      PartialCall pre (fun _ ->
        free_bind op s a b (fnc ()) k)

let free_map
  (op:Type)
  (s:op_sig op)
  (a:Type)
  (b:Type)
  (l : free op s a)
  (k : a -> b) :
  Tot (free op s b) =
  free_bind op s a b
    l (fun a -> free_return op s b (k a))

let free_codomain_ordering
  (#op:Type)
  (#s:op_sig op)
  (#a:Type)
  (x:(free op s a){Call? x}) :
  Lemma (forall r. Call?.cont x r << x) = ()

let add_sig
  (op:Type)
  (#p:op -> bool)
  (#q:op -> bool)
  (s1:op_sig (x:op{p x}))
  (s2:op_sig (x:op{q x})) :
  Tot (op_sig (y:op{p y || q y})) = {
    args = (fun (x:op{p x || q x}) -> if p x then s1.args x else s2.args x);
    res = (fun (x:op{p x || q x}) -> if p x then s1.res x else s2.res x)
 }
