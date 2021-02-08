module Free

noeq
type cmd_sig (op:Type u#a) = {
  args:(op -> Type u#a);
  res:(op -> Type u#a);
}

let add_sig
  (cmds:Type)
  (#p:cmds -> bool)
  (#q:cmds -> bool)
  (s1:cmd_sig (x:cmds{p x}))
  (s2:cmd_sig (x:cmds{q x})) :
  Tot (cmd_sig (y:cmds{p y || q y})) = {
    args = (fun (x:cmds{p x || q x}) -> if p x then s1.args x else s2.args x);
    res = (fun (x:cmds{p x || q x}) -> if p x then s1.res x else s2.res x)
  }

noeq
type free (op:Type u#o) (s:cmd_sig op) (a:Type u#a) : Type u#(max o a) =
  | Call : (l:op) -> (s.args l) -> cont:(s.res l -> (free op s a)) -> free op s a
  | Return : a -> free op s a

let free_codomain_ordering
  (#op:Type)
  (#s:cmd_sig op)
  (#a:Type)
  (x:(free op s a){Call? x}) :
  Lemma (forall r. Call?.cont x r << x) = ()

let free_return (op:Type) (s:cmd_sig op) (a:Type) (x:a) : free op s a =
  Return x

let rec free_bind
  (op:Type u#o)
  (s:cmd_sig op)
  (a:Type u#a)
  (b:Type u#b)
  (l : free op s a)
  (k : a -> free op s b) :
  Tot (free op s b) =
  match l with
  | Return x -> k x
  | Call cmd args fnc ->
      Call cmd args (fun i ->
        free_bind op s a b (fnc i) k)

let free_map
  (op:Type u#o)
  (s:cmd_sig op)
  (a:Type u#a)
  (b:Type u#b)
  (l : free op s a)
  (k : a -> b) :
  Tot (free op s b) =
  free_bind op s a b
    l (fun a -> free_return op s b (k a))
