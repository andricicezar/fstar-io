module Free

open Common

noeq
type cmd_sig (op:Type u#a) = {
  args:(op -> Type u#a);
  res:(op -> Type u#a);
}

noeq
type free (op:Type u#o) (s:cmd_sig op) (a:Type u#a) : Type u#(max o a) =
  | Call : (l:op) -> (s.args l) -> cont:(maybe (s.res l) -> (free op s a)) -> free op s a
  | Return : a -> free op s a
  // TODO: is this relevant? can be made a silent cmd
  | Throw : exn -> free op s a

let free_codomain_ordering (#op:Type) (#s:cmd_sig op) (#a:Type) (x:(free op s a){Call? x})
  : Lemma (forall r. Call?.cont x r << x)
  = ()



let free_return (op:Type) (s:cmd_sig op) (a:Type) (x:a)   : free op s a = Return x
let free_throw  (op:Type) (s:cmd_sig op) (a:Type) (x:exn) : free op s a = Throw x 

let rec free_bind (op:Type u#o) (s:cmd_sig op) (a:Type u#a) (b:Type u#b) (l : free op s a) (k : a -> free op s b) : free op s b =
  match l with
  | Return x -> k x 
  | Throw err -> Throw err 
  | Call cmd args fnc -> 
      Call cmd args (fun i ->
        free_bind op s a b (fnc i) k)

val lift_error : (#op:Type) -> (#s:cmd_sig op) -> (#a:Type) -> (maybe a) -> free op s a
let lift_error #op #s #a v =
  match v with
  | Inl x -> free_return op s a x
  | Inr err -> free_throw op s a err

val free_perform : (#op:Type) -> (#s:cmd_sig op) -> (#a:Type) -> free op s (maybe a) -> free op s a
let free_perform #op #s #a v = 
  free_bind op s (maybe a) (a) 
    v
    lift_error

let free_map (op:Type u#o) (s:cmd_sig op) (a:Type u#a) (b:Type u#b) (l : free op s a) (k : a -> b) : free op s b =
  free_bind op s a b 
    l (fun a -> free_return op s b (k a))
