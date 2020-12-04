module Free

open Common

noeq
type cmd_sig (op:Type u#a) = {
  args:(op -> Type u#a);
  res:(op -> Type u#a);
}

noeq
type freef op (s : cmd_sig op) a =
  | Call : (l:op) -> (s.args l) -> (maybe (s.res l) -> a) -> freef op s a

val freef_fmap : (#a:Type) -> (#b:Type) -> (#op:Type) -> (#s:cmd_sig op) ->
                m:freef op s a -> (x:a{x<<m} -> b) -> freef op s b
let freef_fmap #a #b #op #s m f=
  match m with
  | Call cmd args fnc -> Call cmd args (fun i -> FStar.WellFounded.axiom1 fnc i; f (fnc i))

noeq
type free (op:Type u#o) (s:cmd_sig op) (a:Type u#a) : Type u#(max o a) =
  | Cont : freef op s (free op s a) -> free op s a
  | Return : a -> free op s a
  // TODO: is this relevant? can be made a silent cmd
  | Throw : exn -> free op s a

let free_return (op:Type) (s:cmd_sig op) (a:Type) (x:a)   : free op s a = Return x
let free_throw  (op:Type) (s:cmd_sig op) (a:Type) (x:exn) : free op s a = Throw x 

let rec free_bind (op:Type u#o) (s:cmd_sig op) (a:Type u#a) (b:Type u#b) (l : free op s a) (k : a -> free op s b) : free op s b =
  match l with
  | Return x -> k x 
  | Throw err -> Throw err 
  | Cont t -> Cont (freef_fmap t (fun fnci ->
      free_bind op s a b fnci k))

val lift_error : (#op:Type) -> (#s:cmd_sig op) -> (#a:Type) -> (maybe a) -> free op s a
let lift_error #op #s #a v =
  match v with
  | Inl x -> free_return op s a x
  | Inr err -> free_throw op s a err

val free_perform : (#op:Type) -> (#s:cmd_sig op) -> (#a:Type) -> freef op s (maybe a) -> free op s a
let free_perform #op #s #a v = 
  free_bind op s (maybe a) (a) 
    (Cont (freef_fmap #(maybe a) #_ v Return))
    lift_error

let free_map (op:Type u#o) (s:cmd_sig op) (a:Type u#a) (b:Type u#b) (l : free op s a) (k : a -> b) : free op s b =
  free_bind op s a b 
    l (fun a -> free_return op s b (k a))
