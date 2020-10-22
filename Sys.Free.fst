module Sys.Free

open Common

noeq
type cmd_sig (op:Type u#a) = {
  args:(op -> Type u#a);
  res:(op -> Type u#a);
}

// #push-options "--__temp_no_proj Sys.Free"
  
noeq
type sysf op (s : cmd_sig op) a =
  | Call : (l:op) -> (s.args l) -> (maybe (s.res l) -> a) -> sysf op s a

// #pop-options

val sysf_fmap : (#a:Type) -> (#b:Type) -> (#op:Type) -> (#s:cmd_sig op) ->
                m:sysf op s a -> (x:a{x<<m} -> b) -> sysf op s b
let sysf_fmap #a #b #op #s m f=
  match m with
  | Call cmd args fnc -> Call cmd args (fun i -> FStar.WellFounded.axiom1 fnc i; f (fnc i))

noeq
type sys (op:Type u#o) (s:cmd_sig op) (a:Type u#a) : Type u#(max o a) =
  | Cont : sysf op s (sys op s a) -> sys op s a
  | Return : a -> sys op s a
  | Throw : exn -> sys op s a

let sys_return (op:Type) (s:cmd_sig op) (a:Type) (x:a)   : sys op s a = Return x
let sys_throw  (op:Type) (s:cmd_sig op) (a:Type) (x:exn) : sys op s a = Throw x 

let rec sys_bind (op:Type u#o) (s:cmd_sig op) (a:Type u#a) (b:Type u#b) (l : sys op s a) (k : a -> sys op s b) : sys op s b =
  match l with
  | Return x -> k x 
  | Throw err -> Throw err 
  | Cont t -> Cont (sysf_fmap t (fun fnci ->
      sys_bind op s a b fnci k))

val lift_error : (#op:Type) -> (#s:cmd_sig op) -> (#a:Type) -> (maybe a) -> sys op s a
let lift_error #op #s #a v =
  match v with
  | Inl x -> sys_return op s a x
  | Inr err -> sys_throw op s a err

val sys_perform : (#op:Type) -> (#s:cmd_sig op) -> (#a:Type) -> sysf op s (maybe a) -> sys op s a
let sys_perform #op #s #a v = 
  sys_bind op s (maybe a) (a) 
    (Cont (sysf_fmap #(maybe a) #_ v Return))
    lift_error

let sys_map (op:Type u#o) (s:cmd_sig op) (a:Type u#a) (b:Type u#b) (l : sys op s a) (k : a -> b) : sys op s b =
  sys_bind op s a b 
    l (fun a -> sys_return op s b (k a))
