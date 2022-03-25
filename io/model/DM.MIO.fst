module DM.MIO

open FStar.Tactics
open ExtraTactics

open Common
open DMFree
open IO.Sig
open IO.Sig.Call
open DM.IO

(** MIO models a safe subset of OCaml.

    Differences between IO and MIO:
    1) IO is partial (has pre-conditions), MIO is not.
    2) In IO operations have specification while in MIO they do not have.
    3) 

Maybe it will be just better to use the old free monad with the IO cmds and no spec?
**)

let rec np_io (t:io 'a) =
  match t with
  | Return _ -> True
  | PartialCall _ _ -> False
  | Call cmd arg fnc -> forall r. np_io (fnc r)
  
let dm_mio a wp = m:(dm_io a wp){np_io m} 

val dm_mio_return : (a:Type) -> (x:a) -> dm_mio a (hist_return x)
let dm_mio_return a x = dm_io_return a x

let lemma_io_bind_np_io (#a #b:Type) #w1 #w2 (d1:dm_mio a w1) (d2:(x:a)-> dm_mio b (w2 x)) :
  Lemma (np_io (dm_io_bind _ _ _ _ d1 d2)) = admit ()  

val dm_mio_bind : 
      a: Type ->
      b: Type ->
      wp_v: hist a ->
      wp_f: (a -> hist b) ->
      v: dm_mio a wp_v ->
      f: (x: a -> dm_mio b (wp_f x))
    -> dm_mio b (hist_bind wp_v wp_f)
let dm_mio_bind a b wp_v wp_f v f = 
  let m:(dm_io b (hist_bind wp_v wp_f)) = dm_io_bind a b wp_v wp_f v f in
  lemma_io_bind_np_io v f;
  let m':dm_mio b (hist_bind wp_v wp_f) = m in
  m'

val dm_mio_subcomp :
  a: Type -> wp1: Hist.hist a -> wp2: Hist.hist a -> f: dm_mio a wp1
    -> Pure (dm_mio a wp2) (hist_ord wp2 wp1) (fun _ -> l_True)
let dm_mio_subcomp a wp1 wp2 f = dm_io_subcomp a wp1 wp2 f

val dm_mio_if_then_else : a:Type u#a -> wp1:hist a -> wp2:hist a -> f:dm_mio a wp1 -> g:dm_mio a wp2 -> bool -> Tot (Type u#(max 1 a))
let dm_mio_if_then_else a wp1 wp2 f g b = dm_io_if_then_else a wp1 wp2 f g b 

(** No lift from Pure to MIO because MIO is not partial **)

total
reifiable
reflectable
effect {
  MIOwp (a:Type) (wp : hist a) 
  with {
       repr       = dm_mio
     ; return     = dm_mio_return
     ; bind       = dm_mio_bind 
     ; subcomp    = dm_mio_subcomp
     ; if_then_else = dm_mio_if_then_else
     }
}

effect MIO (a:Type) = MIOwp a (fun p h -> forall lt r. p lt r)
