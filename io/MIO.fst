module MIO

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open Common
open DMFree
open IO.Sig
open IO.Sig.Call
open IIO

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is  in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)
let dm_mio_theta #a = dm_iio_theta #a 

let rec basic_free (x:free iio_cmds iio_sig 'dec 'a) : Type0 =
  match x with
  | Return _ -> True
  | Decorated _ _ _ -> False
  | PartialCall _ _ -> False
  | Call GetTrace _ _ -> False
  | Call cmd arg k ->
    forall res. basic_free (k res)

let dm_mio a wp = (x:(dm_iio a wp){basic_free x})

let dm_mio_return (a:Type) (x:a) : dm_mio a (hist_return x) =
  dm_return iio_cmds iio_sig event iio_wps a x

val dm_mio_bind  : 
  a: Type ->
  b: Type ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Prims.Tot (Hist.hist b)) ->
  v: dm_mio a wp_v ->
  f: (x: a -> Prims.Tot (dm_mio b (wp_f x))) ->
  Tot (dm_mio b (hist_bind wp_v wp_f))
let dm_mio_bind a b wp_v wp_f v f = 
  admit ();
  dm_bind iio_cmds iio_sig event iio_wps a b wp_v wp_f v f

val dm_mio_subcomp : 
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_mio a wp1 ->
  Pure (dm_mio a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_mio_subcomp a wp1 wp2 f = 
  dm_subcomp iio_cmds iio_sig event iio_wps a wp1 wp2 f

let dm_mio_if_then_else a wp1 wp2 f g b = dm_if_then_else iio_cmds iio_sig event iio_wps a wp1 wp2 f g b

total
reifiable
reflectable
effect {
  MIOwp (a:Type) (wp:hist a) 
  with {
       repr       = dm_mio
     ; return     = dm_mio_return
     ; bind       = dm_mio_bind 
     ; subcomp    = dm_mio_subcomp
     ; if_then_else = dm_mio_if_then_else
     }
}

effect MIO
  (a:Type) = MIOwp a (fun p h -> forall r lt . p lt r)

let lift_mio_iio (a:Type) (wp:hist a) (f:dm_mio a wp) :
  Tot (dm_iio a wp) =
  f

sub_effect MIOwp ~> IIOwp = lift_mio_iio
