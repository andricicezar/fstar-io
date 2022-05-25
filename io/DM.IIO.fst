module DM.IIO

open FStar.Tactics
open ExtraTactics
open FStar.Calc

open Common
open DM.IO
open DMFree
open IO.Sig
open IO.Sig.Call

(** The postcondition for an io computation is defined over the
result (type: a) and local trace (type: trace).
The local trace represents the events that happend during the
computation. Local trace is in chronological order.

We also have the history (type: trace) which represents the
events that happend until the beggining of the io computation.
The history is  in reverse chronology order.

At the end of an io computation, the local trace is appended
in reverse order to the history. **)
let dm_iio_theta #a = theta #a #iio_cmds #iio_sig #event iio_wps
  
let dm_iio = dm iio_cmds iio_sig event iio_wps
let dm_iio_return (a:Type) (x:a) : dm_iio a (hist_return x) =
  dm_return iio_cmds iio_sig event iio_wps a x

val dm_iio_bind  : 
  a: Type ->
  b: Type ->
  wp_v: Hist.hist a ->
  wp_f: (_: a -> Prims.Tot (Hist.hist b)) ->
  v: dm_iio a wp_v ->
  f: (x: a -> Prims.Tot (dm_iio b (wp_f x))) ->
  Tot (dm_iio b (hist_bind wp_v wp_f))
let dm_iio_bind a b wp_v wp_f v f = dm_bind iio_cmds iio_sig event iio_wps a b wp_v wp_f v f

val dm_iio_subcomp : 
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_iio a wp1 ->
  Pure (dm_iio a wp2) (hist_ord wp2 wp1) (fun _ -> True)
let dm_iio_subcomp a wp1 wp2 f = dm_subcomp iio_cmds iio_sig event iio_wps a wp1 wp2 f

val dm_if_then_else :
  a: Type ->
  wp1: hist a ->
  wp2: hist a ->
  f: dm_iio a wp1 ->
  g: dm_iio a wp2 ->
  b: bool ->
  Tot Type
let dm_iio_if_then_else a wp1 wp2 f g b = dm_if_then_else iio_cmds iio_sig event iio_wps a wp1 wp2 f g b

val lift_pure_dm_iio :
  a: Type ->
  w: pure_wp a ->
  f: (_: eqtype_as_type unit -> Prims.PURE a w) ->
  Tot (dm_iio a (wp_lift_pure_hist w))
let lift_pure_dm_iio a w f = lift_pure_dm iio_cmds iio_sig event iio_wps a w f


total
reifiable
reflectable
effect {
  IIOwp (a:Type) (wp : hist a) 
  with {
       repr       = dm_iio
     ; return     = dm_iio_return
     ; bind       = dm_iio_bind 
     ; subcomp    = dm_iio_subcomp
     ; if_then_else = dm_iio_if_then_else
     }
}

effect IIO
  (a:Type)
  (pre : trace -> Type0)
  (post : trace -> a -> trace -> Type0) =
  IIOwp a (to_hist pre post) 

sub_effect PURE ~> IIOwp = lift_pure_dm_iio

(** This is a identity function, and we need it because
F* does not have depth subtyping on inductives. **)
let rec cast_io_iio #a (x:io a) : iio a =
  match x with
  | Return z -> Return z
  | Call (cmd:io_cmds) args fnc ->
     Call cmd args (fun res -> cast_io_iio (fnc res))
  | PartialCall pre fnc ->
     PartialCall pre (fun res -> cast_io_iio (fnc res))
  | Decorated d m fnc ->
     Decorated d (cast_io_iio m) (fun res -> cast_io_iio (fnc res))

let rec lemma_cast_io_iio #a (m:io a) :
  Lemma
    (dm_io_theta m `hist_ord` dm_iio_theta (cast_io_iio m)) = 
  match m with
  | Return _ -> ()
  | PartialCall pre k ->begin
    let fst : squash pre -> hist a = fun r -> dm_io_theta (k r) in
    let snd : squash pre -> hist a = fun r -> dm_iio_theta (cast_io_iio (k r)) in
    calc (==) {
      dm_io_theta m;
      == {}
      dm_io_theta (PartialCall pre k);
      == { _ by (norm [delta_only [`%dm_io_theta;`%theta]; zeta; iota]) } // unfold theta
      hist_bind (partial_call_wp pre) (fun r -> dm_io_theta (k r));
      == {}
      hist_bind (partial_call_wp pre) fst;
    };
    (** fst ==> snd /\ hist is monotonic **)
    introduce forall (p:hist_post a) h. hist_bind (partial_call_wp pre) fst p h ==> hist_bind (partial_call_wp pre) snd p h with begin 
      introduce forall (r:squash pre). (fst r `hist_ord` snd r) with begin
        lemma_cast_io_iio (k r)
      end
    end;
    calc (==) {
      hist_bind (partial_call_wp pre) snd;
      == {}
      hist_bind (partial_call_wp pre) (fun r -> dm_iio_theta (cast_io_iio (k r)));
      == { _ by (norm [delta_only [`%dm_iio_theta;`%theta]; zeta; iota]) }
      dm_iio_theta (PartialCall pre (fun r -> cast_io_iio (k r)));
      == { _ by (compute ()) }
      dm_iio_theta (cast_io_iio (PartialCall pre k));
      == {}
      dm_iio_theta (cast_io_iio m);
    }
  end
  | Call (cmd:io_cmds) arg k -> begin
    let fst : io_sig.res cmd arg -> hist a = fun r -> dm_io_theta (k r) in
    let snd : iio_sig.res cmd arg -> hist a = fun r -> dm_iio_theta (cast_io_iio (k r)) in
    calc (==) {
      dm_io_theta m;
      == {}
      dm_io_theta (Call cmd arg k);
      == { _ by (norm [delta_only [`%dm_io_theta;`%theta]; zeta; iota]) } // unfold theta
      hist_bind (iio_wps cmd arg) (fun r -> dm_io_theta (k r));
      == {}
      hist_bind (iio_wps cmd arg) fst;
    };
    (** fst ==> snd /\ hist is monotonic **)
    introduce forall (p:hist_post a) h. hist_bind (iio_wps cmd arg) fst p h ==> hist_bind (iio_wps cmd arg) snd p h with begin 
      introduce forall (r:iio_sig.res cmd arg). (fst r `hist_ord` snd r) with begin
        lemma_cast_io_iio (k r)
      end
    end;
    calc (==) {
      hist_bind (iio_wps cmd arg) snd;
      == {}
      hist_bind (iio_wps cmd arg) (fun r -> dm_iio_theta (cast_io_iio (k r)));
      == { _ by (norm [delta_only [`%dm_iio_theta;`%theta]; zeta; iota]) }
      dm_iio_theta (Call cmd arg (fun r -> cast_io_iio (k r)));
      == { _ by (compute ()) }
      dm_iio_theta (cast_io_iio (Call cmd arg k));
      == {}
      dm_iio_theta (cast_io_iio m);
    }
  end
  | Decorated _ _ _ -> admit ()

let lemma_cast_io_iio_2 #a (x:io a) (wp:hist a) :
  Lemma
    (requires (wp `hist_ord` DM.IO.dm_io_theta x))
    (ensures (wp `hist_ord` dm_iio_theta (cast_io_iio x))) =
  lemma_cast_io_iio x

let lift_io_iio (a:Type) (wp:hist a) (f:DM.IO.dm_io a wp) :
  Tot (dm_iio a wp) =
  lemma_cast_io_iio_2 f wp;
  cast_io_iio f

sub_effect DM.IO.IOwp ~> IIOwp = lift_io_iio


let get_trace () : IIOwp trace
  (fun p h -> forall lt. lt == [] ==> p lt h) =
  IIOwp?.reflect (iio_call GetTrace ())
