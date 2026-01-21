module IO

(** we only have bools in STLC right now **)

(** I would like quotation to happen at the interface level
    and not at the representation level. I think this way
    one could produce code as close as the one written usin the
    do notation. **)

include BaseTypes
include Hist
open Trace
open FStar.List.Tot
open STLC

val io (a:Type u#a) : Type u#a

val io_return (#a:Type) (x:a) : io a

val io_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : io a)
  (k : a -> io b) :
  io b

val read () : io (resexn bool)
val write (x:bool) : io (resexn unit)

let return = io_return
let (let!@) = io_bind

val theta : #a:Type -> io a -> hist a

val theta_monad_morphism_ret (x:'a) :
  Lemma (theta (return x) == hist_return x)

val theta_monad_morphism_bind (m:io 'a) (k:'a -> io 'b) :
  Lemma (theta (io_bind m k) `hist_equiv` hist_bind (theta m) (fun x -> theta (k x)))

val wp2p_theta_bind (m:io 'a) (k:'a -> io 'b) :
  Lemma (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h
         `hist_post_equiv`
         wp2p (theta (io_bind m k)) h)

val io_bind_equivalence #a #b (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k'))

let lem_theta_return #a (x:a) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [])
        (ensures wp2p (theta (return x)) h lt x) =
  theta_monad_morphism_ret x

let lem_theta_bind #a #b (m:io a) (h:history) (lt2:local_trace h) (fs_r_m:a) (k:a -> io b) (lt3:local_trace (h++lt2)) (fs_r:b) (lt:local_trace h) :
  Lemma (requires wp2p (theta m) h lt2 fs_r_m /\
                  wp2p (theta (k fs_r_m)) (h++lt2) lt3 fs_r /\
                  (lt == lt2 @ lt3))
        (ensures wp2p (theta (io_bind m k)) h lt fs_r) = admit ()
  //wp2p_theta_bind m k

val lem_theta_read (x:io_res ORead ()) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [EvRead () x])
        (ensures wp2p (theta (read ())) h lt x)

val lem_theta_write (b:bool) (x:io_res OWrite b) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [EvWrite b x])
        (ensures wp2p (theta (write b)) h lt x)

val get_lt (h h':history) (lt:local_trace h) : Tot (local_trace h') 

val theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r)
        (ensures wp2p (theta m) h' (get_lt h h' lt) fs_r) 

(*val theta_monotonic_hist #a #e #e' #h' #lt' (m:io a) (st:steps e e' h' lt') :
  Lemma (forall h h' (p':hist_post h' a). theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st*) 

(*val theta_history_independence #a #e #e' (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) (st':steps e e' h' lt') (st:steps e e' h lt) :
  Lemma (requires wp2p (theta m) h (construct_local_trace st' h) fs_r)
        (ensures wp2p (theta m) h' (construct_local_trace st h') fs_r)*)

(*let same_shape #h #h' (lt:local_trace h) (lt':local_trace h') : Type0 = lt == lt'

val get_lt (h h':history) (lt:local_trace h) : (lt':local_trace h'{same_shape lt lt'})*)
