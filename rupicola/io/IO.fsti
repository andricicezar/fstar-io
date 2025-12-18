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

val theta : #a:Type -> io a -> hist a

val io_bind_equivalence #a #b (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k'))

let return = io_return
let (let!@) = io_bind

val lem_theta_return #a (x:a) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [])
        (ensures wp2p (theta (return x)) h lt x)

val lem_theta_bind #a #b (m:io a) (h:history) (lt2:local_trace h) (fs_r_m:a) (k:a -> io b) (lt3:local_trace (h++lt2)) (fs_r:b) (lt:local_trace h) :
  Lemma (requires wp2p (theta m) h lt2 fs_r_m /\
                  wp2p (theta (k fs_r_m)) (h++lt2) lt3 fs_r /\
                  (lt == lt2 @ lt3))
        (ensures wp2p (theta (io_bind m k)) h lt fs_r)
// theta (io_bind m k) == pred transformer bind of (theta m) (fun x -> theta (k x))

val theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) :
  Lemma (requires wp2p (theta m) h lt fs_r) 
        (ensures wp2p (theta m) h' lt' fs_r) 
        // use steps e e' h lt and construct_local_trace
