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

val openfile : bool -> io (resexn file_descr)
val read : file_descr -> io (resexn bool)
val write : file_descr * bool -> io (resexn unit)
val close : file_descr -> io (resexn unit)

let return = io_return
let (let!@) = io_bind

val theta : #a:Type -> io a -> hist a

val theta_monad_morphism_ret (x:'a) :
  Lemma (theta (return x) == hist_return x)

val theta_monad_morphism_bind (m:io 'a) (k:'a -> io 'b) :
  Lemma (theta (io_bind m k) `hist_equiv` hist_bind (theta m) (fun x -> theta (k x)))

val io_bind_equivalence #a #b (k k':a -> io b) (m:io a) :
  Lemma (requires forall x. k x == k' x)
        (ensures theta (io_bind m k) `hist_equiv` theta (io_bind m k'))

let thetaP m = wp2p (theta m)

val wp2p_theta_bind (m:io 'a) (k:'a -> io 'b) :
  Lemma (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h (** Kind of ugly. Can we use hist_post_bind? **)
         `hist_post_equiv`
         thetaP (io_bind m k) h)

(** Cezar: Trying to connect with hist_post_bind. Does not look like it holds.
let lem_thetaP_bind #a #b (m:io a) (k:a -> io b) :
  Lemma (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h
        `hist_post_equiv`
         hist_post_bind (thetaP m h) (fun lt r -> thetaP (k r) (h++lt))) =
  assert (forall h.
         wp2p (hist_bind (theta m) (fun x -> theta (k x))) h
        `hist_post_equiv`
         hist_post_bind (thetaP m h) (fun lt r -> thetaP (k r) (h++lt))) by (
         norm [delta_only [`%hist_post_bind; `%thetaP; `%hist_bind; `%wp2p;
         `%hist_post_bind'; `%hist_post_shift;`%hist_post_equiv;`%hist_post_ord]; iota];
         let h = forall_intro () in
         split ();
         dump "H")
**)

val lem_theta_read (arg:io_args ORead) (res:io_res ORead arg) (h:history) :
  Lemma (thetaP (read arg) h [EvRead arg res] res)

val lem_theta_write (arg:io_args OWrite) (res:io_res OWrite arg) (h:history) :
  Lemma (thetaP (write arg) h [EvWrite arg res] res)

let thetaP_monad_morphism_return #a (x:a) (h:history) :
  Lemma (thetaP (return x) h [] x) =
  theta_monad_morphism_ret x

open FStar.Tactics

let lem_thetaP_bind #a #b (m:io a) (h:history) (lt1:local_trace h) (fs_r_m:a) (k:a -> io b) (lt2:local_trace (h++lt1)) (fs_r:b) :
  Lemma (requires thetaP m h lt1 fs_r_m /\
                  thetaP (k fs_r_m) (h++lt1) lt2 fs_r)
        (ensures thetaP (io_bind m k) h (lt1@lt2) fs_r) =
  assume (wp2p (hist_bind (theta m) (fun x -> theta (k x))) h (lt1@lt2) fs_r);
  wp2p_theta_bind m k

(**
val get_lt (h h':history) (lt:local_trace h) : Tot (local_trace h')

val theta_history_independence #a (m:io a) (h h':history) (lt:local_trace h) (fs_r:a) :
  Lemma (requires thetaP m h lt fs_r)
        (ensures thetaP m h' (get_lt h h' lt) fs_r)**)
  //(requires thetaP m) h (get_lt h' h lt') fs_r)
  //(ensures thetaP m) h' lt' fs_r)
  //      (ensures thetaP m) h' (get_lt h h' lt) fs_r)

(*val theta_monotonic_hist #a #e #e' #h' #lt' (m:io a) (st:steps e e' h' lt') :
  Lemma (forall h h' (p':hist_post h' a). theta m h' p' ==> theta m h (fun lt res -> p' (construct_local_trace st*)

(*val theta_history_independence #a #e #e' (m:io a) (h h':history) (lt:local_trace h) (lt':local_trace h') (fs_r:a) (st':steps e e' h' lt') (st:steps e e' h lt) :
  Lemma (requires thetaP m) h (construct_local_trace st' h) fs_r)
        (ensures thetaP m) h' (construct_local_trace st h') fs_r)*)

(*let same_shape #h #h' (lt:local_trace h) (lt':local_trace h') : Type0 = lt == lt'

val get_lt (h h':history) (lt:local_trace h) : (lt':local_trace h'{same_shape lt lt'})*)
