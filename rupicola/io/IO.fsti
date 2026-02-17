module IO

(** we only have bools in STLC right now **)

(** I would like quotation to happen at the interface level
    and not at the representation level. I think this way
    one could produce code as close as the one written usin the
    do notation. **)

include BaseTypes
include Hist
open Trace

val io (a:Type u#a) : Type u#a

val io_return (#a:Type) (x:a) : io a

val io_bind
  (#a:Type u#a)
  (#b:Type u#b)
  (l : io a)
  (k : a -> io b) :
  io b

val openfile : string -> io (resexn file_descr)
val read : file_descr -> io (resexn string)
val write : file_descr * string -> io (resexn unit)
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
val lem_theta_open (arg:io_args OOpen) (res:io_res OOpen arg) (h:history) :
  Lemma (requires Inl? res ==> Inl?.v res == fresh_fd h)
        (ensures thetaP (openfile arg) h (ev_lt (EvOpen arg res)) res)

val destruct_thetaP_open (arg:io_args OOpen) (h:history) (lt:local_trace h) (fs_r:io_res OOpen arg) :
  Lemma (requires thetaP (openfile arg) h lt fs_r)
        (ensures (fs_r == Inl (fresh_fd h) /\ lt == [EvOpen arg (Inl (fresh_fd h))]) \/
                 (fs_r == Inr () /\ lt == [EvOpen arg (Inr ())]))

val lem_theta_read (arg:io_args ORead) (res:io_res ORead arg) (h:history) :
  Lemma (thetaP (read arg) h (ev_lt (EvRead arg res)) res)

val lem_theta_write (arg:io_args OWrite) (res:io_res OWrite arg) (h:history) :
  Lemma (thetaP (write arg) h (ev_lt (EvWrite arg res)) res)

val lem_theta_close (arg:io_args OClose) (res:io_res OClose arg) (h:history) :
  Lemma (thetaP (close arg) h (ev_lt (EvClose arg res)) res)

val destruct_thetaP_read (arg:io_args ORead) (h:history) (lt:local_trace h) (fs_r:io_res ORead arg) :
  Lemma (requires thetaP (read arg) h lt fs_r)
        (ensures lt == [EvRead arg fs_r])

val destruct_thetaP_write (arg:io_args OWrite) (h:history) (lt:local_trace h) (fs_r:io_res OWrite arg) :
  Lemma (requires thetaP (write arg) h lt fs_r)
        (ensures lt == [EvWrite arg fs_r])

val destruct_thetaP_close (arg:io_args OClose) (h:history) (lt:local_trace h) (fs_r:io_res OClose arg) :
  Lemma (requires thetaP (close arg) h lt fs_r)
        (ensures lt == [EvClose arg fs_r])

let lem_thetaP_return #a (x:a) (h:history) :
  Lemma (thetaP (return x) h [] x) =
  theta_monad_morphism_ret x

let lem_thetaP_bind #a #b (m:io a) (h:history) (lt1:local_trace h) (fs_r_m:a) (k:a -> io b) (lt2:local_trace (h++lt1)) (fs_r:b) :
  Lemma (requires thetaP m h lt1 fs_r_m /\
                  thetaP (k fs_r_m) (h++lt1) lt2 fs_r)
        (ensures thetaP (io_bind m k) h (lt1@lt2) fs_r)
        =
  wp2p_theta_bind m k;
  introduce forall (p:hist_post h b). hist_bind (theta m) (fun x -> theta (k x)) h p ==> p (lt1@lt2) fs_r with begin
    introduce _ ==> _ with _. begin
      assert (wp2p (theta (k fs_r_m)) (h++lt1) lt2 fs_r);
      assert (forall (p':hist_post (h++lt1) b). theta (k fs_r_m) (h++lt1) p' ==> p' lt2 fs_r);
      let p' : hist_post (h++lt1) b = fun lt r -> p (lt1@lt) r in
      assert (theta (k fs_r_m) (h++lt1) p' ==> p' lt2 fs_r);
      assert (p (lt1@lt2) fs_r)
    end
  end

val destruct_fs_beh #t1 #t2 (m:io t1) (k:t1 -> io t2) (h:history) (lt:local_trace h) (fs_r:t2) :
  Lemma
    (requires thetaP (io_bind m k) h lt fs_r)
    (ensures exists (lt1:local_trace h) (lt2:local_trace (h++lt1)) (fs_m:t1).
      lt == (lt1@lt2) /\
      thetaP m h lt1 fs_m /\
      thetaP (k fs_m) (h++lt1) lt2 fs_r)

