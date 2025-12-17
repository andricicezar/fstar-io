module IO

(** we only have bools in STLC right now **)

(** I would like quotation to happen at the interface level
    and not at the representation level. I think this way
    one could produce code as close as the one written usin the
    do notation. **)

include BaseTypes
open Hist
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

val io_bind_equivalence #a #b (k k':a -> io b) (m:io a) (h:history) :
  Lemma (requires forall x. k x == k' x)
        (ensures forall p. theta (io_bind m k) h p == theta (io_bind m k') h p)

let return = io_return
let (let!@) = io_bind

val lem_theta_return #a (x:a) (h:history) (lt:local_trace h) :
  Lemma (requires lt == [])
        (ensures forall p. theta (return x) h p ==> p lt x)

val lem_theta_bind #a #b (m:io a) (h:history) (lt2:local_trace h) (fs_r_m:a) (k:a -> io b) (lt3:local_trace (h++lt2)) (fs_r:b) (lt:local_trace h) :
  Lemma (requires (forall (p:hist_post h a). theta m h p ==> p lt2 fs_r_m) /\
                  (forall (p':hist_post (h++lt2) b). theta (k fs_r_m) (h++lt2) p' ==> p' lt3 fs_r) /\
                  (lt == lt2 @ lt3))
        (ensures forall (p_:hist_post h b). theta (io_bind m k) h p_ ==> p_ lt fs_r)
// theta (io_bind m k) == pred transformer bind of (theta m) (fun x -> theta (k x))

val theta_history_independence #a (m:io a) (h:history) (lt:local_trace h) (fs_r:a) :
  Lemma (requires forall p. theta m h p ==> p lt fs_r)
        (ensures forall h' (lt':local_trace h') p'. theta m h' p' ==> p' lt' fs_r) // use steps e e' h lt and construct_local_trace

val theta_history_independence' (#a:Type) (m:io a) (h:history) (p:hist_post h a) :
  Lemma (requires theta m h p)
        (ensures forall h'. exists (p':hist_post h' a). (theta m h' p') /\
                 (forall (lt:local_trace h) (lt':local_trace h') r. (lt == lt') ==> (p lt r <==> p' lt' r)))

val post_condition_history_independence (#a:Type) (m:io a) (h h':history) (p:hist_post h a) (p':hist_post h' a) (lt':local_trace h') (r:a) :
  Lemma (requires theta m h p /\ theta m h' p' /\ p' lt' r)
        (ensures exists (lt:local_trace h). p lt r)
