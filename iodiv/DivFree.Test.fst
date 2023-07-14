(** Definition of a monad with iter and requires *)

module DivFree.Test

open Util
open DivFree
open IIOSig

let body1 (fd:file_descr) : int -> m io_sig (either int string) = (fun i ->
    m_bind (m_call Read fd) (fun msg -> m_ret (Inl (i+1))))

let prog1 : m io_sig unit =
  m_bind #io_sig #file_descr #unit (m_call Openfile "test") (fun fd -> // (fun (fd:int) -> m_call Close fd)
    m_bind (m_iter (body1 fd) 0) (fun msg -> m_call Close fd)) 
  
type fin_trace = list event
type inf_trace = Stream.stream event

noeq
type orun a =
| Fin : tr:fin_trace -> v:a -> orun a
| Inf : inf_trace -> orun a

unfold
let i_pre = fin_trace -> Type0

unfold
let i_post a = orun a -> Type0

let i_pre_le (p q : i_pre) =
  forall hist. p hist ==> q hist

let i_post_le #a (p q : i_post a) =
  forall r. p r ==> q r

let i_post_eq #a (p q : i_post a) =
  p `i_post_le` q /\ q `i_post_le` p

let iwp' a = i_post a -> i_pre

let iwp_monotonic #a (w : iwp' a) =
  forall p q. p `i_post_le` q ==> w p `i_pre_le` w q

let iwp a =
  w : iwp' a { iwp_monotonic w }

let as_iwp #a (w : iwp' a) : Pure (iwp a) (requires iwp_monotonic w) (ensures fun r -> r == w) =
  w

let i_ret #a (x : a) : iwp a =
  as_iwp (fun post hist -> post (Fin [] x))

let trace (tr : orun 'a) : (match tr with | Fin _ _ -> fin_trace | Inf _ -> inf_trace) =
  match tr with
  | Fin tr _ -> tr
  | Inf tr -> tr

let result (tr : (orun 'a){Fin? tr}) : 'a =
  match tr with
  | Fin _ r -> r

let ishift_post #a (tr : fin_trace) (post : i_post a) : i_post a =
  fun r ->
    (Fin? r ==> post (Fin (tr @ trace r) (result r))) /\
    (Inf? r ==> post (Inf (Stream.stream_prepend tr (trace r))))

let i_bind_post #a #b (wf : a -> iwp b) (post : i_post b) hist : i_post a =
  fun r ->
    match r with
    | Fin tr x -> wf x (ishift_post tr post) (hist@tr)
    | Inf st -> post (Inf st)

let i_bind (#a : Type u#a) (#b : Type u#b) (w : iwp a) (wf : a -> iwp b) : iwp b =
  admit ();
  as_iwp (fun post hist ->
    w (i_bind_post wf post hist) hist
  )


type action_iwp (sg : signature) =
  ac : sg.act -> x : sg.arg ac -> iwp (sg.res x)

let i_unLift #a (w : iwp (liftType u#a a)) : iwp a =
  i_bind w (fun x -> i_ret (unLift x))

let i_req (pre : pure_pre) : iwp (squash pre) =
  as_iwp (fun post hist -> pre /\ post (Fin [] (Squash.get_proof pre)))

let i_tau : iwp unit =
  as_iwp (fun post hist -> post (Fin [ ETau ] ()))

unfold
let iter_expand_cont (#index : Type0) (#a : Type0) (k : index -> iwp a) (x : either index a) : iwp a =
  match x with
  | Inl j -> i_bind i_tau (fun _ -> k j)
  | Inr y -> i_ret y

let iter_expand (#index : Type0) (#a : Type0) (w : index -> iwp (either index a)) (i : index) (k : index -> iwp a) : iwp a =
  i_bind (w i) (iter_expand_cont k)

let ile #a (w w' : iwp a) =
  forall p. w' p `i_pre_le` w p

let rec i_iter (#index : Type0) (#a : Type0) (i : index) (w : index -> iwp (either index a)) : Tot (iwp a) (decreases j) =
  fun p h ->
    w i (fun r -> match r with
                | Fin lt (Inl j) -> (i_iter j w (fun r' -> p r') (h@lt))
                | Fin lt (Inr y) -> p r
                | Inf tr -> p r) h
  
let i_iter_lift (#index : Type0) (#a : Type0) (i:index) (w : index -> iwp (liftType u#a (either index a))) : iwp a =
  i_iter i (fun j -> i_unLift (w j))

let rec theta (#a : Type u#a) #sg (w_act : action_iwp sg) (c : m sg a) : iwp a =
  match c with
  | Ret x -> i_ret x
  | Req pre k -> i_bind (i_req pre) (fun x -> theta w_act (k x))
  | Call ac x k -> i_bind (w_act ac x) (fun x -> theta w_act (k x))
  | Iter i f k -> i_bind (i_iter_lift u#a i (fun i -> theta w_act (f i))) (fun x -> theta w_act (k x))

unfold
let iprepost #a (pre : fin_trace -> Type0) (post : (hist : fin_trace) -> orun a -> Pure Type0 (requires pre hist) (ensures fun _ -> True)) : iwp a =
  fun p hist -> pre hist /\ (forall r. post hist r ==> p r)

unfold
let i_open (s : string) : iwp int =
  iprepost (fun _ -> True) (fun hist r -> Fin? r /\ trace r == [ EOpenfile s (result r) ])

unfold
let i_read (fd : int) : iwp string =
  iprepost (fun hist -> True) (fun hist r -> Fin? r /\ trace r == [ ERead fd (result r) ])

unfold
let i_close (fd : int) : iwp unit =
  iprepost (fun hist -> True) (fun hist r -> Fin? r /\ trace r == [ EClose fd ])

unfold
let iodiv_act : action_iwp io_sig =
  fun ac arg ->
    match ac with
    | Openfile -> i_open arg
    | Read -> i_read arg
    | Close -> i_close arg

let th #a = theta #a #io_sig iodiv_act


open FStar.Tactics

let _ =
  assert (th #unit prog1 (fun _ -> True) []) by (
    norm [delta_only [`%prog1; `%th;`%m_call;`%m_bind]];
    dump "H")
