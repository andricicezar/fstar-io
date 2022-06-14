module MLang.InstrumentTo.ILang

open FStar.List.Tot
open FStar.Tactics

open Common
open TC.Checkable
open TC.Monitorable.Hist
open IO.Sig
open IIO
open MLang
open ILang

let mio a pi = x:(iio a){special_tree pi x} 

let super_lemma 
  (pi:monitorable_prop)
  (m : iio (Universe.raise_t 'b))
  d
  k
  p
  (h:trace)
  (_:squash (dm_iio_theta (Decorated d m k) p h))
  (_:squash (forall h lt. d h lt ==> enforced_locally pi h lt)) :
  Lemma (
   dm_iio_theta m (fun lt r -> enforced_locally pi h lt) h /\
   dm_iio_theta m
      (fun lt r ->
        dm_iio_theta (k (Universe.downgrade_val r))
          (hist_post_shift p lt)
          (apply_changes h lt)) h) = admit ()
 (** 
  calc (==>) {
      dm_iio_theta (Decorated d m k) p h;
      ==> { _ by (
            binder_retype (nth_binder (-1));
            norm [delta_only [`%dm_iio_theta;`%DMFree.theta]; zeta];
            trefl ();
            norm [delta_only [`%dm_iio_theta]];
            assumption ()) }
      hist_bind
             (fun p h -> dm_iio_theta m (fun lt r -> d h lt /\ p lt r) h)
             (fun r -> dm_iio_theta (k (Universe.downgrade_val r))) p h;
      ==> {}
      hist_bind
             (fun p h -> dm_iio_theta m (fun lt r -> enforced_locally pi h lt /\ p lt r) h)
             (fun r -> dm_iio_theta (k (Universe.downgrade_val r))) p h;
      ==> { _ by (binder_retype (nth_binder (-1));
                  norm [delta_only [`%hist_bind;`%hist_post_bind]]; trefl (); assumption ()) }
      dm_iio_theta m
        (fun lt r ->
          enforced_locally pi h lt /\
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift p lt)
            (List.Tot.Base.rev lt @ h)) h;
      ==> {}
      dm_iio_theta m
        (fun lt r ->
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift p lt)
            (List.Tot.Base.rev lt @ h)) h;
    }

**) 

let lemma_smt_pat (pi:monitorable_prop) (h lt1 lt2:trace) :
  Lemma (requires (
    enforced_locally pi h lt1 /\
    enforced_locally pi (apply_changes h lt1) lt2))
    (ensures (
    enforced_locally pi h (lt1 @ lt2))) [SMTPat (enforced_locally pi h (lt1@lt2))] = (** not urgent **) admit ()

let run_m
  (pi:monitorable_prop)
  (m : iio (Universe.raise_t 'b))
  (dec : dec_post)
  (k : 'b -> iio (resexn 'c))
  (p : hist_post (resexn 'c))
  (h:trace)
  (_:squash (special_tree pi (Decorated dec m k)))
  (_:squash (dm_iio_theta (Decorated dec m k) p h)) :
  IIO 
    (mio (resexn 'c) pi * hist_post (resexn 'c) * trace)
    (requires (fun h' -> h == h'))
    (ensures (fun h (z', p', h') lt ->
      h' == apply_changes h lt /\
      dm_iio_theta z' p' h' /\
      enforced_locally pi h lt /\
      z' << Decorated dec m k)) =
  assert (forall h lt. dec h lt ==> enforced_locally pi h lt);
  super_lemma pi m dec k p h () ();
  let theMHistPost : trace -> _ -> trace -> Type0 = (fun h r lt -> enforced_locally pi h lt) in
  let theMHist : hist _ = to_hist (fun h' -> h == h') theMHistPost in
  let theM : unit -> IIOwp _ theMHist = (fun () -> IIOwp?.reflect m) in
  let resM = theM () in 
  Classical.forall_intro (lemma_suffixOf_append h);
  let ltM = IIO.CompileTo.ILang.extract_local_trace h pi in

  let z' = k (Universe.downgrade_val resM) in
  assert (dm_iio_theta m (fun lt r -> theMHistPost h r lt) h);
  assert (dm_iio_theta m
        (fun lt r ->
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift p lt)
            (apply_changes h lt)) h);

 // assert (theMHist `hist_ord` dm_iio_theta m);
  //assert (p lt res);
  let p' = hist_post_shift p ltM in
  let h' = apply_changes h ltM in
  (** urgent - it is urgent because I am not confident it can be proved **)
  assume (dm_iio_theta z' p' h');
  (z', p', h')

(** not urgent assume **)
assume val dynamic_cmd :
  (cmd : io_cmds) ->
  (d1 : checkable2 (io_pre cmd)) ->
  (arg : io_sig.args cmd) ->
  IIOwp (io_resm cmd)
    (fun p h ->
      (forall (r:(io_sig.res cmd arg)) lt.
        (match r with
         | Inr Contract_failure -> ~(d1.check2 arg h) /\ lt == []
         | _ -> d1.check2 arg h /\ lt == [convert_call_to_event cmd arg r]) ==> p lt r))

(** this is working but needs more help to verify **)
let rec _instrument
  (pi   : monitorable_prop)
  (tree : mio (resexn 'a) pi)
  (p    : hist_post (resexn 'a))
  (h    : trace)
  (d1   : squash (dm_iio_theta tree p h))
  (c_pi : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOwp (resexn 'a) (fun p h' -> h == h' /\ (forall lt r. enforced_locally pi h lt ==> p lt r)) =
  match tree with
  | Return r -> r
  | Decorated d #b m k ->
    let (z', p', h') = run_m pi m d k p h () d1 in
    assert (z' << tree);
    _instrument pi z' p' h' () c_pi
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace (pi cmd) (io_pre cmd) c_pi) in
    (** Check if the runtime check failed, and if yes, return the error **)
    let rez = dynamic_cmd cmd d argz in
    let z' : iio (resexn 'a) = fnc rez in

    let ltM = IIO.CompileTo.ILang.extract_local_trace h pi in

    let p' : hist_post (resexn 'a) = hist_post_shift p ltM in
    let h' = apply_changes h ltM in
    assume (dm_iio_theta z' p' h');
    assert (z' << tree);
    _instrument pi z' p' h' () c_pi
  end

let instrument_mio
  (pi   : monitorable_prop)
  (tree : mio (resexn 'a) pi)
  (_    : squash (trivial_hist `hist_ord` dm_iio_theta tree))
  (c_pi : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) pi = 
  let p = fun _ _ -> True in
  let h = get_trace () in
  _instrument pi tree p h () c_pi
