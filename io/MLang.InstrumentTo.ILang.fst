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

(** there is something in this calc that break including this file to ILang **)
let super_lemma 
  (pi:monitorable_prop)
  (m : iio (Universe.raise_t 'b))
  (d: dec_post #event)
  (k: 'b -> iio 'c)
  (p:hist_post 'c)
  (h:trace)
  (_:squash (dm_iio_theta (Decorated d m k) p h))
  (_:squash (forall h lt. d h lt ==> enforced_locally pi h lt)) :
  Lemma (
   dm_iio_theta m
      (fun lt r ->
        enforced_locally pi h lt /\
        dm_iio_theta (k (Universe.downgrade_val r))
          (hist_post_shift p lt)
          (apply_changes h lt)) h) = 
  calc (==>) {
      dm_iio_theta (Decorated d m k) p h;
      == {}
      DMFree.theta iio_wps (Decorated d m k) p h;
      == { _ by (
        norm [delta_only [`%DMFree.theta]; zeta]; 
        norm [delta_only [`%dm_iio_theta]; zeta]) }
      hist_bind
             (fun p h -> dm_iio_theta m (fun lt r -> d h lt /\ p lt r) h)
             (fun r -> dm_iio_theta (k (Universe.downgrade_val r))) p h;
      ==> {}
      hist_bind
             (fun p h -> dm_iio_theta m (fun lt r -> enforced_locally pi h lt /\ p lt r) h)
             (fun r -> dm_iio_theta (k (Universe.downgrade_val r))) p h;
      == { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind]]) }
      dm_iio_theta m
        (fun lt r ->
          enforced_locally pi h lt /\
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift p lt)
            (rev lt @ h)) h;
    }

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
  (k : 'b -> iio 'c)
  (p : hist_post 'c)
  (h:trace)
  (_:squash (special_tree pi (Decorated dec m k)))
  (_:squash (dm_iio_theta (Decorated dec m k) p h)) :
  IIO 
    (mio 'c pi * hist_post 'c * trace)
    (requires (fun h' -> h == h'))
    (ensures (fun h (z', p', h') lt ->
      h' == apply_changes h lt /\
      dm_iio_theta z' p' h' /\
      enforced_locally pi h lt /\
      z' << Decorated dec m k)) =
  super_lemma pi m dec k p h () ();
  let intP = (fun lt r ->
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift p lt)
            (apply_changes h lt)) in
  let theMHistPost : trace -> _ -> trace -> Type0 = (fun h r lt -> enforced_locally pi h lt /\ intP lt r) in
  let theMHist : hist _ = to_hist (fun h' -> h == h') theMHistPost in
  let theM : unit -> IIOwp _ theMHist = (fun () -> IIOwp?.reflect m) in
  let resM = theM () in 
  // this is an alternative to the previous two lines
  // let resM = IIOwp?.reflect (m <: dm_iio _ theMHist) in
  Classical.forall_intro (lemma_suffixOf_append h);
  let ltM = IIO.CompileTo.ILang.extract_local_trace h pi in
  Classical.forall_intro (Classical.move_requires (lemma_append_rev_inv_tail h ltM));
  assert (intP ltM resM);

  let z' = k (Universe.downgrade_val resM) in
  let p' = hist_post_shift p ltM in
  let h' = apply_changes h ltM in

  assert (dm_iio_theta z' p' h');

  (z', p', h')

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

    let inst_res : resexn (io_sig.res cmd argz) = IIO.Primitives.dynamic_cmd cmd d argz in
    match inst_res with
    (** the instrumentation failed, so we stop execution **)
    | Inr Contract_failure -> Inr Contract_failure
    (** instrumentation succeded and we continue **)
    | Inl rez -> begin
        let z' : iio (resexn 'a) = fnc rez in

        let ltM = IIO.CompileTo.ILang.extract_local_trace h pi in
        Classical.forall_intro (Classical.move_requires (lemma_append_rev_inv_tail h ltM));

        let p' : hist_post (resexn 'a) = hist_post_shift p ltM in
        let h' = apply_changes h ltM in
        assert (dm_iio_theta z' p' h');
        assert (z' << tree);
        _instrument pi z' p' h' () c_pi
    end
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
