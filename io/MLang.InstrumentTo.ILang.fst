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

(**
Things we tried:
1) we can not index this by h because in the Decorated case
   we don't have the local trace of m to be able to accumulate **)
let rec instrumentable_tree
  (pi : monitorable_prop)
  (tree : iio 'a) : Type0 =
  match tree with
  | Return _ -> True
  | PartialCall _ k -> forall res. instrumentable_tree pi (k res)
  | Call GetTrace arg k -> forall h. instrumentable_tree pi (k h)
  | Call cmd arg k -> forall res. instrumentable_tree pi (k res)
  | Decorated dec m k ->
    (forall h lt. dec h lt ==> enforced_locally pi h lt) /\
    (forall res. instrumentable_tree pi (k res))

let lemma_decoration_implies_pi 
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
    enforced_locally pi h (lt1 @ lt2))) [SMTPat (enforced_locally pi h (lt1@lt2))] =
    (** not urgent **) admit ()

let run_m
  (pi:monitorable_prop)
  (m : iio (Universe.raise_t 'b))
  (dec : dec_post)
  (k : 'b -> iio 'c)
  (p : hist_post 'c)
  (h:trace)
  (_:squash (instrumentable_tree pi (Decorated dec m k)))
  (_:squash (dm_iio_theta (Decorated dec m k) p h)) :
  IIO 
    (iio 'c * hist_post 'c * trace)
    (requires (fun h' -> h == h'))
    (ensures (fun h (z', p', h') lt ->
      h' == apply_changes h lt /\
      instrumentable_tree pi z' /\
      dm_iio_theta z' p' h' /\
      enforced_locally pi h lt /\
      z' << Decorated dec m k)) =
  lemma_decoration_implies_pi pi m dec k p h () ();
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

#set-options "--z3rlimit 10 --fuel 10 --z3seed 10 --quake 1/5"
let rec _instrument
  (pi   : monitorable_prop)
  (tree : iio (resexn 'a))
  (p    : hist_post (resexn 'a))
  (h    : trace)
  (d1   : squash (dm_iio_theta tree p h))
  (d2   : squash (instrumentable_tree pi tree))
  (c_pi : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOwp (resexn 'a) (fun p' h' -> h == h' /\ (forall lt r. enforced_locally pi h lt ==> p' lt r)) =
  match tree with
  | Return r -> r
  | PartialCall pre k -> 
    let z' = k () in
    let p' : hist_post (resexn 'a) = hist_post_shift p [] in
    let h' = apply_changes h [] in
    _instrument pi z' p' h' () () c_pi
  | Call GetTrace argz k -> 
    let z' = k h in
    let p' : hist_post (resexn 'a) = hist_post_shift p [] in
    let h' = apply_changes h [] in
    _instrument pi z' p' h' () () c_pi
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
      _instrument pi z' p' h' () () c_pi
    end
  end 
  | Decorated d #b m k ->
    let (z', p', h') = run_m pi m d k p h () d1 in
    assert (z' << tree);
    _instrument pi z' p' h' () () c_pi
#reset-options

let instrument_instrumentable
  (tree : iio (resexn 'a))
  (pi   : monitorable_prop)
  (#_    : squash (instrumentable_tree pi tree))
  (#_    : squash (forall h. dm_iio_theta tree (fun _ _ -> True) h))
  (#c_pi : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) pi = 
  let p = fun _ _ -> True in
  let h = get_trace () in
  _instrument pi tree p h () () c_pi

let rec lemma_mio_tree_implies_instrumentable_tree (pi:monitorable_prop) (tree:iio 'a) :
  Lemma
    (requires (special_tree pi tree))
    (ensures (instrumentable_tree pi tree)) = 
    match tree with
    | Return _ -> ()
    | PartialCall _ _ -> ()
    | Call GetTrace _ _ -> ()
    | Call cmd arg k -> 
       introduce forall res. special_tree pi (k res) ==> instrumentable_tree pi (k res) with begin
         lemma_mio_tree_implies_instrumentable_tree pi (k res)
       end
    | Decorated dec m k -> 
       introduce forall res. special_tree pi (k res) ==> instrumentable_tree pi (k res) with begin
         lemma_mio_tree_implies_instrumentable_tree pi (k res)
       end

let instrument_mio
  (tree : iio (resexn 'a))
  (pi   : monitorable_prop)
  (#_    : squash (special_tree pi tree))
  (#_    : squash (trivial_hist `hist_ord` dm_iio_theta tree))
  (#c_pi : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) pi = 
  lemma_mio_tree_implies_instrumentable_tree pi tree;
  instrument_instrumentable tree pi #() #() #()

(**
let rec lemma_iiopi_implies_instrumentable_tree (pi:monitorable_prop) (tree:iio 'a) :
  Lemma
    (requires (forall h. dm_iio_theta tree (fun lt r -> enforced_locally pi h lt) h))
    (ensures (instrumentable_tree pi tree)) = 
    match tree with
    | Return _ -> ()
    | Decorated dec m k ->
      assert (forall h lt. dec h lt ==> enforced_locally pi h lt);
      admit ()
    | Call GetTrace _ k -> 
      introduce forall h'. instrumentable_tree pi (k h') with begin
        assume (forall h. dm_iio_theta (k h') (fun lt r -> enforced_locally pi h lt) h);
        lemma_iiopi_implies_instrumentable_tree pi (k h')
      end
    | _ -> admit ()

private
let instrument_iiopi
  (tree : iio (resexn 'a))
  (pi   : monitorable_prop)
  (** when running a computation, F* forces us to prove the wp.
      since we are going to execute the computation ourselfs by
      instrumenting it, we need proof that the tree produces only
      good traces. **)
  (#_    : squash (forall h. dm_iio_theta tree (fun lt r -> enforced_locally pi h lt) h))
  (#c_pi : squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) pi = 
  lemma_iiopi_implies_instrumentable_tree pi tree;
  instrument_instrumentable tree pi #() #() #()

let test (f:unit -> IIOpi (resexn 'b) 'pi) c_pi : IIOpi (resexn 'b) 'pi =
  let tree : dm_iio (resexn 'b) (pi_hist _ 'pi) = reify (f ()) in
  let proof1 : squash (forall h. dm_iio_theta tree (fun lt r -> enforced_locally 'pi h lt) h) = () in
  instrument_iiopi tree 'pi #proof1 #c_pi

(**
let rec lemma_iiopi_implies_instrumentable_tree (pi:monitorable_prop) (tree:iio 'a):
  Lemma
    (requires (pi_hist _ pi `hist_ord` dm_iio_theta tree))
    (ensures (instrumentable_tree pi tree)) = 
    match tree with
    | Return _ -> ()
    | Call GetTrace _ k -> 
      assert (forall p h. pi_hist _ pi p h ==> dm_iio_theta tree p h);
      //assert_norm (forall p h. pi_hist _ pi p h ==> dm_iio_theta (k h) p h);
      introduce forall h. instrumentable_tree pi (k h) with begin
//        eliminate forall h. (forall p. pi_hist _ pi p h ==> dm_iio_theta (k h) p h) with h;
        assume (forall p h'. pi_hist _ pi p h' ==> dm_iio_theta (k h) p h');
        lemma_iiopi_implies_instrumentable_tree pi (k h)
      end
    | _ -> admit ()
**)
val theta' : iio 'a -> monitorable_prop -> hist 'a
let rec theta' m pi =
  match m with
  | Return x -> dm_iio_theta m
  | PartialCall pre k ->
      hist_bind (DMFree.partial_call_wp pre) (fun r -> theta' (k r) pi)
  | Call cmd arg k ->
      hist_bind (iio_wps cmd arg) (fun r -> theta' (k r) pi)
  | Decorated post #b m' k ->
      hist_bind 
        #event
        #(FStar.Universe.raise_t b)
        #_
        (fun p h -> dm_iio_theta m' (fun lt r -> enforced_locally pi h lt /\ p lt r) h)
        (fun r -> theta' (k (FStar.Universe.downgrade_val r)) pi)

let super_lemma 
  (pi:monitorable_prop)
  (m : iio (Universe.raise_t 'b))
  (dec: dec_post #event)
  (p:hist_post unit)
  (h:trace)  
  (_:squash (dm_iio_theta (Decorated dec m (fun x -> Return ())) (fun lt r -> enforced_locally pi h lt) h)) :
  Lemma (
    pi_hist _ pi p h ==>
    dm_iio_theta m
      (fun lt r ->
        enforced_locally pi h lt /\
        dm_iio_theta (Return ())
          (hist_post_shift p lt)
          (apply_changes h lt)) h) =
  introduce pi_hist _ pi p h ==> dm_iio_theta m
      (fun lt r ->
        enforced_locally pi h lt /\
        dm_iio_theta (Return ())
          (hist_post_shift p lt)
          (apply_changes h lt)) h with _. begin 
    calc (==>) {
        dm_iio_theta (Decorated dec m (fun x -> Return ())) p h;
        == {}
        DMFree.theta iio_wps (Decorated dec m (fun x -> Return ())) p h;
        == { _ by (norm [delta_only [`%DMFree.theta;`%dm_iio_theta]; zeta; iota]) }
        hist_bind
        (fun p h -> dm_iio_theta m (fun lt r -> dec h lt /\ p lt r) h)
        (fun r -> dm_iio_theta (Return ())) p h;
        == { _ by (norm [delta_only [`%hist_bind;`%hist_post_bind]]) }
        dm_iio_theta m
        (fun lt r ->
            dec h lt /\
            dm_iio_theta (Return ())
            (hist_post_shift p lt)
            (rev lt @ h)) h;
    };

    let p1 = (fun lt (r: Universe.raise_t 'b)->
            dec h lt /\
            dm_iio_theta (Return ())
            (hist_post_shift p lt)
            (rev lt @ h)) in
    let p2 = (fun lt (r:Universe.raise_t 'b) ->
            enforced_locally pi h lt /\
            dm_iio_theta (Return ())
            (hist_post_shift p lt)
            (rev lt @ h)) in
    assert (forall lt r. enforced_locally pi h lt ==> p lt r);
    assert (forall lt r. p1 lt r ==> p2 lt r) by (
      norm [delta_only [`%dm_iio_theta;`%DMFree.theta;`%hist_return;`%hist_post_shift]; zeta; iota];
      l_to_r [`List.Tot.Properties.append_l_nil];
      tadmit ();
     // ExtraTactics.blowup ();
      dump "H"
    )
  end


#set-options "--fuel 10 --ifuel 10 --z3rlimit 30"
let rec lemma_iiopi_implies_instrumentable_tree (pi:monitorable_prop) (tree:iio 'a) p h:
  Lemma
    (requires (pi_hist _ pi p h ==> dm_iio_theta tree p h))
    (ensures (dm_iio_theta tree p h ==> theta' tree pi p h)) = 
    match tree with
    | Return _ -> ()
  
    (** *** Call GetTrace**)
    | Call GetTrace arg k -> 
      calc (==>) {
        dm_iio_theta (Call GetTrace arg k) p h;
        == { _ by (norm [delta_only [`%dm_iio_theta; `%DMFree.theta]; zeta;iota]) }
        hist_bind (iio_wps GetTrace arg) (fun r -> dm_iio_theta (k r)) p h;
        == {
          _ by (
              norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift;`%iio_wps];iota];
              l_to_r [`List.Tot.Properties.append_nil_l])
        }
        dm_iio_theta (k h) (fun lt' r -> p lt' r) h;
        ==> {
          assert (pi_hist _ pi p h ==> dm_iio_theta (k h) p h) by (rewrite_eqs_from_context (); norm [iota]);
          lemma_iiopi_implies_instrumentable_tree pi (k h) p h;
          assert (dm_iio_theta (k h) p h ==> theta' (k h) pi p h)
        }
        theta' (k h) pi (fun lt' r -> p lt' r) h;
        == {
          _ by (
              norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift;`%iio_wps];iota];
              l_to_r [`List.Tot.Properties.append_nil_l])
        }
        hist_bind (iio_wps GetTrace arg) (fun r -> theta' (k r) pi) p h;
        == { _ by (norm [delta_only [`%theta']; zeta;iota])}
        theta' (Call GetTrace arg k) pi p h;
      }

    (** *** Call cmd**)
    | Call (cmd:io_cmds) arg k ->
      calc (==) {
        dm_iio_theta (Call cmd arg k) p h;
        == { _ by (norm [delta_only [`%dm_iio_theta; `%DMFree.theta]; zeta;iota]) }
        hist_bind (iio_wps cmd arg) (fun r -> dm_iio_theta (k r)) p h;
        == {
          _ by (
            norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift;`%iio_wps];iota];
            l_to_r [`List.Tot.Properties.append_nil_l]
          )
        }
        io_pre cmd arg h /\
         (forall (r: iio_sig.res cmd arg).
            hist_post_bind h (fun r -> dm_iio_theta (k r)) p [convert_call_to_event cmd arg r] r);
      };
      introduce forall (r:iio_sig.res cmd arg). (
        let ltM : trace = [convert_call_to_event cmd arg r] in
        let p' = hist_post_shift p ltM in
        let h' = apply_changes h ltM in
        (dm_iio_theta (k r) p' h' ==> theta' (k r) pi p' h')) with begin
        let ltM = [convert_call_to_event cmd arg r] in
        let p' = hist_post_shift p ltM in
        let h' = apply_changes h ltM in
        assume (pi_hist _ pi p' h' ==> pi_hist _ pi p h);
        assert (dm_iio_theta tree p h ==> dm_iio_theta (k r) p' h');
        assert (pi_hist _ pi p' h' ==> dm_iio_theta (k r) p' h');
        lemma_iiopi_implies_instrumentable_tree pi (k r) p' h';
        assert (dm_iio_theta (k r) p' h' ==> theta' (k r) pi p' h')
      end;
      calc (==) {
        io_pre cmd arg h /\
         (forall (r: iio_sig.res cmd arg).
            hist_post_bind h (fun r -> theta' (k r) pi) p [convert_call_to_event cmd arg r] r);
        == {
          _ by (
              norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift;`%iio_wps];iota];
              l_to_r [`List.Tot.Properties.append_nil_l])
        }
        hist_bind (iio_wps cmd arg) (fun r -> theta' (k r) pi) p h;
        == { _ by (norm [delta_only [`%theta']; zeta;iota])}
        theta' (Call cmd arg k) pi p h;
      }

    (** *** PartialCall **)
    | PartialCall pre k ->
      calc (==) {
        dm_iio_theta (PartialCall pre k) p h;
        == { _ by (norm [delta_only [`%dm_iio_theta; `%DMFree.theta]; zeta;iota]) }
        hist_bind (DMFree.partial_call_wp pre) (fun r -> dm_iio_theta (k r)) p h;
        == {
          _ by (
            norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift;`%DMFree.partial_call_wp];iota];
            l_to_r [`List.Tot.Properties.append_nil_l]
          )
        }
        pre /\ dm_iio_theta (k ()) (fun lt' r -> p lt' r) h;
      };
      introduce forall (r:squash pre). dm_iio_theta (k r) p h ==> theta' (k r) pi p h with begin
        assert (pi_hist _ pi p h ==> dm_iio_theta (k r) p h);
        lemma_iiopi_implies_instrumentable_tree pi (k r) p h;
        assert (dm_iio_theta (k r) p h ==> theta' (k r) pi p h)
      end;
      calc (==) {
        pre /\ theta' (k ()) pi (fun lt' r -> p lt' r) h;
        == {
          _ by (
              norm [delta_only [`%hist_bind;`%hist_post_bind;`%hist_post_shift;`%DMFree.partial_call_wp];iota];
              l_to_r [`List.Tot.Properties.append_nil_l])
        }
        hist_bind (DMFree.partial_call_wp pre) (fun r -> theta' (k r) pi) p h;
        == { _ by (norm [delta_only [`%theta']; zeta;iota])}
        theta' (PartialCall pre k) pi p h;
      }
    | Decorated dec m k ->
      calc (==>) {
        dm_iio_theta (Decorated dec m k) p h;
        == { _ by (norm [delta_only [`%dm_iio_theta; `%DMFree.theta]; zeta;iota]) }
        hist_bind
          (fun p h -> dm_iio_theta m (fun lt r -> dec h lt /\ p lt r) h)
          (fun r -> dm_iio_theta (k (Universe.downgrade_val r))) 
          p 
          h;
        == {}
        dm_iio_theta
          m
          (fun lt r ->
            dec h lt /\
            dm_iio_theta (k (Universe.downgrade_val r)) (hist_post_shift p lt) (apply_changes h lt))
          h;
        ==> { admit () } //super_lemma pi m dec k p h () }
        dm_iio_theta
          m
          (fun lt r ->
            enforced_locally pi h lt /\
            dm_iio_theta (k (Universe.downgrade_val r)) (hist_post_shift p lt) (apply_changes h lt))
          h;
        ==> {
          assume (forall lt r.
            dm_iio_theta (k (Universe.downgrade_val r)) (hist_post_shift p lt) (apply_changes h lt) ==> 
            theta' (k (Universe.downgrade_val r)) pi (hist_post_shift p lt) (apply_changes h lt))
        }
        dm_iio_theta 
          m
          (fun lt r ->
            enforced_locally pi h lt /\
            theta' (k (Universe.downgrade_val r)) pi (hist_post_shift p lt) (apply_changes h lt))
          h;
        == {}
        hist_bind
          (fun p h -> dm_iio_theta m (fun lt r -> enforced_locally pi h lt /\ p lt r) h)
          (fun r -> theta' (k (Universe.downgrade_val r)) pi)
          p 
          h;
        == { _ by (norm [delta_only [`%theta']; zeta;iota]) }
        theta' (Decorated dec m k) pi p h;
      }
#reset-options	
