module ILang.CompileTo.MLang

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open ILang
open MLang
open Hist
open TC.Monitorable.Hist

open IO.Sig
open IIO
open TC.Checkable

class compilable (t:Type) (pi:monitorable_prop) = {
  c_t_ilang : ilang t pi;
  comp_type : Type;
  c_comp_type : either (mlang_fo comp_type) (mlang_verified comp_type);
  compile: t -> comp_type
  // CC theorem?
  // c_compile: squash (forall (wS:t). theta (reify (compile wS)) `hist_ord` theta (reify wS)) 
}

class instrumentable (t:Type) (pi:monitorable_prop) = {
  cc_t_ilang : ilang t pi;
  unverified : Type;
  c_unverified : mlang_unverified unverified;
  [@@@no_method]
  c_pi:squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h);
  instrument: unverified -> t 
}

(** *** Compilable base types **)

instance compile_resexn pi (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  c_t_ilang = ilang_resexn pi t #d1.c_t_ilang;
  comp_type = resexn (d1.comp_type);
  c_comp_type = if Inl? d1.c_comp_type then Inl (mlang_fo_resexn d1.comp_type #(Inl?.v d1.c_comp_type))
                else Inr (mlang_verified_resexn d1.comp_type #(Inr?.v d1.c_comp_type));
  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

(** *** Compilable arrows **)

(** TODO: t1 and t2 are in universe 0. is that a problem? can we do HO? **)
instance compile_ilang_base 
  pi
  (t1:Type u#0) {| d1:instrumentable t1 pi |} 
  (t2:Type u#0) {| d2:compilable t2 pi |} :
  Tot (compilable (t1 -> IIOpi (resexn t2) pi) pi) = {

  c_t_ilang = ilang_arrow pi t1 #d1.cc_t_ilang t2 #d2.c_t_ilang;
  comp_type = d1.unverified -> MIIO (resexn d2.comp_type);
  c_comp_type = Inr (mlang_verified_unverified d1.unverified d2.comp_type #d1.c_unverified #d2.c_comp_type);
  compile = (fun (f:(t1 -> IIOpi (resexn t2) pi)) (x:d1.unverified) ->
    let r : unit -> IIOpi _ pi = fun () -> Universe.raise_val (compile #_ #pi #(compile_resexn pi t2 #d2) (f (instrument x))) in
    let x : dm_iio _ _ = reify (r ()) in
    let x' : dm_iio (Universe.raise_t (resexn d2.comp_type)) (fun p h -> forall r lt. b2t(enforced_locally pi h lt) ==> p lt r) = x in
    assert (forall h. dm_iio_theta x' (fun lt r -> enforced_locally pi h lt) h);
    (** TODO: I have no idea what happens with the raise_t of the result. 
        I suppose for now it does not care. There is a Universe.downgrade_val in the theta and I suppose there will be another
        downgrade_val when interpreting the tree. **)
    let dm : dm_iio (resexn d2.comp_type) trivial_hist = Decorated (fun h lt -> b2t (enforced_locally pi h lt)) x' Return in
    IIOwp?.reflect dm
  );
}

(** *** Insturmentable types **)
instance instrumentable_resexn pi (t:Type) {| d1:instrumentable t pi |} : instrumentable (resexn t) pi = {
  cc_t_ilang = ilang_resexn pi t #d1.cc_t_ilang;
  unverified = resexn (d1.unverified);
  c_unverified = mlang_unverified_resexn d1.unverified #d1.c_unverified;
  c_pi = d1.c_pi;
  instrument = (fun x ->
    match x with
    | Inl r -> Inl (instrument r)
    | Inr err -> Inr err)
}


(** *** Instrumentable arrows **)
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
          (apply_changes h lt)) h) = 
  
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


let lemma_smt_pat (pi:monitorable_prop) (h lt1 lt2:trace) :
  Lemma (requires (
    enforced_locally pi h lt1 /\
    enforced_locally pi (apply_changes h lt1) lt2))
    (ensures (
    enforced_locally pi h (lt1 @ lt2))) [SMTPat (enforced_locally pi h (lt1@lt2))] = (** not urgent **) admit ()

let rec inside_respects_pi
  (tree : iio (resexn 'a))
  (pi : monitorable_prop) : Type0 =
  match tree with
  | Return _ -> True
  | PartialCall pre k ->
      pre ==> (inside_respects_pi (k ()) pi)
  | Call cmd arg k ->
      forall res. inside_respects_pi (k res) pi
  | Decorated dec m k ->
      (forall h lt. dec h lt ==> enforced_locally pi h lt) /\
      (forall res. inside_respects_pi (k res) pi)


let run_m
  (pi:monitorable_prop)
  (m : iio (Universe.raise_t 'b))
  dec
  k
  p
  (h:trace)
  (_:squash (inside_respects_pi (Decorated dec m k) pi))
  (_:squash (dm_iio_theta (Decorated dec m k) p h)) :
//  (_:squash ) :
  IIO 
    (iio _ * _ * trace)
    (requires (fun h' -> h == h'))
    (ensures (fun h (z', p', h') lt ->
      h' == apply_changes h lt /\
      dm_iio_theta z' p' h' /\
      enforced_locally pi h lt /\ 
      inside_respects_pi z' pi)) =
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
  (** urgent - it is urgent, because I am not confident it can be proved **)
  assert (dm_iio_theta z' p' h') by (tadmit ());
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
  (tree : iio (resexn 'a))
  (p    : hist_post (resexn 'a))
  (h    : trace)
  (d1   : squash (dm_iio_theta tree p h))
  (pi   : monitorable_prop)
  (d2   : squash (inside_respects_pi tree pi))
  (c_pi:squash (forall h cmd arg. pi cmd arg h ==> io_pre cmd arg h)) :
  IIOwp (resexn 'a) (fun p h' -> h == h' /\ (forall lt r. enforced_locally pi h lt ==> p lt r)) =
  match tree with
  | Return r -> r
  | Call GetTrace argz fnc -> Inr Contract_failure
  | PartialCall pre fnc -> Inr Contract_failure
  | Decorated d #b m k ->
    admit ();
    let (z', p', h') = run_m pi m d k p h d1 d2 in
    _instrument z' p' h' () pi () c_pi
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace (pi cmd) (io_pre cmd) c_pi) in
    (** Check if the runtime check failed, and if yes, return the error **)
    let rez = dynamic_cmd cmd d argz in
    let z' : iio (resexn 'a) = fnc rez in

    let p' : hist_post (resexn 'a) = hist_post_shift p [convert_call_to_event cmd argz rez] in
    let h' = apply_changes h [convert_call_to_event cmd argz rez] in
    let proof1 : squash (dm_iio_theta z' p' h') = () in
    let proof2 : squash (inside_respects_pi z' pi) = () in
    _instrument z' p' h' proof1 pi proof2 c_pi
  end

let rec lemma_super_lemma (m:iio (resexn 'a)) pi :
  Lemma (MIO.basic_free m ==> inside_respects_pi m pi) =
  match m with
  | Return _ -> ()
  | Decorated _ _ _ -> ()
  | PartialCall _ _ -> ()
  | Call GetTrace _ _ -> ()
  | Call cmd arg k ->
    introduce forall res. MIO.basic_free (k res) ==> inside_respects_pi (k res) pi with begin
      lemma_super_lemma (k res) pi
    end

instance instrumentable_arrow t1 t2 pi {| d1:compilable t1 pi |} {| d2:instrumentable t2 pi |} : instrumentable (t1 -> IIOpi (resexn t2) pi) pi = {
  cc_t_ilang = ilang_arrow pi t1 #d1.c_t_ilang t2 #d2.cc_t_ilang;
  unverified = d1.comp_type -> MIO.MIO (resexn d2.unverified);
  c_unverified = mlang_unverified_verified d1.comp_type d2.unverified #d1.c_comp_type #d2.c_unverified;
  c_pi = d2.c_pi;
  instrument = (fun (f:d1.comp_type -> MIO.MIO (resexn d2.unverified)) (x:t1) -> 
    (**TODO: why is this typechecking? 
       the argument of f is in effect MIIO and it can be composed with the effect of f if f is lifted to 
       MIIO. That happens during reification.... but I am confused if the type of this is correct. **)
    let tree : MIO.dm_mio _ trivial_hist = reify (f (compile x)) in
    let p = fun _ _ -> True in
    let h = get_trace () in
    lemma_super_lemma tree pi;
    let r  : resexn d2.unverified = _instrument #d2.unverified tree p h () pi () d2.c_pi in 
    instrument #_ #pi #(instrumentable_resexn pi t2 #d2) r 
  )
}
