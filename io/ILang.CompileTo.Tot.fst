module ILang.CompileTo.Tot

open FStar.List.Tot
open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open ILang
open Hist
open TC.Monitorable.Hist

open IO.Sig
open IIO
open TC.Checkable

class tlang (t:Type) = { mldummy : unit }
instance tlang_unit : tlang unit = { mldummy = () }

instance tlang_bool : tlang bool = { mldummy = () }
instance tlang_int : tlang int = { mldummy = () }

instance tlang_pair t1 t2 {| d1:tlang t1 |} {| d2:tlang t2 |} : tlang (t1 * t2) = 
  { mldummy = () }
instance tlang_either t1 t2 {| d1:tlang t1 |} {| d2:tlang t2 |} : tlang (either t1 t2) =
  { mldummy = () }

instance tlang_resexn t1 {| d1:tlang t1 |} : tlang (resexn t1) =
  { mldummy = () }
instance tlang_arrow t1 {| d1:tlang t1 |} t2 {| d2:tlang t2 |} : tlang (t1 -> Tot (resexn t2)) = { mldummy = () }

class compilable (t:Type) (pi:monitorable_prop) = {
  c_t_ilang : ilang t pi;
  comp_type : Type;
  c_comp_type : tlang comp_type;
  compile: t -> comp_type
}

class instrumentable (t:Type) (pi:monitorable_prop) = {
  cc_t_ilang : ilang t pi;
  unverified : Type;
  c_unverified : tlang unverified;
  instrument: unverified -> t 
}

(** *** Compilable base types **)

instance compile_resexn pi (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  c_t_ilang = ilang_resexn pi t #d1.c_t_ilang;
  comp_type = resexn (d1.comp_type);
  c_comp_type = tlang_resexn d1.comp_type #(d1.c_comp_type);
  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

(** *** Compilable arrows **)

let the_p #a : hist_post #event a = fun lt r -> True

exception Something_went_really_bad

let super_lemma 
  d
  (m : iio (Universe.raise_t 'b))
  k
  (_:squash (forall h. dm_iio_theta (Decorated d m k) the_p h)) :
  Lemma (
   forall h. dm_iio_theta m (fun lt r ->
        dm_iio_theta (k (Universe.downgrade_val r))
          the_p
          (apply_changes h lt)) h) = 
 introduce 
   forall h. dm_iio_theta m (fun lt r ->
        dm_iio_theta (k (Universe.downgrade_val r))
          the_p
          (apply_changes h lt)) h with begin 
  calc (==>) {
      dm_iio_theta (Decorated d m k) the_p h;
      ==> { _ by (
            binder_retype (nth_binder (-1));
            norm [delta_only [`%dm_iio_theta;`%DMFree.theta]; zeta];
            trefl ();
            norm [delta_only [`%dm_iio_theta]];
            assumption ()) }
      hist_bind
             (fun p h -> dm_iio_theta m (fun lt r -> d h lt /\ p lt r) h)
             (fun r -> dm_iio_theta (k (Universe.downgrade_val r))) the_p h;
      ==> { _ by (binder_retype (nth_binder (-1));
                  norm [delta_only [`%hist_bind;`%hist_post_bind]]; trefl (); assumption ()) }
      dm_iio_theta m
        (fun lt r ->
          d h lt /\
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift the_p lt)
            (List.Tot.Base.rev lt @ h)) h;
      ==> {}
      dm_iio_theta m
        (fun lt r ->
          dm_iio_theta (k (Universe.downgrade_val r))
            (hist_post_shift the_p lt)
            (List.Tot.Base.rev lt @ h)) h;
      == { _ by (norm [delta_only [`%hist_post_shift; `%the_p]]; dump "H")}
      dm_iio_theta m
        (fun lt r ->
          dm_iio_theta (k (Universe.downgrade_val r))
            the_p
            (List.Tot.Base.rev lt @ h)) h;
    }
  end


let rec skip_partial_calls (tree:iio 'a) (_:squash (forall h. dm_iio_theta tree the_p h)) : Tot (resexn 'a) =
  match tree with
  | Return y -> Inl y
  | PartialCall pre k -> begin
    (** The intuition here is that the pre-condition is true,
    thus, all asserts are true **)
   assert (dm_iio_theta tree the_p []);
   assert pre;
   skip_partial_calls (k ()) ()
  end
  | Decorated dec m k -> begin
    let r : resexn _ = skip_partial_calls m () in
    if Inl? r then begin
      let r = Universe.downgrade_val (Inl?.v r) in
      let z = k r in
      super_lemma dec m k ();
      assert (forall h. dm_iio_theta m the_p h);
      assert (forall h. dm_iio_theta m
        (fun lt r -> dm_iio_theta (k (Universe.downgrade_val r)) the_p (apply_changes h lt)) 
        h);
      (** TODO: this is similar with the problem from ILang.CompileTo.MLang#run_m **)
      assume (forall h. dm_iio_theta z the_p h);
      skip_partial_calls z ()
    end else Inr Something_went_really_bad
  end
  (** during extraction, Free.IO.Call is replaced with an actual
  implementation of the commands, therefore, the `Call` constructor
  does not exist **)
  | _ -> Inr Something_went_really_bad

instance compile_ilang_base 
  pi
  (t1:Type) {| d1:instrumentable t1 pi |} 
  (t2:Type) {| d2:compilable t2 pi |} :
  Tot (compilable (t1 -> IIOpi (resexn t2) pi) pi) = {

  c_t_ilang = ilang_arrow pi t1 #d1.cc_t_ilang t2 #d2.c_t_ilang;
  comp_type = d1.unverified -> Tot (resexn d2.comp_type);
  c_comp_type = (tlang_arrow d1.unverified #d1.c_unverified d2.comp_type #d2.c_comp_type);
  compile = (fun (f:(t1 -> IIOpi (resexn t2) pi)) (x:d1.unverified) ->
    let r : unit -> IIOpi _ pi = fun () ->  (compile #_ #pi #(compile_resexn pi t2 #d2) (f (instrument x))) in
    let tree : dm_iio _ _ = reify (r ()) in
    match skip_partial_calls tree () with
    | Inl x -> x
    | Inr r -> Inr r);
}

(** *** Insturmentable types **)
instance instrumentable_resexn pi (t:Type) {| d1:instrumentable t pi |} : instrumentable (resexn t) pi = {
  cc_t_ilang = ilang_resexn pi t #d1.cc_t_ilang;
  unverified = resexn (d1.unverified);
  c_unverified = tlang_resexn d1.unverified #d1.c_unverified;
  instrument = (fun x ->
    match x with
    | Inl r -> Inl (d1.instrument r)
    | Inr err -> Inr err)
}

(** *** Instrumentable arrows **)
instance instrumentable_arrow t1 t2 pi {| d1:compilable t1 pi |} {| d2:instrumentable t2 pi |} : instrumentable (t1 -> IIOpi (resexn t2) pi) pi = {
  cc_t_ilang = ilang_arrow pi t1 #d1.c_t_ilang t2 #d2.cc_t_ilang;
  unverified = d1.comp_type -> Tot (resexn d2.unverified);
  c_unverified = tlang_arrow d1.comp_type #d1.c_comp_type d2.unverified #d2.c_unverified;
  instrument = (fun (f:d1.comp_type -> Tot (resexn d2.unverified)) (x:t1) -> 
    (** this is basically a hack to be able to extract **)
    let f' : d1.comp_type -> IIOpi (resexn d2.unverified) pi = fun x -> f x in
    let r : resexn d2.unverified = f' (compile x) in
    instrument #_ #pi #(instrumentable_resexn pi t2 #d2) r);
}
