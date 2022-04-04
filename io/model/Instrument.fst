module Instrument

open FStar.List
open FStar.Tactics

open Common
open IO.Sig
open DM
open TC.Checkable

let rev_append_rev_append () : Lemma (
  forall (h le1 le2:trace).
    ((List.rev le2) @ (List.rev le1) @ h) ==
      ((List.rev (le1@le2)) @ h))
   by (FStar.Tactics.Derived.l_to_r [`List.append_assoc;`List.rev_append])
      = ()

let rec npnode (t:io 'a) =
  match t with
  | Return _ -> True
  | PartialCall _ _ -> False
  | Call cmd arg fnc -> forall r. npnode (fnc r)
  
type npio 'a = t:(io 'a){npnode t}

let rec from_io_to_npio (tree:io 'a) (p:hist_post #event 'a) h (_:squash (dm_io_theta tree p h)) : npio 'a =
  match tree with
  | Return x -> Return x
  | Call cmd arg fnc -> 
      let k : (io_sig.res cmd arg) -> npio 'a = fun i -> begin
        let p' : hist_post 'a = hist_post_shift p [convert_call_to_event cmd arg i] in
        let h' = apply_changes h [convert_call_to_event cmd arg i] in
        assert (dm_io_theta (fnc i) p' h');
        from_io_to_npio (fnc i) p' h' _
      end in
      Call cmd arg k
  | PartialCall pre fnc ->
      assert pre;
      from_io_to_npio (fnc ()) p h _

let from_dm_io_to_npio (tree:dm_io 'a (trivial_hist ())) : npio 'a =
  from_io_to_npio tree (fun _ _ -> True) [] ()

let rec _instrument
  (tree : npio 'a)
  ('p    : monitorable_prop)
  (piprop:squash (forall h cmd arg. 'p cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (maybe 'a) 'p (fun _ -> True) (fun _ _ _ -> True) =
  match tree with
  | Return r -> (Inl r)
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace ('p cmd) (io_pre cmd) piprop) in
    (** Check if the runtime check failed, and if yes, return the error **)
    match dynamic_cmd cmd d argz with
    | Inl rez ->
      let z' : npio 'a = fnc rez in
      _instrument z' 'p piprop
    | Inr err -> Inr err
  end

let instrument_MIIO = _instrument
