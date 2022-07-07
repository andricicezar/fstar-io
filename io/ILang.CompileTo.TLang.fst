module ILang.CompileTo.TLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open Hist
open IO.Sig

type monitorable_prop = (cmd:io_cmds) -> (io_sig.args cmd) -> (history:trace) -> Tot bool
unfold
let has_event_respected_pi (e:event) (check:monitorable_prop) (h:trace) : bool =
  match e with
  | EOpenfile arg _ -> check Openfile arg h
  | ERead arg _ -> check Read arg h
  | EClose arg _ -> check Close arg h

let rec enforced_locally
  (check : monitorable_prop)
  (h l: trace) :
  Tot bool (decreases l) =
  match l with
  | [] -> true
  | e  ::  t ->
    if has_event_respected_pi e check h then enforced_locally (check) (e::h) t
    else false

class compilable (t:Type) (pi:monitorable_prop) = {
  comp_type : Type;
  compile: t -> comp_type
}

instance compile_resexn (pi:monitorable_prop) (t:Type) {| d1:compilable t pi |} : compilable (resexn t) pi = {
  comp_type = resexn (d1.comp_type);
  compile = (fun x ->
    match x with
    | Inl r -> Inl (compile r)
    | Inr err -> Inr err)
}

class instrumentable (t:Type) (pi:monitorable_prop) = {
  inst_type : Type;
  instrument: inst_type -> t 
}


effect IIOpi (a:Type) (pi : monitorable_prop) = 
  DM.IIO.IIOwp a (fun p h -> (forall r lt. (enforced_locally pi h lt) ==> p lt r))
effect MIIO (a:Type) = DM.IIO.IIOwp a (Hist.trivial_hist)

#set-options "--query_stats"
let test_123
  (t1:Type u#0)
  (t2:Type u#0)
  pi
  {| d1:instrumentable t1 pi |}
  {| d2:compilable t2 pi |}
  (f : (t1 -> IIOpi (resexn t2) pi)) 
  (x : d1.inst_type) :
  compilable (t1 -> IIOpi (resexn t2) pi) pi by (
  unfold_def (`hist_return)
) = {
  comp_type = d1.inst_type -> MIIO (resexn d2.comp_type);
  compile = (fun (f:(t1 -> IIOpi (resexn t2) pi)) (x:d1.inst_type) ->
   let x : DM.IIO.dm_iio (resexn d2.comp_type) (hist_bind (fun p h -> forall r (lt: trace). enforced_locally pi h lt ==> p lt r)
      (fun (r:resexn t2) -> hist_return (compile #_ #pi #(compile_resexn pi t2 #d2) r))) =
     reify (compile #_ #pi #(compile_resexn pi t2 #d2) (f (instrument x))) in
   assert (False);
   DM.IIO.IIOwp?.reflect x
  );
}
