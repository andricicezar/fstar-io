module ILang.CompileTo.TLang

open FStar.Tactics
open FStar.Tactics.Typeclasses

open Common

open ILang
open TLang
open Hist
open TC.Monitorable.Hist

open IO.Sig
open DM.IIO
open TC.Checkable

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

let rec _instrument
  (tree : iio (resexn 'a))
  ('p    : monitorable_prop)
  (piprop:squash (forall h cmd arg. 'p cmd arg h ==> io_pre cmd arg h)) :
  IIOpi (resexn 'a) 'p =
  match tree with
  | Return r -> r
  | Call GetTrace argz fnc -> Inr Contract_failure
  | PartialCall pre fnc -> Inr Contract_failure
  | Decorated d m k ->
      let r = IIOwp?.reflect m in
      instrument (k r) 'p piprop
  | Call cmd argz fnc -> begin
    let d : checkable2 (io_pre cmd) = (
      implies_is_checkable2 (io_sig.args cmd) trace ('p cmd) (io_pre cmd) piprop) in
    (** Check if the runtime check failed, and if yes, return the error **)
    let rez = dynamic_cmd cmd d argz in
    let z' : iio (resexn 'a) = fnc rez in
    _instrument z' 'p piprop
  end



class compile_ilang (t:Type) (pi:monitorable_prop) = {
  c_t_ilang : ilang t pi;
  out_type : Type;
  c_out_type : tlang out_type;
  compile: t -> Tot (out_type)
  // CC theorem?
  // c_compile: squash (forall (wS:t). theta (reify (compile wS)) `hist_ord` theta (reify wS)) 
}

let instrument''
  (f:'a -> MIIO (resexn 'b))
  {| compile_ilang 'a |}
  {| tlang ('a -> MIIO 'b) |}
  (pi:monitorable_prop) :
  Tot ('a -> IIOpi (resexn 'b) pi) = //{ ilang ('a -> IIOpi 'b pi) pi }) =
  fun (x:'a) -> 
    let tree : DM.IIO.dm_iio (resexn 'b) (trivial_hist ()) = reify (f (compile x)) in
    _instrument tree pi (admit ()) 

let instrument (#a #b:Type)
  (f:a) {| tlang a |}
  (pi:monitorable_prop) :
  Tot (x:b{ilang b pi}) = admit ()


instance compile_ilang_base t1 t2 pi {| d1:compile_ilang t1 pi |} {| d2:compile_ilang t2 pi |} : compile_ilang (t1 -> IIOpi (resexn t2) pi) pi = {
  c_t_ilang = ilang_arrow pi t1 #d1.c_t_ilang t2 #d2.c_t_ilang;
  out_type = d1.out_type -> MIIO (resexn d2.out_type);
  c_out_type = tlang_arrow d1.out_type d2.out_type #d1.c_out_type #d2.c_out_type;
  compile = (fun (f:(t1 -> IIOpi (resexn t2) pi)) (x:d1.out_type) ->
     IIOwp?.reflect (Decorated pi (reify (compile (f (instrument x #d1.c_out_type pi))))
                                  Return);
  )
}
