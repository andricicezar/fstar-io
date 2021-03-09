module Test.ExportingToML

open FStar.All
open Common
open IO.Free
open IO.Effect
open IIO.Effect
open MIIO.Effect
open Minterop

instance ml_arrow : ml (monitorable_prop) =
  { mldummy = () }

let _export_MIIO_2
  (#t1:Type) {| d1:importable t1 |}
  (#t2:Type) {| d2:importable t2 |}
  (#t3:Type) {| d3:exportable t3 |}
  (f:t1 -> t2 -> MIIO t3)
  (x:d1.itype) (y:d2.itype) :
  ML d3.etype =
  match import x with
  | Some x -> _export_MIIO (f x) y
  | None -> FStar.All.raise Contract_failure

instance exportable_IOwp_2
  (t1:Type) {| d1:importable t1 |}
  (t2:Type) {| d2:importable t2 |}
  (t3:Type) {| d3:exportable t3 |}
  (pre:t1 -> t2 -> trace -> Type0) {| d4:checkable3 pre |}
  (post:t1 -> t2 -> trace -> (m:maybe t3) -> trace -> Type0) :
  Tot (exportable (x:t1 -> y:t2 ->
    IOwp t3 (fun h p ->
      pre x y h /\ (forall r lt. post x y h r lt ==>  p r lt)))) =
  mk_exportable
    (d1.itype -> d2.itype -> ML d3.etype)
    (fun (f:(x:t1 -> y:t2 ->
    IOwp t3 (fun h p ->
      pre x y h /\ (forall r lt. post x y h r lt ==>  p r lt)))) ->
      _export_MIIO_2 (_IIOwp_as_MIIO_2 d4.check3 post f))

val ml_openfile : monitorable_prop -> args Openfile -> ML (res Openfile)
let ml_openfile = export #_
  #(exportable_IOwp_2
    monitorable_prop #(importable_safe_importable monitorable_prop #(safe_importable_ml monitorable_prop #ml_arrow))
    (args Openfile)
    (res Openfile)
    (fun pi (argz:args Openfile) h -> pi h (| Openfile, argz |))
    (fun pi (argz:args Openfile) h r lt ->
        ~(Inr? r /\ Inr?.v r == Contract_failure) /\
        lt == [convert_call_to_event Openfile argz r] /\
        enforced_locally pi h lt))
  (static_cmd Openfile)


val ml_read : monitorable_prop -> args Read -> ML (res Read)
let ml_read = export #_
  #(exportable_IOwp_2
    monitorable_prop #(importable_safe_importable monitorable_prop #(safe_importable_ml monitorable_prop #ml_arrow))
    (args Read)
    (res Read)
    (fun pi (argz:args Read) h -> pi h (| Read, argz |))
    (fun pi (argz:args Read) h r lt ->
        ~(Inr? r /\ Inr?.v r == Contract_failure) /\
        lt == [convert_call_to_event Read argz r] /\
        enforced_locally pi h lt))
  (static_cmd Read)

val ml_close : monitorable_prop -> args Close -> ML (res Close)
let ml_close = export #_
  #(exportable_IOwp_2
    monitorable_prop #(importable_safe_importable monitorable_prop #(safe_importable_ml monitorable_prop #ml_arrow))
    (args Close)
    (res Close)
    (fun pi (argz:args Close) h -> pi h (| Close, argz |))
    (fun pi (argz:args Close) h r lt ->
        ~(Inr? r /\ Inr?.v r == Contract_failure) /\
        lt == [convert_call_to_event Close argz r] /\
        enforced_locally pi h lt))
  (static_cmd Close)

// Export primitives from IOStHist to ML
let test1 (pi:monitorable_prop) : ML unit =
  let fd = ml_openfile pi "../Makefile" in
  ml_close pi fd;
  let msg = ml_read pi fd in
  ()

let rec is_open (fd:file_descr) (h: trace) :
  Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ (Inl fd') ->
                   if fd = fd' then true
                   else is_open fd tail
               | EClose fd' _ ->
                    if fd = fd' then false
                    else is_open fd tail
               | _ -> is_open fd tail

let somePi : monitorable_prop = (fun s0 action ->
  match action with
  | (| Read, fd |) -> is_open fd s0
  | (| Close, fd |) -> is_open fd s0
  | _ -> true)

let _ =
  try_with
    (fun _ -> test1 somePi)
    (fun (err:exn) ->
      match err with
      | Contract_failure ->
          FStar.IO.print_any "\n\ntest1 failed successfully\n\n"
      | err -> 
          FStar.IO.print_any "Test 1 failed with the following error:\n";
          raise err)






// GIO = IOStHist + Invariant + PI + Flag for verifing dynamically
//                                   the default check

let test2 (pi:monitorable_prop) : IIOwp unit (fun h p ->
  iio_pre pi h /\ (forall r lt. iio_post pi h r lt ==> p r lt)) =
  let fd = dynamic_cmd Openfile pi "../Makefile" in
  let msg = dynamic_cmd Read pi fd in
  dynamic_cmd Close pi fd

val ml_test2 : monitorable_prop -> ML unit
let ml_test2 = export #_
  #(exportable_IIOwp
    monitorable_prop #(importable_safe_importable monitorable_prop #(safe_importable_ml monitorable_prop #ml_arrow))
    unit
    (fun pi h -> iio_pre pi h)
    (fun pi h r lt -> iio_post pi h r lt))
 test2

let pitrue : monitorable_prop = (fun _ _ -> true)

let _ =
  try_with
    (fun _ ->
      ml_test2 pitrue;
      FStar.IO.print_any "ml_test2 executed successfully with pitrue\n\n" )
    (fun (err:exn) ->
      FStar.IO.print_any "Test 1 failed with the following error:\n";
      raise err)

open Hist

effect IO
  (a:Type)
  (pi : monitorable_prop) =
  IOwp a (fun (h:trace) (p:hist_post a) ->
    enforced_globally pi h /\
    (forall res lt. (
      enforced_globally pi (apply_changes h lt) ==>  p res lt)))

instance exportable_IO
  (t1:Type) {| d1:importable t1 |}
  (t2:Type) {| d2:exportable t2 |}
  (pi:monitorable_prop) :
  Tot (exportable (x:t1 -> IO t2 pi)) =
  mk_exportable
    (d1.itype -> ML d2.etype)
    (fun (f:(x:t1 -> IO t2 pi)) ->
      _export_MIIO (
        _IIOwp_as_MIIO
          (fun x h -> enforced_globally pi h)
          (fun x h r lt -> enforced_globally pi (apply_changes h lt))
          f))


let test23 () : IO unit pitrue =
  let fd = static_cmd Openfile pitrue "../Makefile" in
  let msg = static_cmd Read pitrue fd in
  static_cmd Close pitrue fd

// val ml_test23 : unit -> ML unit
// let ml_test23 = export test23




// let pi' : monitorable_prop = (fun s0 action -> 
//   match action with
//   | (| Openfile, fnm |) -> true
//   | (| Read, fd |) -> false 
//   | (| Close, fd |) -> true)

// let _ = 
//   try_with
//     (fun _ -> ml_test2 pi')
//     (fun (err:exn) -> 
//       match err with
//       | GIO_pi_check_failed -> 
//           FStar.IO.print_any "ml_test2 failed successfully with p2\n\n" 
//       | err -> raise err)






// let test3 (pi:monitorable_prop) : GIO unit pi =
//   let fd = dynamic_cmd Openfile pi "../Makefile" in
//   dynamic_cmd Close pi fd;
//   let msg = dynamic_cmd Read pi fd in
//   ()

// val ml_test3 : monitorable_prop -> ML unit
// let ml_test3 = export test3

// let _ = 
//   try_with
//     (fun _ -> ml_test3 pitrue)
//     (fun (err:exn) -> 
//       match err with
//       | GIO_default_check_failed -> 
//           FStar.IO.print_any "ml_test3 failed successfully with pitrue\n\n" 
//       | err -> raise err)





// let test4 (pi:monitorable_prop) : GIO unit pi =
//   let fd = dynamic_cmd Openfile pi "../Makefile" in 
//   let msg = mixed_cmd Read pi fd in
//   mixed_cmd Close pi fd

// val ml_test4 : monitorable_prop -> ML unit
// let ml_test4 = export test4

// let _ = 
//   try_with
//     (fun _ -> 
//       ml_test4 pitrue;
//       FStar.IO.print_any "ml_test4 executed successfully with pitrue\n\n" )
//     (fun (err:exn) -> raise err)

// let _ = 
//   try_with
//     (fun _ -> ml_test4 pi')
//     (fun (err:exn) -> 
//       match err with
//       | GIO_pi_check_failed -> 
//           FStar.IO.print_any "ml_test4 failed successfully with p2\n\n" 
//       | err -> raise err)










// let test5 (pi:monitorable_prop) : GIO unit pi =
//   let fd = mixed_cmd Openfile pi "../Makefile" in
//   let msg = mixed_cmd Close pi fd in
//   dynamic_cmd Close pi fd

// val ml_test5 : monitorable_prop -> ML unit
// let ml_test5 = export test5

// let _ = 
//   try_with
//     (fun _ -> ml_test5 pitrue)
//     (fun (err:exn) -> 
//       match err with
//       | GIO_default_check_failed -> 
//           FStar.IO.print_any "ml_test5 failed successfully with pitrue\n\n" 
//       | err -> raise err)
