module WebServer.Compiled

open FStar.Ghost
open FStar.Tactics
open FStar.List.Tot

open Compiler.Model
open WebServer

let check_send_pre : tree pck_rc = 
  Node 
    (| Bytes.bytes, unit, (fun msg h _ _ -> (Bytes.length msg) < 500) |)
    Leaf
    Leaf

let export_send (#fl:erased tflag) : exportable ((msg:Bytes.bytes -> IIO (resexn unit) fl (fun h -> Bytes.length msg < 500)
                                            (fun _ _ lt -> exists fd r. lt == [EWrite true (fd,msg) r] ))) Utils.pi check_send_pre fl =
  exportable_arrow_pre_post_args Bytes.bytes unit
    (fun msg h ->  Bytes.length msg < 500)
    (fun msg _ _ lt -> exists fd r. lt == [EWrite true (fd,msg) r])
    #()
    #()


let check_handler_post : tree pck_rc =
  Node (| file_descr, resexn unit, (fun client _ _ lt -> Utils.wrote_at_least_once_to client lt) |)
    check_send_pre 
    Leaf

(* Breaks F* *)
instance import_request_handler (fl:erased tflag) : safe_importable (req_handler fl) Utils.pi check_handler_post fl = admit ()
(* {
  swtyp = file_descr -> Bytes.bytes -> export_send.wtyp -> IIOpi (resexn unit) fl Utils.pi;
  c_swtyp = weak_arrow3 fl Utils.pi file_descr Bytes.bytes export_send.wtyp #export_send.c_wtyp(resexn unit);
  safe_import = (fun (f:file_descr -> Bytes.bytes -> export_send.wtyp -> IIOpi (resexn unit) fl Utils.pi) eff_rcs -> 
    let f' : req_handler fl = (fun fd req -> 
      let f'' = f fd req in
      (safe_importable_arrow_pre_post_res 
        #_ #_
        #Utils.pi
        #check_handler_post
        #fl
        (fun _ _ -> True)
        (fun _ h r lt -> enforced_locally Utils.pi h lt /\ 
          (Utils.wrote_at_least_once_to fd lt \/ Inr? r))
        ((fun () -> admit ()) ())
        ((fun () -> admit ()) ())
        #export_send).safe_import f'' eff_rcs) in
    f'
  )
}*)


let interface : src_interface = {
  pi = Utils.pi;
  phi = Utils.phi;
  ct = req_handler;
  ct_rcs = check_handler_post;
  ct_importable = (fun fl -> import_request_handler fl); 
  psi = (fun _ _ lt -> Utils.every_request_gets_a_response lt);
}

let compiled_webserver = 
  comp.compile_pprog #interface webserver 

(** TODO: compile webserver to ML/Tot **)
