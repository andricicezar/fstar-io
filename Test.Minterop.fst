module Test.Minterop

open Common
open IO.Free
open IO.Effect
open IIO.Effect
open MIO.Effect
open Minterop

noeq type interface = {
  a : Type; ad : exportable a;
  b : Type; bdi : importable b; bde : exportable b;
  c : Type; cd : exportable c;
  pre:a -> trace -> Type0;
  cpre : checkable2 pre;
  post:a -> trace -> (m:maybe b) -> trace -> (r:Type0{Inr? m ==> r});
  cpost : checkable4 post;
}

// the plugin will be written in GIO (should be ML?)
type plugin_type (i:interface) (pi:monitorable_prop) = x:i.a -> IIO i.b pi (i.pre x) (i.post x)
type webserver_type (i:interface) (pi:monitorable_prop) = (plugin:plugin_type i pi) -> IIO i.c pi (fun _ -> True) (fun _ _ _ -> True)

(*** Example 1: simple interface where pre and post return always
true ***)

val i1pre : file_descr -> trace -> bool
let i1pre fd h = true
  
val i1post : file_descr -> trace -> maybe unit -> trace -> bool
let i1post fd h r le = true 

let i1 : interface = {
  a = file_descr; 
    ad = exportable_ml file_descr #ml_file_descr;
  b = unit; 
    bdi = importable_safe_importable unit #(safe_importable_ml unit #ml_unit);
    bde = exportable_ml unit #ml_unit;
  c = unit;
    cd = exportable_ml unit #ml_unit;
  pre = (fun x h -> i1pre x h);
  cpre = general_is_checkable2 file_descr trace i1pre;
  post = (fun x h r le -> i1post x h r le);
  cpost = general_is_checkable4 file_descr trace (maybe unit) trace i1post;
}

let pi1 : monitorable_prop = fun _ _ -> true

val webserver1 : webserver_type i1 pi1
let webserver1 plugin =
  rev_append_rev_append ();
  let fd = static_cmd pi1 Openfile "Demos.fst" in
  plugin fd

let ml_plugin1 : file_descr -> MIO unit = fun fd ->
  unsafe_cmd Close fd

val plugin1 : plugin_type i1 pi1
let plugin1 = safe_import #_ #(
  importable_MIO_IIO 
    i1.a #i1.ad 
    i1.b #i1.bdi
    pi1
    i1.pre #i1.cpre
    i1.post #i1.cpost) ml_plugin1

val app1 : unit -> IIO unit pi1 (fun _ -> True) (fun _ _ _ -> True)
let app1 () = webserver1 plugin1


(** Example 2: the post condition of the plugin requires that the 
    file_descr given as argument to remain opened. Probably this 
    should be enforced by pi. **)

val i2pre : file_descr -> trace -> bool
let i2pre fd h = true
  
val i2post : file_descr -> trace -> (r:maybe unit) -> trace -> (x:bool{Inr?r ==> x == true})

let rec not_closed (fd:file_descr) (h: trace) :
  Tot bool =
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EClose fd' _ -> 
                    if fd = fd' then false
                    else not_closed fd tail
               | _ -> not_closed fd tail

let i2post fd h r le = 
  if (Inl? r) then not_closed fd le
  else true

let i2 : interface = {
  a = file_descr; 
    ad = exportable_ml file_descr #ml_file_descr;
  b = unit; 
    bdi = importable_safe_importable unit #(safe_importable_ml unit #ml_unit);
    bde = exportable_ml unit #ml_unit;
  c = unit;
    cd = exportable_ml unit #ml_unit;
  pre = (fun x h -> i2pre x h);
  cpre = general_is_checkable2 file_descr trace i2pre;
  post = (fun x h r le -> i2post x h r le);
  cpost = general_is_checkable4 file_descr trace (maybe unit) trace i2post;
}


let pi2 : monitorable_prop = fun _ _ -> true

val webserver2 : webserver_type i2 pi2
let webserver2 plugin =
  rev_append_rev_append ();
  let fd = static_cmd pi2 Openfile "Demos.fst" in
  plugin fd;
  (** TODO: try to read from fd. This should be safe to 
  do because the post guarantees the fd is open.
  -  it seems F* can not prove automatically 
  bodies that contain more than 3 functions**)
  // let msg = static_cmd pi2 Read fd in
  ()

let ml_plugin2 : file_descr -> MIO unit = fun fd ->
  unsafe_cmd Close fd

val plugin2 : plugin_type i2 pi2
let plugin2 = safe_import #_ #(
  importable_MIO_IIO 
    i2.a #i2.ad 
    i2.b #i2.bdi
    pi2
    i2.pre #i2.cpre
    i2.post #i2.cpost) ml_plugin2

val app2 : unit -> IIO unit pi2 (fun _ -> True) (fun _ _ _ -> True)
let app2 () = webserver2 plugin2

(** Example 3: the post condition of the plugin requires that the 
    file_descr returned to be opened remain opened. **)

val i3pre : unit -> trace -> bool
let i3pre fd h = true
  
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

val i3post : unit -> trace -> (r:maybe file_descr) -> trace -> (x:bool{Inr?r ==> x == true})
let i3post fd h r le = 
  if (Inl? r) then is_open (Inl?.v r) (apply_changes h le)
  else true

let i3 : interface = {
  a = unit; 
    ad = exportable_ml unit #ml_unit;
  b = file_descr; 
    bdi = importable_safe_importable file_descr #(safe_importable_ml file_descr #ml_file_descr);
    bde = exportable_ml file_descr #ml_file_descr;
  c = unit;
    cd = exportable_ml unit #ml_unit;
  pre = (fun x h -> i3pre x h);
  cpre = general_is_checkable2 unit trace i3pre;
  post = (fun x h r le -> i3post x h r le);
  cpost = general_is_checkable4 unit trace (maybe file_descr) trace i3post;
}

let pi3 : monitorable_prop = (fun s0 action -> 
  match action with
  | (| Read, fd |) -> is_open fd s0
  | _ -> true)

val webserver3 : webserver_type i3 pi3
let webserver3 plugin =
  rev_append_rev_append ();
  let fd = plugin () in
  (** This is nice. pi3 is enforced statically and
  F* can automatically prove that fd is open from the 
  post condition **)
  let msg = static_cmd pi3 Read fd in
  ()

let ml_plugin3 : unit -> MIO file_descr = fun () ->
  unsafe_cmd Openfile "Demo.fst"

val plugin3 : plugin_type i3 pi3
let plugin3 = safe_import #_ #(
  importable_MIO_IIO 
    i3.a #i3.ad 
    i3.b #i3.bdi

    pi3
    i3.pre #i3.cpre
    i3.post #i3.cpost) ml_plugin3

val app3 : unit -> IIO unit pi3 (fun _ -> True) (fun _ _ _ -> True)
let app3 () = webserver3 plugin3


(** Example 4: the post condition of the plugin forces the
    plugin to have only one Openfile. **)

val i4pre : unit -> trace -> bool
let i4pre fd h = true
  
let rec only_one_openfile (ok:bool) (h:trace) :
  Tot bool (decreases h)=
  match h with
  | [] -> false
  | h :: tail -> match h with
               | EOpenfile _ _ ->
                   if ok then only_one_openfile false tail
                   else false
               | _ -> only_one_openfile ok tail 

val i4post : unit -> trace -> (r:maybe file_descr) -> trace -> (x:bool{Inr?r ==> x == true})
let i4post fd h r le = 
  if (Inl? r) then only_one_openfile true le
  else true

let i4 : interface = {
  a = unit; 
    ad = exportable_ml unit #ml_unit;
  b = file_descr; 
    bdi = importable_safe_importable file_descr #(safe_importable_ml file_descr #ml_file_descr);
    bde = exportable_ml file_descr #ml_file_descr;
  c = unit;
    cd = exportable_ml unit #ml_unit;
  pre = (fun x h -> i4pre x h);
  cpre = general_is_checkable2 unit trace i4pre;
  post = (fun x h r le -> i4post x h r le);
  cpost = general_is_checkable4 unit trace (maybe file_descr) trace i4post;
}

let pi4 : monitorable_prop = (fun _ _ -> true)

open FStar.Tactics 

let webserver4 : webserver_type i4 pi4 = (fun plugin -> 
  rev_append_rev_append ();
  let fd = plugin () in
  ())

// let ml_plugin4 : unit -> MIO file_descr = fun () ->
//   unsafe_cmd Openfile "Demo.fst"

// val plugin4 : plugin_type i4 pi4
// let plugin4 = safe_import #_ #(
//   importable_MIO_IIO 
//     i4.a #i4.ad 
//     i4.b #i4.bdi

//     pi4
//     i4.pre #i4.cpre
//     i4.post #i4.cpost) ml_plugin4

// val app4 : unit -> IIO unit pi4 (fun _ -> True) (fun _ _ _ -> True)
// let app4 () = webserver4 plugin4
