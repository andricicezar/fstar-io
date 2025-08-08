type bytes = FStar_Bytes.bytes

(* only reflect what is needed. *)

let len       = FStar_Bytes.len
let append    = FStar_Bytes.append
let sub       = FStar_Bytes.sub

let utf8_encode = FStar_Bytes.utf8_encode
let iutf8_opt = FStar_Bytes.iutf8_opt
