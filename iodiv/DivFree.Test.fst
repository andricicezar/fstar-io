(** Definition of a monad with iter and requires *)

module DivFree.Test

open Util
open DivFree
open IIOSig

let body1 (fd:file_descr) : m io_sig string =
    (m_call Read fd)

let body1' (fd:file_descr) : unit -> m io_sig (either unit unit) = (fun i ->
    m_bind (body1 fd) (fun msg -> m_ret (Inl i)))

let loop1 (fd:file_descr) : m io_sig unit =
    (m_iter (body1' fd) ())

let prog1 : m io_sig unit =
  m_bind #io_sig #file_descr #unit (m_call Openfile "test") (fun fd -> // (fun (fd:int) -> m_call Close fd)
    m_bind (loop1 fd) (fun msg -> m_call Close fd)) 
