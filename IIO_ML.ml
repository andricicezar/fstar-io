open Prims

let global_trace : IO_Free.trace ref = ref []

let (ml_gettrace : unit -> Obj.t) =
  fun () -> Obj.magic (!global_trace)

let (ml_updatetrace : IO_Free.event -> unit) =
  fun e -> global_trace := !global_trace @ [e]

let (ml_openfile : Obj.t -> Obj.t) =
  fun file_name ->
    try (
      let r = Unix.openfile (Obj.magic file_name) [O_RDONLY] 0x700 in
      ml_updatetrace (IO_Free.EOpenfile ((Obj.magic file_name), (FStar_Pervasives.Inl (Obj.magic r))));
      Obj.magic r
    ) with err -> (
      ml_updatetrace (IO_Free.EOpenfile ((Obj.magic file_name), (FStar_Pervasives.Inr (Obj.magic err))));
      raise err
    )

let (ml_read : Obj.t -> Obj.t) =
  fun fd ->
    let buff = Bytes.make 50 '\000' in
    let c = Unix.read (Obj.magic fd) buff 0 50 in
    Obj.magic (Bytes.to_string buff)

let (ml_close : Obj.t -> unit) =
  fun a30 ->
    (fun fd ->
        Unix.close (Obj.magic fd)) a30

let (ml_io_all : IO_Free.cmds -> Obj.t -> Obj.t) =
  fun cmd ->
    fun args ->
      match cmd with
      | IO_Free.GetTrace -> Obj.repr (ml_gettrace ())
      | IO_Free.Openfile -> Obj.repr (ml_openfile args)
      | IO_Free.Read -> Obj.repr (ml_read args)
      | IO_Free.Close -> Obj.repr (ml_close args)
let (ml_io_execute : IO_Free.cmds -> Obj.t -> unit IO_Free.resm) =
  fun cmd ->
    fun argz ->
      try
        (fun uu___ ->
           let uu___1 = ml_io_all cmd argz in FStar_Pervasives.Inl uu___1) ()
      with | err -> FStar_Pervasives.Inr err
