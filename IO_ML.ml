open Prims
let (ml_openfile : string -> Unix.file_descr) =
  fun file_name ->
    Unix.openfile file_name [O_RDONLY] 0x700

let (ml_read : Unix.file_descr -> string) =
  fun fd ->
    let buff = Bytes.make 50 '\000' in
    let c = Unix.read fd buff 0 50 in
    Bytes.to_string buff

let (ml_close : Unix.file_descr -> unit) =
  fun a30 ->
    (fun fd ->
        Unix.close fd) a30

let (ml_io_all : IO_Free.io_cmds -> Obj.t -> Obj.t) =
  fun cmd ->
    fun args ->
      match cmd with
      | IO_Free.Openfile -> Obj.repr (ml_openfile (Obj.magic args))
      | IO_Free.Read -> Obj.repr (ml_read (Obj.magic args))
      | IO_Free.Close -> Obj.repr (ml_close (Obj.magic args))

let (ml_io_execute : IO_Free.io_cmds -> Obj.t -> Obj.t Common.maybe) =
  fun cmd ->
    fun argz ->
      try
        (fun uu____641 ->
           let uu____642 = ml_io_all cmd argz in
           FStar_Pervasives.Inl uu____642) ()
      with | err -> FStar_Pervasives.Inr err
                       
let (ml_io_execute : IO_Free.io_cmds -> Obj.t -> Obj.t Common.maybe) =
  fun cmd ->
    fun argz ->
      try
        (fun uu____641 ->
           let uu____642 = ml_io_all cmd argz in
           FStar_Pervasives.Inl uu____642) ()
      with | err -> FStar_Pervasives.Inr err
