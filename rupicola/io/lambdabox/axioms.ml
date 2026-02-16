(* Runtime axioms for the STLC (IO) -> LambdaBox pipeline.
   Implements IO operations on Church-encoded values.

   LambdaBox/Peregrine value conventions (OCaml runtime):
     string:     native OCaml string (from TPrim (PrimString s))
     unit:       tt    = int 0  (nullary constructor 0)
     nat:        zero  = int 0  (nullary constructor 0)
                 succ n = block { tag=0, field[0] = n }  (only non-nullary ctor)
     sum/either: inl x = block { tag=0, field[0] = x }
                 inr y = block { tag=1, field[0] = y }
   file_descr = nat (Church-encoded nat) *)

(* Decode a Church-encoded nat to an OCaml int *)
let rec decode_nat x =
  if Obj.is_int x then 0
  else 1 + decode_nat (Obj.field x 0)

(* Encode an OCaml int as a Church-encoded nat *)
let rec encode_nat n =
  if n = 0 then Obj.repr 0
  else
    let b = Obj.new_block 0 1 in
    Obj.set_field b 0 (encode_nat (n - 1));
    b

(* Build an Inl x constructor: block { tag=0, field[0]=x } *)
let make_inl x =
  let b = Obj.new_block 0 1 in
  Obj.set_field b 0 x;
  b

(* Build an Inr x constructor: block { tag=1, field[0]=x } *)
let make_inr x =
  let b = Obj.new_block 1 1 in
  Obj.set_field b 0 x;
  b

(* Unit value: tt = int 0 *)
let unit_val = Obj.repr 0

(* File descriptor table: maps nat fds to Unix file descriptors.
   fd 0 = stdin, fd 1 = stdout, fd 2 = stderr; others opened via io_open. *)
let fd_table : (int, in_channel * out_channel) Hashtbl.t =
  let t = Hashtbl.create 8 in
  Hashtbl.add t 0 (stdin,  stdout);  (* fd 0: stdin  *)
  Hashtbl.add t 1 (stdin,  stdout);  (* fd 1: stdout — write target *)
  Hashtbl.add t 2 (stdin,  stderr);  (* fd 2: stderr *)
  t

let next_fd = ref 3

(* io_read fd : resexn string
   Read one line from the input channel associated with fd.
   Returns Inl s (OCaml string) on success, Inr () on EOF or error. *)
let def_Runtime_io_read fd =
  let n = decode_nat fd in
  match Hashtbl.find_opt fd_table n with
  | None -> make_inr unit_val
  | Some (ic, _) ->
    (try
      let line = input_line ic in
      make_inl (Obj.repr line)
    with End_of_file -> make_inr unit_val)

(* io_write fd msg : resexn unit
   Write a string to the output channel associated with fd.
   msg is a native OCaml string (from TPrim (PrimString s)).
   Returns Inl () on success, Inr () on error. *)
let def_Runtime_io_write fd msg =
  let n = decode_nat fd in
  match Hashtbl.find_opt fd_table n with
  | None -> make_inr unit_val
  | Some (_, oc) ->
    (try
      let s = (Obj.obj msg : string) in
      output_string oc s;
      flush oc;
      make_inl unit_val
    with _ -> make_inr unit_val)

(* io_open fnm : resexn file_descr
   Open a file with the given string filename.
   fnm is a native OCaml string (from TPrim (PrimString s)).
   Returns Inl fd (Church-encoded nat) on success, Inr () on error. *)
let def_Runtime_io_open fnm =
  let filename = (Obj.obj fnm : string) in
  try
    let ic = open_in filename in
    let oc = open_out_gen [Open_append; Open_creat] 0o644 filename in
    let fd = !next_fd in
    incr next_fd;
    Hashtbl.add fd_table fd (ic, oc);
    make_inl (encode_nat fd)
  with _ -> make_inr unit_val

(* io_close fd : resexn unit
   Close the file descriptor.
   Returns Inl () on success, Inr () on error. *)
let def_Runtime_io_close fd =
  let n = decode_nat fd in
  match Hashtbl.find_opt fd_table n with
  | None -> make_inr unit_val
  | Some (ic, oc) ->
    (try
      (if ic <> stdin then close_in ic);
      (if oc <> stdout && oc <> stderr then close_out oc);
      Hashtbl.remove fd_table n;
      make_inl unit_val
    with _ -> make_inr unit_val)

(* run_main f : unit
   Execute the IO program: apply f to unit, which runs all IO effects.
   f has type unit -> resexn unit (after monad erasure).
   Prints an error message if the computation returns Inr (failure). *)
let def_Runtime_run_main f =
  let result = f unit_val in
  (* result : resexn unit = Inl () | Inr () *)
  if Obj.is_block result && Obj.tag result = 1 then
    (Printf.eprintf "IO program returned an error\n"; flush stderr);
  unit_val
