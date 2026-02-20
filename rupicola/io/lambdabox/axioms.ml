(* Runtime axioms for the STLC (IO) -> LambdaBox pipeline.
   Implements IO operations.

   LambdaBox/Peregrine value conventions (OCaml runtime):
     string:     native OCaml string (from TPrim (PrimString s))
     unit:       tt    = int 0  (nullary constructor 0)
     sum/either: inl x = block { tag=0, field[0] = x }
                 inr y = block { tag=1, field[0] = y }
     file_descr = nat *)

(* Decode a nat to an OCaml int *)
let rec decode_nat x =
  if Obj.is_int x then 0
  else 1 + decode_nat (Obj.field x 0)

(* Encode an OCaml int as a nat *)
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

let unit_val = Obj.repr 0

(* File descriptor table: maps nat fds to a single Unix file descriptor.
   fd 0 = stdin, fd 1 = stdout, fd 2 = stderr; others opened via io_open. *)
let fd_table : (int, Unix.file_descr) Hashtbl.t =
  let t = Hashtbl.create 8 in
  Hashtbl.add t 0 Unix.stdin;
  Hashtbl.add t 1 Unix.stdout;
  Hashtbl.add t 2 Unix.stderr;
  t

let next_fd = ref 3

let def_Runtime_io_read fd =
  let n = decode_nat fd in
  match Hashtbl.find_opt fd_table n with
  | None -> make_inr unit_val
  | Some ufd ->
    (try
      let buf = Buffer.create 64 in
      let b = Bytes.create 1 in
      let rec read_line () =
        let got = Unix.read ufd b 0 1 in
        if got = 0 then ()
        else
          let c = Bytes.get b 0 in
          if c = '\n' then ()
          else begin Buffer.add_char buf c; read_line () end
      in
      read_line ();
      make_inl (Obj.repr (Buffer.contents buf))
    with _ -> make_inr unit_val)

let def_Runtime_io_write (fd : Obj.t) (msg : Obj.t) : Obj.t =
  let n = decode_nat fd in
  match Hashtbl.find_opt fd_table n with
  | None -> make_inr unit_val
  | Some ufd ->
    (try
      let s = (Obj.obj msg : string) in
      let b = Bytes.of_string s in
      let len = Bytes.length b in
      let _ = Unix.write ufd b 0 len in
      make_inl unit_val
    with _ -> make_inr unit_val)

let def_Runtime_io_open fnm =
  let filename = (Obj.obj fnm : string) in
  try
    let ufd = Unix.openfile filename
      [Unix.O_RDWR; Unix.O_CREAT;] 0o644 in
    let fd = !next_fd in
    incr next_fd;
    Hashtbl.add fd_table fd ufd;
    make_inl (encode_nat fd)
  with _ -> make_inr unit_val

let def_Runtime_io_close fd =
  let n = decode_nat fd in
  match Hashtbl.find_opt fd_table n with
  | None -> make_inr unit_val
  | Some ufd ->
    (try
      (if ufd <> Unix.stdin && ufd <> Unix.stdout && ufd <> Unix.stderr then
        Unix.close ufd);
      Hashtbl.remove fd_table n;
      make_inl unit_val
    with _ -> make_inr unit_val)

let def_Runtime_string_eq s1 s2 =
    String.equal s1 s2

let def_Runtime_run_main f agent =
  let result = f agent in
  (match result with
  | false -> print_string "false"
  | true -> print_string "true");
  unit_val
