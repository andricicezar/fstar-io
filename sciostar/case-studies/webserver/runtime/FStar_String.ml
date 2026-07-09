(* ASCII-only replacement for F*'s app runtime FStar_String.ml, which depends
   on the batteries library (BatUTF8/BatString) that is not available in this
   environment. The web server only deals with ASCII. *)

let make i c = String.make (Z.to_int i) (Char.chr c)
let strcat s t = s ^ t
let op_Hat s t = strcat s t

let string_nsplit (s:string) (sep:string) : string list =
  if s = "" then []
  else if sep = "" then [s]
  else begin
    let seplen = String.length sep in
    let n = String.length s in
    let parts = ref [] in
    let start = ref 0 in
    let i = ref 0 in
    while !i <= n - seplen do
      if String.sub s !i seplen = sep then begin
        parts := String.sub s !start (!i - !start) :: !parts;
        start := !i + seplen;
        i := !i + seplen
      end else incr i
    done;
    List.rev (String.sub s !start (n - !start) :: !parts)
  end

let split seps s =
  let rec repeat_split acc = function
    | [] -> acc
    | sep::seps ->
       let usep = String.make 1 (Char.chr sep) in
       let l = List.flatten (List.map (fun x -> string_nsplit x usep) acc) in
       repeat_split l seps in
  repeat_split [s] seps

let compare (x:string) (y:string) = Z.of_int (String.compare x y)
type char = FStar_Char.char
let concat = String.concat
let length s = Z.of_int (String.length s)
let strlen s = length s

let substring s i j = String.sub s (Z.to_int i) (Z.to_int j)
let sub = substring

let get (s:string) (i:Z.t) : char = Char.code s.[Z.to_int i]
let collect (f:char -> string) (s:string) =
  let r = ref "" in
  String.iter (fun c -> r := !r ^ f (Char.code c)) s; !r
let lowercase = String.lowercase_ascii
let uppercase = String.uppercase_ascii
let escaped = String.escaped
let index = get
let index_of (s:string) (c:char) : Z.t =
  match String.index_opt s (Char.chr c) with
  | Some i -> Z.of_int i
  | None -> Z.of_int (-1)
let list_of_string s = List.init (String.length s) (fun i -> Char.code s.[i])
let string_of_list l = String.init (List.length l) (fun i -> Char.chr (List.nth l i))
let string_of_char (c:char) = String.make 1 (Char.chr c)
