(* ASCII-only replacement for F*'s app runtime FStar_Char.ml, which depends
   on the batteries library (BatUChar) that is not available in this
   environment. The web server only deals with ASCII. *)

module U32 = FStar_UInt32

type char = int
type char_code = U32.t

let lowercase (x:char) : char =
  try Char.code (Char.lowercase_ascii (Char.chr x))
  with _ -> x

let uppercase (x:char) : char =
  try Char.code (Char.uppercase_ascii (Char.chr x))
  with _ -> x

let int_of_char (x:char) : Z.t = Z.of_int x
let char_of_int (i:Z.t) : char = Z.to_int i

let u32_of_char (x:char) : char_code = U32.of_native_int x
let char_of_u32 (x:char_code) : char = U32.to_native_int x
