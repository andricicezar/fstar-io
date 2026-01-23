module Sexp

(** S-expression data types following the Ceres format.
    Reference: https://github.com/peregrine-project/peregrine-tool/blob/ast-format/doc/format.md *)

(** Atomic values in S-expressions *)
type atom =
| Num : int -> atom       (* Integers *)
| Str : string -> atom    (* Literal strings with escaping *)
| Raw : string -> atom    (* Simple atoms/symbols - should fit in alphabet [A-Za-z0-9'=+*/:!?@#$%^&<>.,|_~-] *)

(** S-expression type *)
type sexp =
| Atom : atom -> sexp
| List : list sexp -> sexp

(** Helper constructor for raw atoms (symbols) *)
let raw (s: string) : sexp = Atom (Raw s)

(** Helper constructor for numeric atoms *)
let num (n: int) : sexp = Atom (Num n)

(** Helper constructor for string atoms *)
let str (s: string) : sexp = Atom (Str s)

(** Helper constructor for lists *)
let slist (l: list sexp) : sexp = List l

(** String conversion for S-expressions *)
open FStar.String
open FStar.List.Tot

(** Convert a single digit (0-9) to its string representation *)
let digit_to_string (d: nat{d < 10}) : string =
  match d with
  | 0 -> "0" | 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
  | 5 -> "5" | 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9"

(** Convert a natural number to string using string literals *)
let rec nat_to_string (n: nat) : Tot string (decreases n) =
  if n < 10 then digit_to_string n
  else nat_to_string (n / 10) ^ digit_to_string (n % 10)

(** Convert an integer to string *)
let int_to_string (n: int) : string =
  if n < 0 then "-" ^ nat_to_string (-n)
  else nat_to_string n

(** Convert a character to string for escaping - using common cases *)
let char_to_escaped_string (c: FStar.Char.char) : string =
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if c = '\r' then "\\r"
  else String.make 1 c  (* fallback for other chars *)

(** Escape a string for S-expression output *)
let escape_string (s: string) : string =
  concat "" (List.Tot.map char_to_escaped_string (String.list_of_string s))

(** Convert atom to string *)
let atom_to_string (a: atom) : string =
  match a with
  | Num n -> int_to_string n
  | Str s -> "\"" ^ escape_string s ^ "\""
  | Raw s -> s

(** Convert sexp to string *)
let rec sexp_to_string (s: sexp) : Tot string (decreases s) =
  match s with
  | Atom a -> atom_to_string a
  | List [] -> "()"
  | List xs -> "(" ^ sexp_list_to_string xs ^ ")"

and sexp_list_to_string (xs: list sexp) : Tot string (decreases xs) =
  match xs with
  | [] -> ""
  | [x] -> sexp_to_string x
  | x :: rest -> sexp_to_string x ^ " " ^ sexp_list_to_string rest
