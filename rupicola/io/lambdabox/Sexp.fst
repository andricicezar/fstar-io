module Sexp

(** S-expression data types used to interact with Peregrine (AST output).
    Reference: https://github.com/peregrine-project/peregrine-tool/blob/master/doc/format.md *)

type atom =
| Num : int -> atom
| Str : string -> atom
| Raw : string -> atom

type sexp =
| Atom : atom -> sexp
| List : list sexp -> sexp

let raw (s: string) : sexp = Atom (Raw s)

let num (n: int) : sexp = Atom (Num n)

let str (s: string) : sexp = Atom (Str s)

let slist (l: list sexp) : sexp = List l

open FStar.String
open FStar.List.Tot

let digit_to_string (d: nat{d < 10}) : string =
  match d with
  | 0 -> "0" | 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
  | 5 -> "5" | 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9"

let rec nat_to_string (n: nat) : Tot string (decreases n) =
  if n < 10 then digit_to_string n
  else nat_to_string (n / 10) ^ digit_to_string (n % 10)

let int_to_string (n: int) : string =
  if n < 0 then "-" ^ nat_to_string (-n)
  else nat_to_string n

let char_to_escaped_string (c: FStar.Char.char) : string =
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\n' then "\\n"
  else if c = '\t' then "\\t"
  else if c = '\r' then "\\r"
  else String.make 1 c  (* fallback for other chars *)

let escape_string (s: string) : string =
  concat "" (List.Tot.map char_to_escaped_string (String.list_of_string s))

let atom_to_string (a: atom) : string =
  match a with
  | Num n -> int_to_string n
  | Str s -> "\"" ^ escape_string s ^ "\""
  | Raw s -> s

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
