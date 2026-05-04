module Examples

let ut_unit = ()
let ut_true = true
let ut_false = false

let constant (x: bool) : bool =
  true

let identity : bool -> bool =
  fun x -> x

let thunked_id : bool -> bool -> bool =
  fun x y -> y

let proj1 : bool -> bool -> bool -> bool =
  fun x y z -> x

let proj2 : bool -> bool -> bool -> bool =
  fun x y z -> y

let proj3 : bool -> bool -> bool -> bool =
  fun x y z -> z

let apply_top_level_def : bool -> bool =
  fun x -> thunked_id x true

let apply_top_level_def' : bool -> bool -> bool =
  fun x y -> thunked_id x y

let papply__top_level_def : bool -> bool -> bool =
  fun x -> thunked_id x

let apply_arg : (unit -> unit) -> unit =
  fun f -> f ()

let apply_arg2 : (bool -> bool -> bool) -> bool =
  fun f -> f true false

let papply_arg2 : (bool -> bool -> bool) -> bool -> bool =
  fun f -> f true

let anif : bool = if true then false else true

let negb : bool -> bool =
  fun x -> if x then false else true

let negb_pred : (bool -> bool) -> bool -> bool =
  fun f x -> negb (f x)

let if2 : bool -> bool -> bool =
  fun x y -> if x then false else y

let callback_return : bool -> (bool -> bool) =
  fun x -> if x then (fun _ -> x) else (fun z -> z)

let callback_return' : bool -> (bool -> bool) =
  fun x -> if x then (fun _ -> x) else identity

let make_pair : bool -> bool -> (bool & bool) =
  fun x y -> (x, y)

let pair_of_functions : (bool -> bool) & (bool -> bool -> bool) =
  (fun x -> negb x), (fun x y -> y)

let pair_of_functions2 : (bool -> bool) & (bool -> bool -> bool) =
  (negb, if2)

let fst_pair : bool = fst (true, ())
let wrap_fst : (bool & bool) -> bool = fun p -> fst p
let wrap_fst_pa : (bool & bool) -> bool = fst

let snd_pair : unit = snd (true, ())
let wrap_snd : (bool & unit) -> unit = fun p -> snd p
let wrap_snd_pa : (bool & unit) -> unit = snd

let a_few_lets : bool -> unit =
  fun x ->
    let p = (x, x) in
    let y = x in
    let z = fst p in
    let g = (y, z) in
    ()

let inl_true : either bool unit = Inl true
let inr_unit : either bool unit = Inr ()
let return_either : bool -> either unit unit =
  fun x -> if x then Inl () else Inr ()

let match_either : either bool bool -> bool =
  fun x ->
    match x with
    | Inl x -> x
    | Inr x -> x

let match_either' : either bool bool -> bool =
  fun x ->
    match x with
    | Inr x -> x
    | Inl x -> x

let match_either_arg : either bool bool -> bool -> bool =
  fun x y ->
    match x with
    | Inl x -> x
    | Inr x -> y

let greeting (b:bool) : string = if b then "hello" else "goodbye"
let const_str : string = "constant"

let nat_zero : nat = 0
let nat_one  : nat = 1
let nat_two  : nat = 2

let nat_succ_fn : nat -> nat = fun n -> n + 1

let nat_add2 : nat -> nat = fun n -> IOStar.io_nrec 2 n (fun x -> x + 1)

let nat_five1 : nat = IOStar.io_nrec 3 2 (fun x -> x + 1)

let nat_five2 : nat = nat_add2 3

let fact_five : nat = snd (IOStar.io_nrec 5 (0, 1) (fun (v : nat*nat) -> (fst v + 1, IOStar.io_nrec (fst v + 1) 0 (fun (a : nat) -> IOStar.io_nrec (snd v) a (fun (w : nat) -> w + 1)))))
