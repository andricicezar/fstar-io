module Examples

open QTyp

let ut_unit = ()
let ut_true = true
let ut_false = false

val var0 : fs_oexp (extend qBool empty) qBool
let var0 fsG = hd fsG

val var1 : fs_oexp (extend qBool (extend qBool empty)) qBool
let var1 fsG = hd (tail fsG)

let var2 : fs_oexp (extend qBool (extend qBool (extend qBool empty))) qBool =
  fun fsG -> hd (tail (tail fsG))

let var3 : fs_oexp (extend qBool (extend qBool (extend qBool (extend qBool empty)))) qBool =
  fun fsG -> hd (tail (tail (tail fsG)))

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
