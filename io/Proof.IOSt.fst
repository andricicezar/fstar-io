module Proof.IOSt

open Free.IO
open DM.IO

type iost a = trace -> io (trace * a)

let aux #a (cmd:io_cmds) argz (k:res cmd -> io (trace * a)) : io (trace * a) =
  Call cmd argz k

let rec iio_to_iost (m:iio 'a) : iost 'a =
  fun s ->
    match m with
    | Return x -> Return (s, x)
    | Call GetTrace _ fnc -> iio_to_iost (fnc s) s
    | Call cmd argz fnc ->
       let k : res cmd -> io (trace * 'a) = fun r -> iio_to_iost (fnc r) s in
       aux cmd argz k

open DM.IIO
open Hist

let histst_post a = trace * a -> trace -> Type0

let iost_interpretation #a (m : iost a) (s0 : trace) (p : histst_post a) : Type0 =
  io_interpretation (m s0) (fun r le -> p r le)

open FStar.Tactics

let rec lemma (m:iio 'a) (h:trace) (p : hist_post 'a) :
  Lemma
    (requires (iio_interpretation m h p))
    (ensures (iost_interpretation (iio_to_iost m) h (fun ((s, r)) -> p r)))
  by (
    ExtraTactics.blowup ();
    bump_nth 6;
    ExtraTactics.rewrite_lemma 8 19;
    ExtraTactics.rewrite_lemma 6 19;
    compute ();
    rewrite_eqs_from_context ();
    norm [iota];
    norm [delta_only [`%iio_to_iost]];
    dump "h"
  ) =
  match m with
  | Return _ -> ()
  | Call GetTrace argz fnc -> lemma (fnc h) h p
  | Call cmd argz fnc ->
       let k : res cmd -> io (trace * 'a) = fun r -> iio_to_iost (fnc r) s in
       aux cmd argz k
