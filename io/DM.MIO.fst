module DM.MIO

open FStar.Tactics

open IO.Sig
open IO.Sig.Call
open DM.IO

let trivial_wp a : hist a =
  fun p _ -> forall l r. p l r

effect MIO (a:Type) = IOwp a (trivial_wp a)
#set-options "--print_implicits"
let lemma_trivial_wp_theta (cmd:io_cmds) (argz:io_sig.args cmd) :
  Lemma (trivial_wp (io_sig.res cmd argz) `hist_ord #_ #(io_sig.res cmd argz)` dm_io_theta (io_call cmd argz)) = admit ()

let unsafe_cmd
  (cmd : io_cmds)
  (argz : io_sig.args cmd) :
  MIO (io_sig.res cmd argz) =
    IOwp?.reflect (
      lemma_trivial_wp_theta cmd argz;
      io_call cmd argz)
