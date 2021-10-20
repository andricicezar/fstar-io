module DM.IIO.Tactics

open FStar.Tactics
open ExtraTactics

open Common
open Free.IO
open DM.IIO

(** This tactic has the role to help F*/SMT to prove
larger function bodies in the IIO Effect. This is
needed for function bodies that contain a function
call to other IIO computations.

CA: I don't like that it explodes the goal. **)
let iio_tactic () : Tac unit =
    l_to_r [`List.append_l_nil; `List.append_nil_l];
    let lem = pose_lemma (`(rev_append_rev_append ())) in
    norm [delta_only [`%iio_post;`%apply_changes]];
    explode ()
