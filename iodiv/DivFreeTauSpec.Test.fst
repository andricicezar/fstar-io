module DivFreeTauSpec.Test

open FStar.Tactics

open DivFreeTauSpec
open IIOSigSpec

(** 
let dm sg (w_act : action_iwp sg) (a : Type) (w : iwp a) =
  c : m sg a { theta w_act c `ile` w }

**)

let triv #a : iwp a =
  iprepost (fun _ -> True) (fun h r -> True) 

let r_div : iwp unit =
  iprepost (fun _ -> True) (fun h r -> diverges r)

let r_cv : iwp unit =
  iprepost (fun _ -> True) (fun h r -> terminates r)

(** *** Append assert false to divergent code **)

let assert_false : iwp unit =
  iprepost (fun _ -> False) (fun h r -> True)

let _ = assert (i_bind r_div (fun _ -> assert_false) `ile` r_div)
(** This is not surprising taking in consideration the definition of `i_bind`.
   If we unfold it, we obtain something similar to:
   (fun post hist ->
      w (fun r ->
        match r with
        | Cv tr x -> wf x (ishift_post tr post) (rev_acc (to_trace tr) hist)
        | Dv st -> post (Dv st)
        ) hist)

   and here one can see that `wf` (which is `(fun _ -> testfalse)` in our case)
   is not used in the `Dv` branch.

   TODO: is this a problem?
**)


[@expect_failure] (** fails goal 2 that requires to prove False **)
let _ = assert (i_bind r_cv (fun _ -> assert_false) `ile` r_cv) by (norm [delta_only [`%r_cv;`%iprepost]]; explode ();dump "H")


(** *** Actions **)

let _ = assert (i_open "test.txt" `ile` triv)
let _ = assert (i_bind (i_open "test.txt") (fun _ -> i_ret ()) `ile` triv)
let _ = assert (i_bind (i_open "test.txt") (fun _ -> i_ret ()) `ile` r_cv)
  
[@expect_failure]
let _ = assert (i_bind (i_open "test.txt") (fun _ -> i_ret ()) `ile` r_div) by (norm [delta_only [`%r_div;`%iprepost;`%i_ret;`%ishift_post;`%as_iwp;`%ishift_post;`%ret_fin_trace];zeta]; explode (); bump_nth 2; compute ();explode (); dump "H")
