(** Trick by Aseem *)

// You could use the postprocess_with attribute, that runs a metaprogram on the let definition, after it is typechecked, e.g.
module Unfold_trick

open FStar.Tactics

[@@ "opaque_to_smt"]
let n = 0

[@@ "opaque_to_smt"]
let m = 1

let t () : Tac unit = norm [delta_only [`%n; `%m]]; trefl ()

[@@ (postprocess_with t)]
let foo = n + m

let test () = assert (foo == 1)




// (the typechecker presents to the postprocess tactic a goal of the form e == ?u , and sets the definition to ?u)

// As you can see, we can also make a definition unfold after the fact using it, e.g.

[@@ "opaque_to_smt"]
let k = 0

let t' () : Tac unit = norm [delta_only [`%k]]; trefl ()

[@@ (postprocess_with t')]
unfold
let k' = k

#set-options "--no_smt"
//With no smt, this proof relies on n' being unfolded in the typechecker
let test2 () = assert (k' == 0)
