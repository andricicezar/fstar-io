# Let do notation for Dijkstra Monads

I'm trying to figure out if one can get rid of the F\*'s effect system
by working directly with the monadic representation.

#### Syntactic sugar
F\*'s effect system handles for the user the interaction
with squash, refinements and pattern matching (match).

When working with the monadic representation directly,
dealing with refinements and pattern matching is pretty verbose.
This can be seen in the `Assert.fst` file, `Refinements tests`
and `partial_match`.

Also see: https://github.com/FStarLang/FStar/blob/master/examples/misc/MonadicLetBindings.fst

- [ ] TODO: what else?

#### Monadic Representation for the effects
This is a problem since many of the primitive F\* effects
do not have a monadic representation, however, they can be
axiomatized (the way they are now).

#### Lifting mechanism (subeffecting)
I have a first idea on how to approach this with type classes.
I have something for normal monads in `TCPolyBind.fst`
that works pretty well.
Extending it to DMs does not seem conceptually complicated.

#### Reify/reflect

A reifiable/reflectable effect, is an effect whose computational monad
is not hidden.

To make an effect NOT reifiable,
one can hide the computational monad behind a module interface,
and then one has to use the subcomp combinator.
I called it `do` since mostly one uses it only once for the entire
body of the function. Again, when pattern matching,
it is more complicated because one has to use it on each branch.
This can be seen in `Assert.fsti` and `AssertTest.fst`.

Would be interesting to explore if one can expose a ghost reify so that
one is still able to reason.
