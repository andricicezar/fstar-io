# Let do notation for Dijkstra Monads

I'm trying to figure out if one can get rid off the F\*'s effect system.

#### Syntactic sugar
F\*'s effect system handles many things for the user.
This can be seen in the `Assert.fst` file, `Refinements tests`
and `partial_match`.

#### Monadic Representation for the effects
This is a problem since many of the primitive F\* effects
do not have a monadic representation, however, they can be
axiomatized as they are now.

#### Reify/reflect


#### Lifting mechanism (subeffecting)
I have a first idea on how to approach this with type classes.
I have something for normal monads in `TCPolyBind.fst`
that works pretty well.
Extending it to DMs does not seem that hard conceptually.

