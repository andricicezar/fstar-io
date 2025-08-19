Notes from [Rupicola paper](https://dl.acm.org/doi/pdf/10.1145/3519939.3523706):
- Cezar: Their use case seems to be different than ours, so we may hit different challenges.
  Rupicola is designed to provide
  a proof that the compiled code satisfies the specification of the source code.
  It is more like "program synthesis" from the specs with the source code as hints.
  We want a more traditional compiler, starting from the source code,
  it provides the compiled code and proof they are in some relation, no specs involved.
  - Their approach is powerful because one can reason about chunks of code,
    which allows them to go from a functional model (source code) to imperative code in one go.
  - We want to compile F\* to OCaml, which is more like getting rid
  of annotations. The complicated case would be to relate monadic representations
  to the syntactic expressions.

- "Rupicola is implemented in Coq, using a mix of Coq lem-
mas (to relate high-level functional code patterns to low-level
imperative ones) and Ltac tactics (to guide the application of
these lemmas). Its core is very small (hundreds of lines)"
      - Cezar: Does Coq have type classes? It would be interesting to see if one can just use what already exists in F\* or if we have to implement our own variant.
      - "We designed Rupicola so that the default reaction to un-
expected input is to stop and ask for user guidance, rather
than fall back to a slower generic implementation."

- "with all extensions loaded,
we have support for arithmetic over many types (Booleans,
bounded and unbounded natural numbers, bytes, integers,
machine words), various control-flow patterns (condition-
als as well as iteration patterns like maps and folds, with
and without early exits), various flat data structures such as
mutable cells and arrays; plain and monadic binds; various
monadic extensions including the nondeterminism, state,
writer, and I/O monads and a generic free monad; and vari-
ous low-level effects and features such as stack allocation,
inline tables, intrinsics, and external functional calls. "

- "two particular
challenges: genericity in computational effects and loop-
invariant inference"

- Cezar: in section 3.3 they seem to compile vectors indexed by length.
  It seems to be a set of specific lemma for compiling vectors.
  Rupicola is extensible enough that one just adds lemmas to be able to
  support such things. Our logical relation is not easily extensible. 
  How could we make it more extensible? Can we define it using type classes?
  Probably yes, but then wouldn't it be difficult to use it to state lemmas
  and prove them by induction?

- Cezar: in 3.4.1, extensional effects, they can compile lambdas in this
  scenario: `bind ma k`.
  I don't really understand how the `value is now constrained
  by the computation ma`.