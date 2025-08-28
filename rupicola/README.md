### To try next

Next challenges:
* Limitations of type classes
  - [ ] Pattern matching -- an inherent problem of F*, one cannot abstract over them anyway. Not a typeclass problem.
      	Typeclasses do not add any expressivity to F*. We're limited by what we can abstract away in F*.
	For PMs, maybe one can generate instances on the fly. There is another project requiring this.
  - [ ] How powerful is phase1? A lot seems to happen, which can be problematic if we want to claim any kind of end-to-end result.
        Typeclasses in F* may be less fancy than other languages. We expect it to be portable.
* Features of Dependently Typed Languages:
  - [ ] Compiling fixpoints (may work with F* if one defines instances for different arrities). Stuck [FStarLang/FStar#3991](https://github.com/FStarLang/FStar/issues/3991)
  - [x] Compiling pairs
    - [ ] Automation problems when compiling fst / snd. [See here](https://github.com/andricicezar/fstar-io/blob/010dda6a013cb23288ad14019eca03b2bea2bdd0/rupicola/stlc_v2/Compiler.fst#L290).
  - [ ] Compiling Dependent Pairs/Functions. See attempt on [dpair2](https://github.com/andricicezar/fstar-io/blob/dpairs2/rupicola/stlc_v2/Compiler.fst#L359) branch.
* Features of F\*:
  - [x] Compiling refined types
    - [ ] [Automation does not work when erasing](https://github.com/andricicezar/fstar-io/blob/010dda6a013cb23288ad14019eca03b2bea2bdd0/rupicola/refinements/Compiler.fst#L333)
  - [ ] Compiling arrows with pre-post-conditions
  - [ ] Compiling effects?
* Compiling the identity monad
  - [ ] Identity monad
  - [ ] State/IO?
    * if we try to do state, I suppose we would have to reproduce the proofs from Amal's Thesis, which are very complicated. From what I know, separation logic helps with those proofs. Any way to take advantage of Pulse for that (not ideal since it gives us partial correctness)? Probably it is better to start with IO.

TODOs:
- [ ] Improve performance in HOC cases (see `test1_hoc` in [Compiler.fst](./stlc/Compiler.fst))
- [ ] [Makefile](./stlc/Makefile) fails with weird error

### Notes from [Rupicola paper](https://dl.acm.org/doi/pdf/10.1145/3519939.3523706):
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
      - Cezar: Does Coq have type classes? It would be interesting
      to see if one can just use what already exists in F\* or if we have to implement our own variant.
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
