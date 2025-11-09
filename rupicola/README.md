### To try next

#### The predicate for quotation
- [x] STLC (see `stlc` folder)
  - [ ] Problems with unification. See TODO in [`stlc/QExp.fst`](./stlc/QExp.fst).
      - [ ] Pairs. `pair_of_functions` and `pair_of_functions2`
      - [ ] Top level definitions. `apply_top_level_def`, `apply_top_level_def'` and `papply_top_level_def`
      - [ ] HO cases. `callback_return` and `callback_return'`
- [ ] Free Monad
  - [ ] IO
- [ ] Refinements (see `refinements` folder)
    - [ ] computes a WP that has to be separately proven. it will be nice to not have to compute it, but I think that is a futile exercise. We should look for how to prove it automatically. The good new is that we are not worse than Related Work: CakeML has the same problem. Œuf uses translation validation to verify quotation. Others trust quotation. 
    - [ ] F* has problems computing the WP. It adds an "invisible" guard that is hard to debug: https://github.com/andricicezar/fstar-io/blob/master/rupicola/refinements2/CompilableWP2.fst#L396
- [ ] Avoid quoting ghost code
- [ ] Compiling fixpoints 
    - [ ] @Guido, may work with F* if one defines instances for different arrities. Stuck [FStarLang/FStar#3991](https://github.com/FStarLang/FStar/issues/3991)
    - [ ] Should we use a custom fixpoint combinator? Obvious drawback is that compilation would not be compatible with existing code. 
- [ ] Arrows with pre-post
- [ ] Dijkstra Monads. Note: we cannot compile effects directly because we apply the lambdas we compile in the logical relation.
  - [ ] Identity monad
  - [ ] IO. Maybe easier than state?
  - [ ] State. I suppose we would have to reproduce the proofs from Amal's Thesis, which are very complicated. From what I know, separation logic helps with those proofs. Any way to take advantage of Pulse for that (not ideal since it gives us partial correctness)? Probably it is better to start with IO.
- [ ] Dependent Pairs and Dependent Functions. See attempt on [dpairs2](https://github.com/andricicezar/fstar-io/blob/dpairs2/rupicola/stlc_v2/Compiler.fst#L359) branch.
  - [ ] We have to implement a typing environment, where adding a new type can depend on the types that already exists in the environment. To check if such envs are called Telescopes.
  - [ ] Generally, the typing relation and the expression relation have to be defined mutually recursive, which is a definition rejected by Rocq (probably F* too).
	    Since we want to compile to a language without universe polymorphism, maybe we can define it using concrete universes.
- [ ] We need a way to test completness of the predicate. How? Right now, we write programs by hand.

#### Automation. Defining a type class on top of the predicate
- [ ] Build a TC on top of the predicate for quotation
  - Cezar: this seems a lot harder to do since what is good for a nice relation
    is not necessarly good for type class automation. One example is `hd'`,
    a wrapper on top of `hd`. In practice, it helps type class resolution,
    but it does not work great with the predicate.
- [ ] Type class resolution does not work in HO case (see TODO in [`./experiments/PredicateQuotation.fsti`](./experiments/PredicateQuotation.fsti))

#### Proof of secure compilation
- [ ] Complete proof for STLC
    - [x] Verified back-translation
    - [ ] Define the meta program as described in extended abstract
    - [ ] Admit free
    - [ ] Compiler correctness?
    - [ ] Is it funny that back-translation does not even use the predicate
      	  for quotation?

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
