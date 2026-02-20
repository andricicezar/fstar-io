### TODO ICFP Submission

The TODOs for the paper, are in the paper.

- [ ] Running example
  - [ ] verify the running example in F*

- [ ] Merge natural numbers and interation to IO
  - [ ] Add compatibility lemmas
  - [ ] Extend compilation
  - [ ] Extend backtranslation (one has to extend the syntactic typing for STLC)
  
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
    - [ ] Problems with unification. See TODO in [`refinements/QExp.fst`](./refinements/QExp.fst).
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

#### Other TODOs
- [ ] Why do we need the helpers functions to define the predicate for quotation? See file [`./experiments/HelpersBug.fst`](./experiments/HelpersBug.fst) for minimized PoC
