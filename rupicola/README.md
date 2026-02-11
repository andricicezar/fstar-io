### TODO ICFP Submission

The TODOs for the paper, are in the paper.

- [ ] Compatibility lemmas (@Abigal)
  - [ ] Make the proofs stable
  - [ ] LogRelSourceTarget.CompatibilityLemmas.fst
    - [x] Admit free `equiv_oval_app`
    - [x] Admit free `equiv_oprod_app_oval_oval`
    - [ ] Admit free `equiv_oprod_app`
    - [x] Admit free `equiv_oval_lambda`
    - [x] Admit free `equiv_oval_lambda_oprod`
    - [x] Admit free `equiv_oprod_lambda`
  - [ ] LogRelTargetSource.CompatibilityLemmas.fst
    - [x] Admit free `equiv_oval_app`
    - [x] Admit free `equiv_oprod_app_oval_oval`
    - [ ] Admit free `equiv_oprod_app` (+ @Danel)
    - [x] Admit free `equiv_oval_lambda`
    - [x] Admit free `equiv_oval_lambda_oprod`
    - [x] Admit free `equiv_oprod_lambda`
  - [ ] Do we agree that proving these lemmas is enough to be confident that we can prove the other compatibility lemmas?

- [ ] Running example (@Theo)
  - [ ] @everyone, give feedback on the running example in the paper
  - [ ] implement the running example in F*
    - [ ] quotation
    - [ ] instantiate the compiler (preferably, not the night before the deadline :D)
  - [ ] @everyone, debate on how to instantiate the running example: what is a task? what is validate? what would be some attacks?

- [ ] Merge Exe's strings, natural numbers and interation to IO
  - [ ] Add compatibility lemmas
  - [ ] Extend compilation
  - [ ] Extend backtranslation (one has to extend the syntactic typing for STLC)
  
- [ ] Backend to λ□  (@Exe)
  - [ ] extract the running example to Malfunction and run it

- [ ] Metaprogram (@Cezar)
  - [ ] working on simply typed F* examples
  - [ ] working on IO examples
  - [ ] working on the running example

- [ ] Admits (81)
  - [ ] Trace.fst
    - [ ] 6 admits about traces and append
  - [ ] Hist.fst
    - [ ] 2 admits about monotonicity
  - [ ] IO.fsti
    - [ ] one assume that was fixed on Abigail's branch
  - [ ] IO.fst
    - [ ] theta is a monad morphism
    - [ ] `io_bind_equivalence`
  - [ ] QTyp.fst 
    - [ ] `lem_substitution`
    ```fstar
    let lem_substitution #g #b (s:gsub g b) (t:qType) (v:value) (e:exp)
  : Lemma (
    (subst (sub_beta v) (subst (sub_elam s) e)) == (subst (gsub_extend s t v) e))
    ```
    - [ ] `lem_gsubst_closed_identity`
    ```fstar
    let lem_gsubst_closed_identiy #g #b (s:gsub g b) (e:closed_exp) :
      Lemma (gsubst s e == e)
    ```
    - [ ] 14 admitted lemmas about fv_in_env
  - [ ] STLC.fst
    - [ ] assume in `subst_beta`
    - [ ] `lem_destruct_steps_epair_fst`
    - [ ] `lem_destruct_steps_epair_snd`
    - [ ] one case in `lem_shifting_preserves_closed`
    - [ ] admits and assumes in `lem_subst_freevars_closes_exp`
  - [ ] LogRelSourceTarget.fst
    - [ ] `lem_values_valid_superset_val_valid_contains`
    - [ ] `lem_values_are_expressions`
    - [ ] `lem_values_are_producers`
  - [ ] LogRelTargetSource.fst
    - [ ] `lem_values_valid_subset_val_valid_member_of`
    - [ ] `lem_values_are_expressions`
    - [ ] `lem_values_are_producers`
  - [ ] LogRelSourceTarget.CompatibilityLemmas.fst
    - [ ] `equiv_oprod_app` has to be redone
    - [ ] 10 admitted compatibility lemmas on Abigail's branch
  - [ ] LogRelTargetSource.CompatibilityLemmas.fst
    - [ ] 26 admitted compatibility lemmas
  - [ ] Compilation.fst
    - [ ] `lem_compile_closed_arrow_is_elam`
    ```fstar
    let lem_compile_closed_arrow_is_elam (#a #b:qType) (#s:fs_val (a ^->!@ b)) (qs:(a ^->!@ b)   s) : Lemma (ELam? (compile qs))
  ```
    - [ ] Two big assumes in `lem_compile_closed_valid`
  - [ ] Backtranslation.fst
    - [ ] backtranslation of values missing
    - [ ] verify backtranslation of values
  - [ ] RrHP.fst
    - [ ] one assume in the main theorem


- [ ] Prepare artifact
  - [ ] Use the names from the paper in the artifact (e.g., rename STLC to something better)
  - [ ] Cleanup comments
  - [ ] Prepare README
    - [ ] Prepare message on why things are admitted :D



### Old todos

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