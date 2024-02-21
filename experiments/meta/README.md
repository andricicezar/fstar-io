TODOs
- [x] Define Deep Embedding of STLC ([`STLC.fst`](./STLC.fst))
    - [x] Var, App, Lam, Unit, Zero, Succ, NRec, Inl, Inr, Case, Fst, Snd, Pair
    - [x] Define Small Step Operational Semantics
- [x] Define Evaluation using Progress and Preservation ([`eval`](./STLC.fst))
    - [x] Prove Progress and Preservation
    - [ ] Prove termination of `eval`. One can build on top of the [proof that normalization halts](https://softwarefoundations.cis.upenn.edu/plf-current/Norm.html) from Software Foundations, which uses a logical predicate.
    - [-] This is already going into the direction of a Big Step Semantics. It is not obvious if in the
          current setting it will help to replace the current `eval`, an interpreter, with big step. Trying to
          predict the future, if/when we will add non-termination, we may need small step to differentiate
          between when the program is stuck and when it loops. For now sticking with small step.
- [x] Define elaboration of STLC expressions into F* ([`elab_exp`](./STLC.fst))
    * In POPL'24, `elab` is effectful, `elab_exp : exp -> MIO (elab_typ _)`
- [x] Define a Cross-Language Logical Relation between F* values and STLC expressions ([`≍`](./CriteriaStatic.STLC.fst))
    - [-] Keep in mind a different way to define the logical relation:
```fstar
val (≍) : rel
let rec (≍) #ty fst_v stlc_ht =
    fst_v R STLC.elab_exp stlc_ht STLC.vempty (** where R = logical relation between F* values **)
```
- [x] Prove that relation `≍` implies compiler correctness of whole programs ([`rel_implies_cc`](./CriteriaStatic.STLC.fst)).
- [x] Prove that relation `≍` implies RHC 
    - [ ] Prove that a STLC expression (representing contexts) is in rel `≍` with its elaboration ([`elab_rel`](./CriteriaStatic.STLC.fst)). 
        - [ ] Prove that the elaboration (`elab_exp`) is invariant to stepping the expression ([`elab_invariant_to_eval`](./STLC.fst)).
- [ ] Prove that compilation returns an STLC expression in rel `≍` with the initial F* value
