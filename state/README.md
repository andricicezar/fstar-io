# Directions

### Labeled References

We have three different implementations of Labeled References:
1. Extending Monotonic State by extending the definition of the heap. (current folder, [The definition of the heap](./Labeled.Monotonic.Heap.fsti), and [the effect](./Labeled.MST.fst))
2. [Encoding in MST](./experiments/LabelsInST.fst) (missing invariants for now, no technical reason)
3. [Attempt at encoding in Pulse](./experiments/shared_in_pulse/SharedInPulse.fst)

You can find many examples of how shared references work in [TargetLang.fst](./TargetLang.fst) (search for Examples).
The examples are written using a total effect, so one has to deal with universe problems.

### Secure Compilation Diagram

The specification of unverified contexts can be found in [`mk_tgt_arrow` in TargetLang.fst](./TargetLang.fst).

The compilations steps:
1. Higher-order contracts, we did not start yet.
2. Reify/Reflect. [There is a PoC here](./experiments/mst_reifyreflect/MSTReifyReflect.fst).
3. DM <-> Free. [There is an attempt here](./experiments/mst_handleaway/FreeParam.fst)

Back-translations:
1. Translation from [STLC to Free](./Translation2.fst).
2. Translation from [STLC to MST](./Translation.fst).

### Assumptions

- [ ] Inverison Lemma in [TargetLang.fst](./TargetLang.fst).
- [ ] Strict Positivity in translation from STLC to Free ([here](./Translation2.fst)). 
- [ ] The behavior of the computation remains unchanged after applying reflect and reify. ([Lemma `lemma_reify_reflect`](./experiments/mst_reifyreflect/MSTReifyReflect.fst))


