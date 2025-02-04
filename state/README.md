## Labeled References

### TODOs
- [ ] Refactor effect to have Read/Write/Alloc operations instead of Get/Put
- [ ] Extend sst_alloc to support monotonic references
    - [ ] Test sst_write and sst_alloc with monotonic references
- [ ] Refactor effect to have an extra index for the flag
    - [ ] Refactor target contexts to be polymorphic in the flag
- [ ] Higher-order Contracts: Figure out, Implement, prove RrHP
- [ ] Instantiate compiler model with target contexts written in STLC
- [ ] Write an interpreter
    - [ ] Skip nodes that write to the top-level interface that keeps track of the shared references
- [ ] Examples for key ideas
    - [ ] Implement, verify and run auto grader
    - [ ] Implement, verify and run guess example
- [ ] Find, Implement and run in OCaml a Case Study
- [ ] Stretch: Try to do an encoding of shared references in Separation Logic (e.g., Pulse)[Attempt](./experiments/shared_in_pulse/SharedInPulse.fst)
- [ ] Stretch: Prove correctness of DM (see [Zulip](https://fstar.zulipchat.com/#narrow/channel/214975-fstar-ml-interop/topic/Correctness.20Dijkstra.20Monad))

You can find many examples of how shared references work in [Backtranslation.STLCToTargetLang.fst](./Backtranslation.STLCToTargetLang.fst) (search for Examples).
The examples are written using a total effect, so one has to deal with universe problems.