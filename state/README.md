## Labeled References

### TODOs
- [X] Refactor effect to have Read/Write/Alloc operations instead of Get/Put @Theo
- [ ] Refactor effect to have an extra index for the flag @Theo
    - [ ] Refactor target contexts to be polymorphic in the flag
- [x] Extend sst_alloc to support monotonic references @Danel
    - [ ] Test sst_write and sst_alloc with monotonic references
- [ ] Extend Shared References to also have label "encapsulated"
- [ ] Higher-order Contracts: Figure out, Implement, prove RrHP 
- [x] Create compiler model for STLC
- [x] Create compiler models also for when context has initial control
- [ ] Make the effect extractable and executable in OCaml @Guido
    - [ ] Skip nodes that write to the top-level interface that keeps track of the shared references
- [ ] Examples for key ideas @Ruxandra
    - [ ] Implement, verify and run artificial example from introduction
    - [ ] Implement, verify and run auto grader
    - [ ] Implement, verify and run guess example
    - [ ] Implement some contexts (good and attackers) in STLC
    - [ ] Instantiate compiler models
- [ ] Find, Implement and run in OCaml a Case Study @Exe
- [ ] Add Linked Lists to STLC and to the BackTranslation
- [ ] Improve stability of proofs in SharedRefs.fsti
- [ ] Add the two lemmas in Sharedefs.fsti to the F*'s library Monotonic.Heap
- [ ] Stretch: Try to do an encoding of shared references in Separation Logic (e.g., Pulse)[Attempt](./experiments/shared_in_pulse/SharedInPulse.fst)
- [ ] Stretch: Prove correctness of DM @Danel (see [Zulip](https://fstar.zulipchat.com/#narrow/channel/214975-fstar-ml-interop/topic/Correctness.20Dijkstra.20Monad))

You can find many examples of how shared references work in [Backtranslation.STLCToTargetLang.fst](./Backtranslation.STLCToTargetLang.fst) (search for Examples).
The examples are written using a total effect, so one has to deal with universe problems.
