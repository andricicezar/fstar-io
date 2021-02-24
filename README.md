This code should work with the F\* commit: e0ba9134812b74dc112be287c108ccff8f1ab064

## Ideas
1. trigger events when there is a switch between context and the partial program
   -- everytime the partial program gives control to the context will trigger an
      event called EnterContext and when it gets back the control will trigger
      ExitContext
   -- everytime the context calls in the interface of partial program, the
      EnterPartialProgram trigger will be called and when exiting
      ExitPartialProgram.
   -- take care of higher order programs

   Motivation: this feature allows more rich specification. the pi will be
   more powerful because it will be able to discriminate between actions that
   happen in the context and the ones from the partial program.
2. Change type of pi from Tot to St, such that it has its own memory.
   Motivation: The motivation would be to have more rich specification, but
   this may be obtained from other ideas in this file. The "memory" of pi is
   the trace, therefore replacing the trace with another data structure should
   be sufficient.
2. Mixing events using the demo Catalin & Guido did. Motivation: it may give
   composability.
3. Extending the IO effect with non termination. Motivation: This is needed
   because our proof of "RSP" uses reification and in F\*, reifying a non
   terminating effect will return in Dv, which makes proofs harder. (???)
4. Extending the IO effect with state. Motivation: state is necessary to
   have a realistic use case.

# Related to the efficiency of trace
Eric comments:
```
Regarding efficiency and keeping the trace at RT: this issue was quite well
studied in the AOP community back then. One basic idea was to partially evaluate
"pointcuts" (which are the predicates on runtime events) in order to determine
the "shadows" that you actually need to keep track of. There's even work on
trace-based aspects, and how to make them efficient (Eric Bodden was
particularly brilliant at coming up with techniques for that)

The problem of trace recording and querying is even more general - a student of
mine did super cool work in the context of an omniscient debugger
-- see OOPSLA'07 followed by ECOOP'11. The key idea of ECOOP'11 is to have an
efficient representation that combines the benefits of both snapshot-replay and
trace-recording (the two main approaches to back-in-time debugging)

btw, Arthur Chargueraud mentioned this paper in his ML workshop talk:
https://cakeml.org/itp19.pdf might be relevant
```
3. Replacing the trace with an automata
4. extracting the monitor from LTL formulas
5. can ghost trace be mixed with materialized trace?
