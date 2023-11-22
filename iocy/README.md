# Looking for a DM to verify concurrent programs using trace properties

There are three interesting experiments in this folder. All of them are based on a Free monad with the operations `async` and `await`.

The first one is in file [`pure_async_await.fst`](pure_async_await.fst), where we used to define a Dijkstra Monad indexed by pure weakest-preconditions (no trace properties in this file). The file verifies well, without troubles from the SMT. However, I am unsure what exciting examples we can do using this DM.

The second one is file [`runtree_async_await.fst`](runtree_async_await.fst), where we added the operations `print X` producing the event `X`. Here, we defined a specification monad on top of a data structure, we call, [Runtree](runtree.fst). A Runtree is a representation of a concurrent program as a tree, where the synchronous events are concatenated, and each async produces a branching. However, we cannot interpret the `await` operation, thus, we rely on special events for awaits. I think this data structure is clean, and one can look for other solutions starting from it.

The third file, [`poset.fst`](poset.fst), contains only a data structure based on posets. While from the manual testing, the data structure seems fit to represent concurrent programs, the SMT performance is bad. For this file, I also wrote a detailed description of how it works in [`poset.md`](poset.md).
