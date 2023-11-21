# Specialized partial-ordered set for compositional verification of concurrent programs using trace properties

We try to represent terminating stateless programs that can call the operations `print`, `async` and `await`.
The representation has to:
1) have an associative concatenation function;
2) support programs that await on free thread ids;
3) have a clear representation of what events run in parallel and which run sequentially

We're working under the assumptions that the semantic function is providing the ids of the threads.

The informal semantics are:
* `print "x"` - produces events containing the printed string.
    
* `async (fun () -> ...)` - spawns a new thread where it executes the lambda.
     it returns the id of the new thread.

* `await tid` - blocks the current thread and waits for the thread with the id `tid` to end.
    Note: because we look at compositional verification, we have to represent `await tid` without knowing anything about the thread with id `tid`.

In this file, we try to find a data structure by building on top of a partial-order set (poset), where an element is of type `elem` (synonym for `th_id * event`), a pair between a thread id (of type `th_id`) and an event (of type `event`). An event is represented using an option type (`option string`): it can be "empty" (denoted using `ε`) or it can be a string printed by `print`. We need empty events later when we represent the async/await operations to preserve the properties of our data structure.

Note: we do not discuss here how we distinguish between the same events that happen multiple times.

For now, I believe that we only have to deal with posets that have the following properties:
* it has a least element.
* the current thread corresponds to the thread of the least element.
* only the current thread's representation progresses, all the other threads have their complete representation.
* it has a maximal element for each thread that was not awaited.

## Visual representation

#### Synchronous program
```fstar
let main () =
  print "a"; print "a"; print "b"
```
is represented like:
```
(1, "a") ⟶ (1, "a") ⟶ (1, "b")
```

#### Async:
```fstar
let main () =
  let tid = async (fun () -> print "a") in
  ()
```
Visually represented like this:
```
(1,ε)                         <-- current thread
     ↘                    
      (tid,"a")               <-- new thread
```

#### Await
```fstar
let f pr =
  let _ = await pr in
  ()
```
Visually we represent it like this:
```
          (1,ε)     <-- current thread
        ↗ 
(tid,?)             <-- thread with id `th_id`
```
TODO: this visual representation is misleading because no element is created,
  we only have to keep track of this unrealized relation.

#### Program with async
```fstar
let main () =
  print "a";
  let tid = async (fun () -> print "b"; print "c") in
  print "d"
```
is represented like:
```
(1,"a") ⟶ (1,ε) ⟶ (1,"d")    
              ↘                    
                (tid,"b") ⟶ (tid,"c")
```
#### Complete program with async and await
```fstar
let main () =
  print "a";
  let tid = async (fun () -> print "b"; print "c") in
  print "d";
  let _ = await tid in
  print "e"
```
is represented like:
```
(1,"a") ⟶ (1,ε)    ⟶    (1,"d")       ⟶ (1,ε) ⟶ (1,"e")
                 ↘                         ↗ 
                   (tid,"b")  ⟶ (tid,"c")
```
#### Program with a free thread id
```fstar
let f tid =
  print "a";
  let _ = await tid in
  print "b"
```
is represented like:
```
(1,"a") ⟶ (1,ε) ⟶ (1,"b")
          ↗ 
  (tid, ?)
```

## Data Structure

We define our data structure as the tuple `(s, ≼, least, maxs, urel)`, where:
1) `s : set elem` represents the set of elements.
2) `≼ : elem → elem → prop` is the partial order between elements.
3) `least : option elem` is the least element. If `s` is empty, then there is no least element.
4) `maxs : th_id → option elem` is a map from a thread id to the last element produced by it.
5) `urel : list (th_id * elem)` is the list of unrealized relations. These are produced by awaits when a relation cannot be defined because in `s` there is no element of thread `tid`.

We define the following properties of our data structure:
1) `≼` is reflexive, antisymmetric, and transitive on `s`
2) `least` is the least element of poset `(s,≼)`
3) For all thread ids `tid`, if `maxs tid` exists, then `maxs tid` in `s` and `tid = fst (maxs tid)` 
4) For all `m`, if `m` in `s` and there is no `n` in `s` so that `fst m = fst n` and `m ≼ n`, then `maxs (fst m) = m`
5) For all `u`, if `u` in `urel`, then `maxs (fst u)` does not exist and `snd u` is in `s`

NOTE: `least` and `maxs` can be defined as functions over the poset `(s,≼)`.

We define concatenation for our data structure. I think the following assumtions are true when concatenation is used:
* the main threads of the two sets have the same id.
* one cannot find in the second set a thread represented in the first set (and vice versa).

```
(s₀,≼₀,least₀,maxs₀,urel₀) ∙ (s₁,≼₁,least₁,maxs₁,urel₁) = (
  s₀ ∪ s₁,
  (λ x y →
    (x ∈ s₀ ∧ y ∈ s₀ ∧ x ≼₀ y) ∨
    (x ∈ s₁ ∧ y ∈ s₁ ∧ x ≼₁ y) ∨
    (x ∈ s₀ ∧ y ∈ s₁ ∧ x ≼₀ maxs₀ (fst least₀)) ∨
    (x ∈ s₀ ∧ y ∈ s₁ ∧ (∃ u. u ∈ urel₁ ∧ Some? (maxs₀ (fst u)) ∧
                             x ≼₀ maxs₀ (fst u) ∧ (snd u) ≼₁ y))
  ),
  least₀,
  (λ tid → maxs₁ tid ;; maxs₀ tid),
  urel₀ ∪ (filter (λ (tid,_) → !(Some? (maxs₀ tid))) urel₁)
)
```
From property 4, we can prove that all exists `maxs (fst least)` if the set is nonempty.

TODO: how do we represent threads that wait on themselves? how do we represent a child thread waiting on its parent?