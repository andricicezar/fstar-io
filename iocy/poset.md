# Specialized partial-ordered set to verify trace properties of concurrent programs

We try to represent terminating stateless programs that can call the operations `print`, `async` and `await`.
The representation has to:
1) have a associative concatenation function;
2) support programs that await on free thread ids;
3) have a clear representation of what events run in parallel and which run sequentially

The informal specifications of print, async and await are:
* `print "x"` - produces an event `(1, "x")`, where on the first position is
    the id of the current thread (assumed here to be 1).
    
* `async (fun () -> ...)` - spawns a new thread where it executes the lambda.
     it returns the id of the new thread.

* `await tid` - waits for the thread with the id `tid` to end, but because the operation
    is ran on an current thread, it does not know anything about the thread with id `tid`.

In this file, we try to do that using a partial-order set,
where the elements of the set are either events or empty `ε`. Empty elements are necessary to preserve the properties of our posets when representing the async and await operations.

We define our posets as the triple `(s, ≼, urel)`, where:
1) `s : set (option a)` represents the set of elements where events are of type `a`.
2) `≼ : a → a → prop` is the partial order between elements
3) `urel : set (tid:int * (option a))` is the set of unrealized relations. These are produced by awaits when a relation cannot be defined because in `s` there is no element of thread `tid`.

Our partial-order sets have the following properties:
* it has a least element.
* it has a maximal element for each thread that was not awaited.


We define concatenation between two posets, under the assumptions that the first one is not empty and that the sets are distinct, as:
```
(s₀,≼₀,urel₀) ∙ (s₁,≼₁,urel₁) = (
  s₀ ∪ s₁,
  (λ x y →
    (x ∈ s₀ ∧ y ∈ s₀ ∧ x ≼₀ y) ∨
    (x ∈ s₁ ∧ y ∈ s₁ ∧ x ≼₁ y) ∨
    (x ∈ s₀ ∧ y ∈ s₁ ∧ (∃ top. top ∈ s₀ ∧
                                max (s₀,≼₀) (th_id (least (s₀,≼₀))) = Some top ∧
                                x ≼₀ top)) ∨
    (x ∈ s₀ ∧ y ∈ s₁ ∧ (∃ top z. top ∈ s₀ ∧ z ∈ s₁ ∧
                                  (th_id top, z) ∈ urel₁ ∧
                                  max (s₀,≼₀) (th_id top) = Some top ∧
                                  x ≼₀ top ∧
                                  z ≼₁ y))

  ),
  urel₀ ∪ (urel₁ - { (tid,_) ∈ urel₁ | ∃ x. x ∈ s₀ ∧ th_id x = tid })
)
```
where `max (s,≼) tid` is a partial function that returns the maximal element corresponding to the thread `tid`, and `least (s,≼)` is a function that returns the least element of the poset.

## Visual representation

We explain how it works by representing things visually:

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
  let _ = async (fun () -> print "a") in
  ()
```
Visually we represent it like this:
```
ε ⟶ ε                <-- current thread
  ↘                    
   (2,"a")            <-- new thread
```

#### Await
```fstar
let f pr =
  let _ = await pr in
  ()
```
Visually we represent it like this:
```
             ε         <-- current thread
           ↗ 
(th_id, ?)             <-- thread with id `th_id`
```
TODO: this visual representation is misleading because no node is created.

#### Program with async
```fstar
let main () =
  print "a";
  let _ = async (fun () -> print "b"; print "c") in
  print "d"
```
is represented like:
```
(1, "a") ⟶ ε ⟶ ε ⟶ (1, "d")    
              ↘                    
               (2, "b") ⟶ (2, "c")
```
#### Complete program with async and await
```fstar
let main () =
  print "a";
  let th_id = async (fun () -> print "b"; print "c") in
  print "d";
  let _ = await th_id in
  print "e"
```
is represented like:
```
(1, "a") ⟶ ε ⟶  ε ⟶ (1, "d") ⟶  ε  ⟶ (1, "e")
             ↘                     ↗ 
              (2, "b") ⟶ (2, "c")
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
(1, "a") ⟶ ε ⟶ (1, "b")
           ↗ 
   (tid, ?)
```