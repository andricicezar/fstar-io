# Partial Dijkstra monads

Should work fine with Coq 8.14.

## Examples of partiality in F*

These should type-check from the existence of a lift from PURE.
They explain the need for deep asserts in the effect representation.

State:
```fstar
let s₀ = get () in
let s₁ = get () in
assert (s₀ = s₁)
```

ND:
```fstar
let x = choose l in
assert (x `memP` l)
```

## TODO

- Next step is the guarded construction and then use it for stuff like ND and
maybe IO?

- What are the good expectations of a PDM?

- Make the DM4Free construction in general by applying the transformer to G

- Is it equivalent from having a lift from PURE?

- Since we can combine free monads easily, can we provide a way to define free
monadic effect like:

```fstar
effect ND a (w : (a -> prop) -> prop)
  choose : (l : list a) -> ND a (fun post -> forall x. x `memP` l ==> post x)
```

```fstar
effect PURE a (w : (a -> prop) -> prop)
  assert : (p : prop) -> PURE p (fun post -> p /\ post ())
```

```fstar
effect STATE a (w : (state -> a -> prop) -> (state -> prop))
  get : unit -> STATE state (fun post s -> post s s)
  put : (s : state) -> STATE unit (fun post s0 -> post s ())
```

and then allow for arbitrary combination of those?

- Factories for WPs of the form post → pre + monotonicity?

- Maybe we can do as Catalin suggests for GuardedPDM using θ and maybe liftᵂ?

## Random notes

- We can do DM for free constructions, but we have more flexibility with respect
to the effect observation and specification monad.
- Computation monad could be called syntax monad.