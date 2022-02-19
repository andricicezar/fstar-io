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
- Laws
- What are the good expectations of a PDM?
- Make the DM4Free construction in general by applying the transformer to G
- Is it equivalent from having a lift from PURE?