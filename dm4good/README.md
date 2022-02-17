# Partial Dijkstra monads

Should work fine with Coq 8.14.

## TODO

- Refactor to define a notion of monad and `ReqMonad` and `DijkstraMonad` on
top of it.
- Show that `pure_wp` also has a lift from pure for ND.
- Next step is the guarded construction and then use it for stuff like ND and
maybe IO?