Verifying non-terminating programs with IO in F*
================================================

## Prerequisites

The code in this repo has been tested on the following F* version:
```
F* 2021.11.05~dev
commit=d20e32ca8ef7ab2e4cc79e0f553687ee2ae4a2ed
```

## Terminating effect

The effect that only supports termination is found in the `io` subdirectory.

The computational monad can be found in `Free`, the specification monad can 
be found in `Hist`, and the Dijkstra Monad can be found in `DMFree`.
The signature for the IO effect can be found in `IO.Sig`, and the definition
of the IO effect (which is just an instantiation of `DMFree`) is in `IO`.


## Non-terminating effect

The effect that supports non-termination is found in the `iodiv` subdirectory.

`Util` contains common lemmas. `Stream` proposes an encoding of streams using
functions from natural numbers.

`DivFree` contains the definition of the free monad extended with an iter
operator.
`DivFreeTauSpec` contains the definition of the specification of IO +
non-termination.
`IIOSig` gives a signature for IO and `IIOSpec` gives the associated
specifications.
`DivFreeTauDM` builds a partial Dijkstra monad on top of `DivFree`.

The effect is defined in `TauIODiv` and tested in `TestIODiv`.

The extra I that is sometimes before IO stands for "instrumented".
Instrumentation is something we use for secure F*-ML interoperability.
