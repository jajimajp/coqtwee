# CoqTwee

CoqTwee is an equational theorem proving plugin for Coq.
This plugin utilizez [twee](https://nick8325.github.io/twee/), an equational theorem prover.

## Example

```coq
From CoqTwee Require Import Twee.

Parameter G : Set.
Parameter O : G.
Parameter i : G -> G.
Parameter f : G -> G -> G.

Axiom plus_zero : forall X, f O X = X.
Axiom minus_left : forall X, f (i X) X = O.
Axiom associativity : forall X Y Z, f X (f Y Z) = f (f X Y) Z.

Goal forall a b, f a b = a -> b = O.
Proof.
  intros a b h.
  twee plus_zero minus_left associativity h.
Qed.
```

See [./e2e_test](./e2e_test) for more examples.

## Requirement

- twee 2.4.2
- Coq 8.20.0

## Setup

```bash
make && make install
```

## Development

To run unit tests:

```bash
dune runtest
```

To run e2e tests:

```bash
dune build e2e_tests
```
