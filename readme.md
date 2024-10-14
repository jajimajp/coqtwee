# CoqTwee

CoqTwee is an equational theorem proving plugin for Coq.
This plugin utilizez [twee](https://nick8325.github.io/twee/), an equational theorem prover.

## Example

```coq
From CoqTwee Require Import Loader.

Parameter G : Set.
Parameter O : G.
Parameter i : G -> G.
Parameter f : G -> G -> G.

Axiom plus_zero : forall X, f O X = X.
Axiom minus_left : forall X, f (i X) X = O.
Axiom associativity : forall X Y Z, f X (f Y Z) = f (f X Y) Z.

Goal forall a b, f a b = a -> b = O.
Proof.
  intros.
  twee plus_zero minus_left associativity H.
Qed.
```

## Requirement

- twee 2.4.2
- Coq 8.20.0

## Setup

```bash
make && make install
```

## Usage

```bash
coqtop

Coq < From CoqTwee Require Import Loader.
[Loading ML file coqtwee.plugin ... done]

Coq < HelloWorld.
Hello, world!
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
