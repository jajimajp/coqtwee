# CoqTwee

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
