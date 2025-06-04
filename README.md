# bfcoq

A formally verified Brainfuck compiler in Coq using Hoare logic.

## Stages

- [`Token`](./theories/Token.v): Flat lexical tokens
- [`AST`](./theories/AST.v): Inductive loops
- [`ComIR`](./theories/ComIR.v): Combined sequences of `>`, `<`, `+`, and `-`
- [`RelIR`](./theories/RelIR.v): Relative-positioned cell offsets

## Installation

bfcoq requires CompCert for its `byte` type. [Using opam](https://coq.inria.fr/opam-using.html),
make sure that Coq is installed, then install the CompCert package from the Coq
opam repository:

```sh
opam install coq
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-compcert
```
