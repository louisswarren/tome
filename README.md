# tome
First-order natural deduction in Agda

Agda is a dependently-typed functional programming language, based on an
extension of intuitionistic Martin-Löf type theory. We implement first order
natural deduction in Agda. We use Agda's type checker to verify the correctness
of natural deduction proofs, and also prove properties of natural deduction,
using Agda's proof assistant functionality. This implementation corresponds to
a formalisation of natural deduction in constructive type theory, and the
proofs are verified by Agda to be correct (under the assumption that Agda
itself is correct).

The code is written and documented in literate Agda, is written with the
assumption that the reader is not already familiar with Agda.

[Paper available on ArXiv.](https://arxiv.org/abs/2104.04095v1)
