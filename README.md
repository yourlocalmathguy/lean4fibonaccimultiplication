# Formalizing Fibonacci Multiplication in Lean 4

## Overview

This project contains a Lean 4 formalization of Fibonacci multiplication, an operation on nonnegative integers defined using their Zeckendorf representations.

The project formalizes the associativity theorem:

\[
(a \circ b) \circ c = a \circ (b \circ c).
\]

## Mathematical Background

Every nonnegative integer has a unique Zeckendorf representation as a sum of non-consecutive Fibonacci numbers.

For integers \(a,b \geq 0\), define

\[
a \circ b =
\sum_{i \in I(a)}\sum_{j \in I(b)}F_{i+j},
\]

where \(I(n)\) is the set of Fibonacci indices in the Zeckendorf representation of \(n\).

## Main Results

- Definition of Fibonacci multiplication.
- Zero and commutativity properties.
- A shifted Fibonacci sum identity.
- A conjugate-golden-ratio error bound.
- A threefold expansion theorem.
- Associativity of Fibonacci multiplication.

## Proof Strategy

The formal proof uses a conjugate-golden-ratio error term to establish a key shift identity. The identity is extended to all shifts using the Fibonacci recurrence. Associativity then follows from the symmetry of a threefold finite sum.

This proof organization is related to the non-combinatorial approach of Arnoux (1989); it is not claimed as a new proof of the underlying mathematical theorem.

## Implementation

- **Proof assistant:** Lean 4
- **Mathematical library:** Mathlib

Exact Lean and Mathlib versions will be documented with the verified release.

## Repository Structure

- `Main.lean` — Main formalization.
- `README.md` — Project documentation.
- `LICENSE` — Software license.

## References

1. D. E. Knuth, "Fibonacci multiplication," Applied Mathematics Letters, 1988.
2. P. Arnoux, "Some remarks about Fibonacci multiplication," Applied Mathematics Letters, 1989.
3. The mathlib Community, "The Lean Mathematical Library," CPP 2020.

## Verification

The formalization should be compiled using the Lean and Mathlib versions specified by the project configuration.
