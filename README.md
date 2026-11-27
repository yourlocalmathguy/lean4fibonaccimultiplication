# Fibonacci Multiplication in Lean 4

A formalization of Knuth's Fibonacci multiplication on the natural numbers in Lean 4. The project develops an associativity proof using shifted Fibonacci sums, the conjugate of the golden ratio, and a threefold finite-sum expansion.

## 1. Mathematical definition

Let $F_0=0$, $F_1=1$, and let $I(n)$ denote the set of indices appearing in the Zeckendorf representation of a natural number $n$. Define Fibonacci multiplication by

$$
a \circ b = \sum_{i \in I(a)} \sum_{j \in I(b)} F_{i+j}.
$$

The operation is implemented in Lean using the Zeckendorf representations provided by Mathlib.

The main theorem formalized in this repository is associativity:

```lean
FibonacciMultiplication.fibMul_assoc
```

That is,

**$$(a \circ b) \circ c$$**

$$a \circ (b \circ c)$$


## 2. Formalized results

The main public declarations are:

| Declaration | Result |
|---|---|
| `fibMul` | Definition of Fibonacci multiplication |
| `fibMul_zero` | $a \circ 0 = 0$ |
| `zero_fibMul` | $0 \circ b = 0$ |
| `fibMul_comm` | Commutativity |
| `fibMul_assoc` | Associativity |

The implementation also contains private helper lemmas and definitions used to establish associativity. These include the shifted-sum identity, the conjugate-error bound, the shift-invariance argument, and the threefold expansion. They are internal components of the proof rather than public declarations.

## 3. Proof architecture

The associativity proof is organized around the following steps:

1. **Shifted Fibonacci sums:** Define a function that shifts every Fibonacci index in a Zeckendorf representation.
2. **Conjugate-error identity:** Relate shifted Fibonacci sums to the golden ratio and its algebraic conjugate.
3. **Error bound:** Establish a uniform bound on the conjugate error using the separation of indices in Zeckendorf representations.
4. **Shift-one identity:** Compare two natural numbers whose difference has absolute value strictly less than one, forcing them to be equal.
5. **Shift recurrence:** Use the Fibonacci recurrence to extend the identity to every nonnegative shift.
6. **Threefold expansion:** Express the iterated product as a symmetric finite sum over three Zeckendorf representations.
7. **Associativity:** Reorder the finite sums and use the expansion to establish associativity.

The golden-ratio conjugate approach is not claimed as a new mathematical discovery. Arnoux used a related conjugate-number argument in his 1989 discussion of Fibonacci multiplication. The contribution of this project is the Lean 4 formalization and its organization of the proof.

## 4. Repository structure

```text
lean4fibonaccimultiplication/
├── formalization.lean
├── lakefile.toml
├── lean-toolchain
├── lake-manifest.json
├── README.md
├── LICENSE
└── .gitignore
```

- `formalization.lean`: Complete Lean formalization.
- `lakefile.toml`: Lake project configuration and Mathlib dependency.
- `lean-toolchain`: Specifies the Lean version.
- `lake-manifest.json`: Locks the resolved dependency revisions.
- `LICENSE`: Project license.
- `.gitignore`: Excludes generated build artifacts and editor files.

## 5. Lean and Mathlib versions

The project currently uses:

- **Lean:** `leanprover/lean4:v4.37.0-rc1`
- **Mathlib requirement:** `v4.37.0-rc1`

The committed `lake-manifest.json` records the exact resolved Git revisions of Mathlib and its transitive dependencies. In particular, the resolved Mathlib revision is:

```text
31ce06eaadf4a200c0e1407c5f10953cf606b8f8
```

Keep `lake-manifest.json` committed so that other users can reproduce the dependency environment.

## 6. Building the project

Install Lean 4 and Lake using `elan`, then open a terminal in the repository root.

First, download available precompiled Mathlib artifacts:

```bash
lake exe cache get
```

Then build the project:

```bash
lake build formalization
```

The committed dependency manifest should be used for ordinary builds. Running `lake update` is not necessary for routine setup and may change resolved dependencies.

To compile the main source file directly, run:

```bash
lake env lean formalization.lean
```

A successful compilation should finish without Lean errors.

The initial dependency setup can be resource-intensive if precompiled artifacts are unavailable. The cache command is intended to avoid compiling the entire Mathlib dependency tree from source.

## 7. Axiom verification

The associativity theorem was inspected using:

```lean
#print axioms FibonacciMultiplication.fibMul_assoc
```

The reported dependencies in the development environment were:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, `sorryAx` was not present in the reported dependency list.

These are standard Lean foundational axioms. The result should not be described as having no axiomatic dependencies.

The source file includes commands to print the Lean version and the associativity theorem's axiom dependencies.

## 8. Mathematical references

1. E. Zeckendorf, “Représentation des nombres naturels par une somme de nombres de Fibonacci ou de nombres de Lucas,” *Bulletin de la Société Royale des Sciences de Liège* 41 (1972), 179–182.

2. D. E. Knuth, “Fibonacci multiplication,” *Applied Mathematics Letters* 1 (1988), no. 1, 57–60.  
   https://doi.org/10.1016/0893-9659(88)90176-0

3. P. Arnoux, “Some remarks about Fibonacci multiplication,” *Applied Mathematics Letters* 2 (1989), no. 4, 319–320.  
   https://doi.org/10.1016/0893-9659(89)90078-5

4. L. de Moura and S. Ullrich, “The Lean 4 theorem prover and programming language,” in *Automated Deduction – CADE 28*, 2021, 625–635.  
   https://doi.org/10.1007/978-3-030-79876-5_37

5. The mathlib Community, “The Lean mathematical library,” *CPP 2020*, 2020, 367–381.  
   https://doi.org/10.1145/3372885.3373824

6. J.-F. Burnol, *The zeckendorf package*, CTAN, 2025.  
   https://ctan.org/pkg/zeckendorf

## 9. License

This project is distributed under the MIT License. See [LICENSE](LICENSE).
