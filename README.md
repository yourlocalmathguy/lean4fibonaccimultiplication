# Fibonacci Multiplication in Lean 4

A Lean 4 formalization of Knuth's Fibonacci multiplication on the natural numbers. The development proves associativity using shifted Fibonacci sums, an estimate involving the algebraic conjugate of the golden ratio, and a symmetric threefold finite-sum expansion.

## 1. Mathematical definition

Let the Fibonacci sequence be defined by

$$
F_0=0, \qquad F_1=1, \qquad F_{n+2}=F_{n+1}+F_n.
$$

For each natural number $n$, let $I(n)$ be the finite set of indices in its Zeckendorf representation. Thus

$$
n=\sum_{i\in I(n)}F_i,
$$

where all indices are at least $2$ and distinct indices differ by at least two. The representation of zero is empty, so $I(0)=\varnothing$.

Following Knuth [2], define Fibonacci multiplication by

$$
a \circ b = \sum_{i\in I(a)}\sum_{j\in I(b)}F_{i+j}.
$$

The operation is implemented in Lean using the Zeckendorf representations provided by Mathlib. The main theorem formalized in this repository is

```lean
FibonacciMultiplication.fibMul_assoc
```

which states that

$$
(a \circ b) \circ c = a \circ (b \circ c)
$$

for all natural numbers $a,b,c$.

## 2. Formalized results

The main public declarations are:

| Declaration | Result |
|---|---|
| `fibMul` | Definition of Fibonacci multiplication |
| `fibMul_zero` | $a \circ 0 = 0$ |
| `zero_fibMul` | $0 \circ b = 0$ |
| `fibMul_comm` | Commutativity |
| `fibMul_assoc` | Associativity |

The implementation also contains private helper definitions and lemmas used in the associativity proof. These include the shifted-sum function, the conjugate-error function and its bound, the shift-one identity, the general shift identity, and the threefold expansion. The private declarations are internal components of the proof rather than part of the module's public interface.

## 3. Proof architecture

The proof is organized around the shifted Fibonacci sums

$$
S_k(n)=\sum_{i\in I(n)}F_{i+k}.
$$

The key steps are:

1. **Conjugate-error identity:** Define $E(n)=\sum_{i\in I(n)}\psi^i$, where $\psi=(1-\sqrt{5})/2=-\varphi^{-1}$, and prove $S_1(n)-\varphi n=E(n)$.
2. **Uniform error bound:** Use the separation of Zeckendorf indices to show $|E(n)|<q$, where $q=\varphi^{-1}$ and $q+q^2=1$.
3. **Shift-one identity:** For the partial-product sum $P_k(a,b)=\sum_{j\in I(b)}S_{k+j}(a)$, use the error bound to show that $S_1(a\circ b)$ and $P_1(a,b)$ differ by less than one. Since both are natural numbers, they must be equal.
4. **General shift identity:** Use the Fibonacci recurrence and agreement at shifts zero and one to establish the identity for every nonnegative shift.
5. **Threefold expansion:** Express the iterated product as a finite sum of $F_{i+j+k}$ over the three Zeckendorf representations.
6. **Associativity:** Reorder the finite sums in the threefold expansion and use commutativity to obtain associativity.

The conjugate-number method is not claimed as a new mathematical discovery. Arnoux [3] used the golden-ratio conjugate in a real-algebraic treatment of Fibonacci multiplication. In the notation here, if $\alpha=\psi=1-\varphi$ and $p_n=S_1(n)-n$, then

$$
E(n)=p_n+n\alpha.
$$

The shift-one identity is equivalent to the multiplicative-closure relation $E(a\circ b)=E(a)E(b)$. The contribution of this project is the Lean 4 formalization and its organization through shifted sums, an error estimate, integer separation, and the Fibonacci recurrence.

The threefold-sum identity used to conclude associativity is also present in Knuth's original proof [2, equation (12)]. Knuth obtains it through radix-$F$ normalization; this formalization derives it from the general shift identity. The project does not claim the underlying associativity theorem, the conjugate-number estimate, or the threefold expansion as new mathematical results.

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
- `lake-manifest.json`: Records the resolved dependency revisions.
- `README.md`: Project description and build instructions.
- `LICENSE`: Project license.
- `.gitignore`: Excludes generated build artifacts and editor files.

## 5. Lean and Mathlib versions

The project is configured to use:

- **Lean:** `leanprover/lean4:v4.37.0-rc1`
- **Mathlib requirement:** `v4.37.0-rc1`

The committed `lake-manifest.json` records the exact resolved Git revisions of Mathlib and its transitive dependencies. The resolved Mathlib revision is:

```text
31ce06eaadf4a200c0e1407c5f10953cf606b8f8
```

Keep `lake-manifest.json` committed so that other users can reproduce the dependency environment. The manifest, rather than the version tag in `lakefile.toml` alone, records the exact resolved revision used for the project.

## 6. Building the project

Install Lean 4 and Lake using `elan`, then open a terminal in the repository root.

First, download available precompiled Mathlib artifacts:

```bash
lake exe cache get
```

Then build the formalization target:

```bash
lake build formalization
```

To compile the main source file directly in the Lake environment, run:

```bash
lake env lean formalization.lean
```

The committed dependency manifest should be used for ordinary builds. Running `lake update` is not necessary for routine setup; use it only when intentionally updating dependency resolutions, then review and commit the resulting manifest.

The cache command is intended to avoid compiling the entire Mathlib dependency tree from source. Initial dependency setup may still require substantial disk space, network transfer, and memory.

The project has been built successfully with the committed configuration; the maintainer's build of `lake build formalization` returned exit status `0`.

## 7. Axiom verification

The associativity theorem can be inspected with:

```lean
#print axioms FibonacciMultiplication.fibMul_assoc
```

The reported dependencies in the development environment were:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, `sorryAx` was not present in the reported dependency list. These are standard Lean foundational axioms; the theorem should not be described as having no axiomatic dependencies. The result records the output obtained in the stated development environment and should be checked again if the toolchain or dependency revisions change.

The source file also includes commands for inspecting the Lean version and the axiom dependencies of the associativity theorem.

## 8. Mathematical references

1. E. Zeckendorf, “Représentation des nombres naturels par une somme de nombres de Fibonacci ou de nombres de Lucas,” *Bulletin de la Société Royale des Sciences de Liège* 41 (1972), 179–182.

2. D. E. Knuth, “Fibonacci multiplication,” *Applied Mathematics Letters* 1 (1988), no. 1, 57–60.  
   https://doi.org/10.1016/0893-9659(88)90176-0

3. P. Arnoux, “Some remarks about Fibonacci multiplication,” *Applied Mathematics Letters* 2 (1989), no. 4, 319–320.  
   https://doi.org/10.1016/0893-9659(89)90078-5

4. L. de Moura and S. Ullrich, “The Lean 4 theorem prover and programming language,” in *Automated Deduction – CADE 28*, 2021, 625–635.  
   https://doi.org/10.1007/978-3-030-79876-5_37

5. The mathlib Community, “The Lean mathematical library,” *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, 2020, 367–381.  
   https://doi.org/10.1145/3372885.3373824

6. J.-F. Burnol, *The zeckendorf package*, CTAN, 2025.  
   https://ctan.org/pkg/zeckendorf

## 9. License

This project is distributed under the MIT License. See [LICENSE](LICENSE).
