This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Dyck path algebra, `Θ`, and the `Ψ` bijection in Lean

This Lean 4 project formalizes two related parts of the mathematics developed in
[`main.tex`](main.tex):

1. a generators-and-relations model of the Dyck path algebra `𝒜_{q,t}`, its
   abstract operator representations, the `Θ` transformation, descent through a
   quotient, and preservation of the kernel relations of the symmetric-function
   action; and
2. the unlabelled decorated-Dyck-path bijection `Ψ` used in the `q = 1` part of
   the Theta conjecture, including area and rise-composition preservation.

The project deliberately separates these developments:

```text
RequestProject/
├── Main.lean                 algebraic entry point and headline examples
├── Aqt/                      algebra, representations, and Θ
│   ├── Algebra.lean
│   ├── Rep.lean
│   ├── Theta.lean
│   ├── ThetaDescent.lean
│   ├── PreserveKernel.lean
│   └── DGamma.lean
├── Psi.lean                  umbrella import for the complete Ψ development
└── Psi/                      definitions and proofs for the bijection
    ├── Defs.lean
    ├── PathLemmas.lean
    ├── PhiBasic.lean
    ├── Area.lean
    ├── RiseComp.lean
    ├── Forward.lean
    ├── Inverse.lean
    └── Bijection.lean
```

## Scope and modeling choices

The algebraic part uses a level-graded path-algebra presentation with vertex
idempotents, level-indexed arrows and loops, all relations `(R1)`–`(R6)` and
their starred counterparts.  The elements `y_i` and `z_i` are derived words,
not generators.  The concrete action on symmetric functions remains represented
abstractly by an algebra homomorphism rather than by a plethystic datatype;
inverses belonging to the `u`-adic completion are supplied as two-sided inverse
data.

Within that scope, the formalization constructs the full quotient algebra,
packages its actions, proves the transformed-operator identities, and gives the
universal descended homomorphism directly from that quotient.  It also proves the abstract conjugation identity
`Θ(L) = U L U⁻¹` from intertwining and the corresponding commutation and
conjugation theorems for the natural-composition operators `D_γ`.

The combinatorial part is independent of the algebraic one.  Paths are Boolean
lists (`true` = North, `false` = East).  The Lean target stores an area vector
rather than the paper's absolute height vector; the latter is recovered by
adding the descent staircase.  The development proves that `Φ` and `Ψ` are
inverse on the appropriate domains and that the bijection preserves area and
rise composition.

## Documentation

Detailed guides are in [`docs/`](docs/):

- [`AQT_FILES.md`](docs/AQT_FILES.md) — the algebraic modules;
- [`PSI_FILES.md`](docs/PSI_FILES.md) — the split combinatorial modules;
- [`PSI_BIJECTION.md`](docs/PSI_BIJECTION.md) — a mathematical guide to the
  bijection, encodings, and principal theorems;
- [`SOURCE_AND_SCOPE.md`](docs/SOURCE_AND_SCOPE.md) — how the formalization
  relates to `main.tex` and what remains abstract.

For the algebraic development, start with `RequestProject/Main.lean`.  For the
bijection, import `RequestProject.Psi` and read `Psi/Defs.lean` followed by the
files in the order shown above.

## Building

The pinned Lean version is in `lean-toolchain`; the Mathlib dependency is in
`lakefile.toml` and `lake-manifest.json`.  Build everything with:

```bash
lake build RequestProject
```

All checked Lean modules are intended to compile without `sorry` or `admit`.
