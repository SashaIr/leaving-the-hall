# Algebraic development: file guide

The modules under `RequestProject/Aqt/` implement the algebraic part of the
project.  They share the namespace `DyckAlgebra`.

## `Algebra.lean`

Defines the generators `Gen`, the free associative algebra `Pre`, and the
relation family `Rel`.  The relations include the Hecke, braid, inverse,
intertwining, `(Q1)`, `(Q2)`, and required `y`/`z` commutation laws.  The
presented algebra is

```lean
Aqt q cQ2 := RingQuot (Rel q cQ2).
```

The parameter `cQ2` abstracts the coefficient that depends on the level in the
fully graded path algebra.

## `Rep.lean`

Defines `DyckRep`, an operator-algebra interpretation of all generators with
proofs of all relations.  `DyckRep.preLift` interprets the free algebra and
`DyckRep.lift` descends this interpretation to

```lean
Aqt q cQ2 →ₐ[𝕜] carrier.
```

This is the project's abstract implementation of an action.  The intended
carrier is the algebra of operators on the graded symmetric-function module,
but no concrete plethystic symmetric-function datatype is introduced.

## `Theta.lean`

Contains general noncommutative identities for the ingredients

```text
w = (1 + u y)⁻¹,  s = u w y z,  s* = u(1-z)y.
```

These identities provide the finite algebra behind the transformed operators.

## `ThetaHom.lean`

Extends a representation to `DyckRepU` by adding `u`, `w`, the inverse of
`1+s*`, and their defining equations.  It defines `Θdp`, `Θdps`, `Θy1`, and
`Θz1`, proves preservation of the core intertwining relations, proves `(Q2)`
compatibility (`theta_Q2`), and establishes the two product formulas
`theta_z1_dp` and `theta_y1_dps`.

## `ThetaDescent.lean`

Defines the core presentation `Aq0`, its transformed generator map, and the key
relation-preservation lemma `thetaPre_relCore`.  The principal construction is

```lean
DyckRepU.thetaDescent : Aq0 q →ₐ[𝕜] carrier,
```

which states that the transformed generator assignment passes to the quotient.
Compatibility with the additional `(Q2)` relation is supplied by
`ThetaHom.lean`.

## `DGamma.lean`

Defines the natural-composition word `dGamma` and its generatorwise transformed
word `thetaDGamma`.  It proves:

- intertwining of powers, tails, and complete `D_γ` words;
- the abstract identity `Θ(L) = U L U⁻¹` from `U L = Θ(L) U`;
- conjugation of every `D_γ` by an invertible operator implementing `Θ` on the
  constituent generators.

These are the operator-algebra forms of the remaining conjugation and
commutation results in the source.  Identifying `U` with the classical
symmetric-function series and expanding the shuffle-indexed coefficients needs
the concrete graded symmetric-function model omitted by this project.

## `PreserveKernel.lean`

Formalizes preservation of the `(I1)` and `(I2)` kernel relations at arbitrary
levels under explicit level-specific hypotheses.  Its main chain is:

- `sStar_acts_as_0`;
- `minv_mul_dps_pow` and `theta_dps_pow_eq`;
- `theta_preserve_I1_via_sStar`;
- `theta_preserve_I2_scalar_via_sStar` and its `q^k` specialization.

The explicit hypotheses reflect the single-generic-level model: the surrounding
files do not construct the full family of graded idempotents and
level-dependent operators.

## `../Main.lean`

Imports the algebraic development, including `DGamma.lean`, and presents short typed examples of the
principal definitions and theorems.  It is the recommended algebraic entry
point.
