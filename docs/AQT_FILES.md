# Algebraic development: file guide

The modules under `RequestProject/Aqt/` use the namespace `DyckAlgebra`.

## `Algebra.lean`

Defines the **level-graded path algebra** on the genuine generators
`ε_k`, `T_i`, `T_i⁻¹`, `d₊`, `d₋`, and `d₊*`.  Its relation family contains
(S), (B), (C), every relation (R1)--(R6), and every starred relation
(R1*)--(R6*), followed by (Q1), (Q1*), and (Q2).

The elements `Pre.yy` and `Pre.zz` are recursive definitions in those genuine
generators; they are not constructors of `Gen`.  The quotient is

```lean
Aqt q t := RingQuot (Rel q t).
```

## `Rep.lean`

Defines `AqtAction`, which packages a linear action as an algebra homomorphism
from the full quotient `Aqt q t` to `Module.End 𝕜 V`.  It also provides
`AqtAction.apply` and the expected addition, multiplication, and identity laws.
The local single-level interface used by finite `Θ` calculations is not an
`Aqt` representation and therefore lives in `Theta.lean`, under the explicit
name `ThetaData`.

## `Theta.lean`

Contains the general noncommutative identities and the finite, single-level
`ThetaData`/`DyckRepU` calculations.  This local calculation environment is
explicitly not presented as an action of the level-graded quotient.  The file
defines `w`, `s`, `s*`, `Θdp`, and `Θdps`, and proves the relevant compatibility
identities.

## `ThetaDescent.lean`

Uses `Gen`, `Pre`, `Rel`, and `Aqt` directly from `Algebra.lean`.  It introduces
no `RelCore` or `Aq0`.  Its main construction is

```lean
thetaDescent :
  (thetaGen : Gen → C) →
  (∀ {a b}, Rel q t a b → thetaPre thetaGen a = thetaPre thetaGen b) →
  Aqt q t →ₐ[𝕜] C
```

Thus the quotient theorem explicitly requires preservation of the complete
relation family, including all unstarred and starred R-relations.

## `PreserveKernel.lean` and `DGamma.lean`

Contain the kernel-preservation and `D_γ` operator consequences developed on
the local operator interface.

## `../Main.lean`

Imports the complete development and gives typed examples for the full algebra
action and quotient descent.
