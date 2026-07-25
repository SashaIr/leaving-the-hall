# Algebraic development: exact file guide

The modules under `RequestProject/Aqt/` use the namespace `DyckAlgebra`.
This guide distinguishes declarations that are **constructed or proved** from
interfaces whose mathematical laws are **fields/hypotheses**.

## `Algebra.lean`: the presented algebra

This is the only file that defines the quotient called `Aqt`.

* `Gen` has constructors `eps k`, `T k i`, `Tinv k i`, `dp k`, `dm k`, and
  `dps k`.
* `Pre 𝕜` is the unital free algebra on `Gen`.
* `Pre.yy q k i` and `Pre.zz q t k i` are recursive words in those generators.
  They are not constructors of `Gen`.  `zz` denotes the paper's normalized
  element `z_i/(qt)`, not its unnormalized `z_i`.
* `Rel q t` has support and orthogonality constructors, Hecke inverse
  constructors, `(S)`, `(B)`, `(C)`, all of `(R1)`--`(R6)`, all of
  `(R1*)`--`(R6*)`, and `(Q1)`, `(Q1*)`, `(Q2)`.
* `Aqt q t := RingQuot (Rel q t)`.

### Differences from the paper's presentation

The paper uses an infinite path algebra over `ℚ(q,t)`.  Lean uses a unital free
algebra over an arbitrary field, with infinitely many explicit orthogonal
idempotents and support relations.  Its global unit is therefore not an
individual paper vertex idempotent.  `Tinv` is an explicit generator constrained
by left and right inverse relations.  The paper describes a free product of two
Dyck path algebras and identifies starred data; Lean directly presents the
result after those identifications.

Because the parameters are arbitrary field elements, no assumptions such as
`q ≠ 0`, `q ≠ 1`, or `t ≠ 0` are built into `Aqt`.  At singular specializations,
field inverses in the formulas for `yy` and `zz` become Lean's totalized inverse
of zero, so this is not automatically the same object as specialization of the
paper's rational-function algebra.  The paper's bigrading is described in the
source but is not encoded as a graded type in Lean.

## `Rep.lean`: an abstract action interface

`AqtAction` packages an already-supplied algebra homomorphism

```lean
Aqt q t →ₐ[𝕜] Module.End 𝕜 V.
```

It provides application and elementary homomorphism laws.  It does **not**
construct the paper's carrier
`⊕ k, Λ ⊗ ℚ(q,t)[y₁⁺⁻¹,…,yₖ⁺⁻¹]`, symmetric functions, plethysm, or the displayed
formulas for `T_i`, `d₋`, `d₊`, and `d₊*`.

## `Theta.lean`: fixed-level calculations, not `Aqt`

The first section proves general identities in an arbitrary noncommutative
algebra.  The second defines `ThetaData`, a fixed-generic-level interface:

* `level` selects one level, but all elements live in one ambient ring; there
  are no vertex idempotents or typed hom-spaces;
* `T`, `Tinv`, `dp`, `dm`, and `dps` are supplied elements;
* all `(R1)`--`(R6)` and `(R1*)`--`(R6*)` are fields of the structure;
* `ThetaData.yy` and `ThetaData.zz` are recursively defined from those supplied
  elements and are **not fields**; `zz` is again normalized `z/(qt)`;
* `(Q1)`, `(Q1*)`, `(Q2)` and several standard identities involving the derived
  `yy`/`zz` words are fields (assumptions), not derived in this file;
* `Q2scalar` ties the formerly free local coefficient to the paper's value
  `cQ2 = -q^level`.

Since level-changing paths are collapsed into one ring, the local forms of
`(R1)`, `(R4)`, and `(R5)` cannot express the source and target levels visible
in `Algebra.Rel`.  Thus `ThetaData` is useful for finite word calculations but
is not a presentation equivalent to `Aqt`.

`DyckRepU` extends this interface by supplying `u`, two-sided inverses
`w_i = (1+u y_i)⁻¹`, and `minv = (1+s*)⁻¹`.  No formal-power-series ring or
completion is constructed.  The file defines `s`, `s*`, `Θdp`, `Θdps`, `Θy1`,
and `Θz1`.  It proves that `w₁` and `s` commute with `d₋`, and consequently
proves directly from the recursive definition that recomputing `y₁` with
`Θ(d₊)` gives `(1-s)y₁`; thus `Θy1` is no longer merely an unrelated formula.
It also proves preservation of the local `(R2)`, `(R2*)`, and `(Q2)` identities
and the two product formulas used later.  It does not prove in this interface
that the proposed transformation preserves every `Rel` constructor.

## `ThetaDescent.lean`: the universal quotient mechanism

This file uses the genuine `Gen`, `Pre`, `Rel`, and `Aqt` from `Algebra.lean`.
Its construction is

```lean
thetaDescent :
  (thetaGen : Gen → C) →
  (∀ {a b}, Rel q t a b → thetaPre thetaGen a = thetaPre thetaGen b) →
  Aqt q t →ₐ[𝕜] C
```

The complete relation-preservation proof is an explicit input named
`preserves`.  Consequently this is a proved universal-property theorem, but the
project does not instantiate it with the paper's completed target and a proof
that the particular `Θ` formulas preserve every constructor of `Rel`.

## `PreserveKernel.lean`

This proves conditional algebraic consequences corresponding to `(I1)` and
`(I2)` in the fixed-level `DyckRepU` interface.  The required level-graded
annihilator, `(Q2)`, and `s*`-annihilation facts occur as hypotheses where the
fixed-level model cannot supply them.  These are not theorems about a constructed
symmetric-function representation.

## `DGamma.lean`

This defines `D_γ` words for lists of natural numbers and proves abstract
intertwining and conjugation lemmas.  It now also isolates the paper's two
basic commutation relations.  With
`D⁺ = d₋ w₁ (-y₁) d₊*` (the inverse-form positive `D` series), Lean proves

```text
Θ(D₁) = D⁺,
Θ(e₁) = e₁ + D⁺ - D₁              (at level zero),
U D₁ = D⁺ U,
U e₁ = (e₁ + D⁺ - D₁) U.
```

The last two statements assume that `U` intertwines the constituent generators.
After expanding `w₁=(1+u y₁)⁻¹`, these are the source relations
`[Θ,e₁]=∑_{n≥2}u^(n-1)Dₙ Θ` and
`[Θ,D₁]=∑_{n≥2}u^(n-1)Dₙ Θ`.

The paper permits integer compositions when inverse `y₁` powers make sense;
Lean uses naturals and assigns the empty list the value zero.  It does not
formalize the formal-series coefficient extraction, the paper's shuffle-algebra
coefficient formulas, or identify the abstract intertwiner with the classical
symmetric-function Theta generating series.

## `../Main.lean`

This imports the algebraic development and gives typed examples of the
interfaces and established conditional results.  Examples are not additional
constructions of the missing concrete action or completed endomorphism.
