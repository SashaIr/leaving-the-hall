import Mathlib

/-!
# The Dyck path algebra `A_{q,t}`

This file implements (a faithful presentation of) the *Dyck path algebra*
`𝒜_{q,t}` of Carlsson–Mellit and Mellit, as a quotient of a free associative
algebra by the defining relations.

## Design / scope

The full algebra `𝒜_{q,t}` is the path algebra of an infinite quiver with
vertex set `ℕ` (arrows `d_+ : k → k+1`, `d_- : k+1 → k` and loops
`T_1, …, T_{k-1}`), with the elements `y_i` and `z_i = y_i^*` *derived* from
`d_±`, `d_±^*` and the `T_i`.

For the purpose of the `Θ`-operator theorem (`Θ` extends to an endomorphism of
`𝒜_{q,t}[[u]]`), the proof only uses the *commutation relations* satisfied by
`T_i`, `d_±`, `d_+^*`, `y_i`, `z_i`.  We therefore present the algebra on these
generators subject to exactly those relations.  This is faithful to the paper's
own proof of Theorem 4.1, which is carried out entirely at the level of these
relations.

Simplifications relative to the fully graded path algebra, all harmless for the
`Θ` theorem, are documented explicitly:

* we work at a single "generic level", so the idempotents `ε_k`, the
  level bookkeeping, and the level–range relations `(R1)`, `(R4)`, `(R5)` are
  omitted;
* the level–dependent scalar `-q^k` appearing in relation `(Q2)` is
  replaced by an abstract scalar parameter `cQ2`;
* `y_i`, `z_i` are taken as generators subject to the commutation relations that
  the paper establishes for them.
-/

namespace DyckAlgebra

open scoped BigOperators

/-- Abstract generators of the Dyck path algebra fragment. -/
inductive Gen where
  | T (i : ℕ)
  | Tinv (i : ℕ)
  | dp
  | dm
  | dps
  | y (i : ℕ)
  | z (i : ℕ)
  deriving DecidableEq

variable (𝕜 : Type*) [Field 𝕜]

/-- The free algebra on the generators. -/
abbrev Pre : Type _ := FreeAlgebra 𝕜 Gen

namespace Pre

/-- Generator `T i`. -/
def T (i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (Gen.T i)
/-- Generator `T i⁻¹`. -/
def Tinv (i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (Gen.Tinv i)
/-- Generator `d₊`. -/
def dp : Pre 𝕜 := FreeAlgebra.ι 𝕜 Gen.dp
/-- Generator `d₋`. -/
def dm : Pre 𝕜 := FreeAlgebra.ι 𝕜 Gen.dm
/-- Generator `d₊^*`. -/
def dps : Pre 𝕜 := FreeAlgebra.ι 𝕜 Gen.dps
/-- Generator `y i`. -/
def yy (i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (Gen.y i)
/-- Generator `z i`. -/
def zz (i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (Gen.z i)

end Pre

open Pre

variable {𝕜}

/-- The defining relations of the Dyck path algebra fragment, with structure
constant `q` (the Hecke parameter) and `cQ2` (an abstract stand–in for the
level–dependent scalar `-q^k` of relation `(Q2)`). -/
inductive Rel (q cQ2 : 𝕜) : Pre 𝕜 → Pre 𝕜 → Prop
  /-- Skein relation `(T i - 1)(T i + q) = 0`. -/
  | skein (i : ℕ) : Rel q cQ2 ((T 𝕜 i - 1) * (T 𝕜 i + q • 1)) 0
  /-- Braid relation. -/
  | braid (i : ℕ) : Rel q cQ2 (T 𝕜 i * T 𝕜 (i+1) * T 𝕜 i) (T 𝕜 (i+1) * T 𝕜 i * T 𝕜 (i+1))
  /-- Far commutation `T i T j = T j T i` for `i + 1 < j`. -/
  | Tcomm (i j : ℕ) (h : i + 1 < j) : Rel q cQ2 (T 𝕜 i * T 𝕜 j) (T 𝕜 j * T 𝕜 i)
  /-- `T i` is invertible with inverse `Tinv i` (right). -/
  | TinvL (i : ℕ) : Rel q cQ2 (T 𝕜 i * Tinv 𝕜 i) 1
  /-- `T i` is invertible with inverse `Tinv i` (left). -/
  | TinvR (i : ℕ) : Rel q cQ2 (Tinv 𝕜 i * T 𝕜 i) 1
  /-- `(R2)`: `d₊ T i = T (i+1) d₊` for `i ≥ 1`. -/
  | R2 (i : ℕ) (h : 1 ≤ i) : Rel q cQ2 (dp 𝕜 * T 𝕜 i) (T 𝕜 (i+1) * dp 𝕜)
  /-- `(R2*)`: `d₊^* T i⁻¹ = T (i+1)⁻¹ d₊^*` for `i ≥ 1`. -/
  | R2s (i : ℕ) (h : 1 ≤ i) : Rel q cQ2 (dps 𝕜 * Tinv 𝕜 i) (Tinv 𝕜 (i+1) * dps 𝕜)
  /-- `(R3)`: `T 1 d₊² = d₊²`. -/
  | R3 : Rel q cQ2 (T 𝕜 1 * dp 𝕜 * dp 𝕜) (dp 𝕜 * dp 𝕜)
  /-- `(R3*)`: `T 1⁻¹ (d₊^*)² = (d₊^*)²`. -/
  | R3s : Rel q cQ2 (Tinv 𝕜 1 * dps 𝕜 * dps 𝕜) (dps 𝕜 * dps 𝕜)
  /-- `(R6)`: `T 1 [d₊,d₋] d₊ = q d₊ [d₊,d₋]`. -/
  | R6 : Rel q cQ2 (T 𝕜 1 * (dp 𝕜 * dm 𝕜 - dm 𝕜 * dp 𝕜) * dp 𝕜)
      (q • (dp 𝕜 * (dp 𝕜 * dm 𝕜 - dm 𝕜 * dp 𝕜)))
  /-- `(R6*)`: dual of `(R6)` for `A_{q⁻¹}`. -/
  | R6s : Rel q cQ2 (Tinv 𝕜 1 * (dps 𝕜 * dm 𝕜 - dm 𝕜 * dps 𝕜) * dps 𝕜)
      (q⁻¹ • (dps 𝕜 * (dps 𝕜 * dm 𝕜 - dm 𝕜 * dps 𝕜)))
  /-- `(Q1)`: `z (i+1) d₊ = d₊ z i`. -/
  | Q1 (i : ℕ) : Rel q cQ2 (zz 𝕜 (i+1) * dp 𝕜) (dp 𝕜 * zz 𝕜 i)
  /-- `(Q1*)`: `y (i+1) d₊^* = d₊^* y i`. -/
  | Q1s (i : ℕ) : Rel q cQ2 (yy 𝕜 (i+1) * dps 𝕜) (dps 𝕜 * yy 𝕜 i)
  /-- `(Q2)`: `z 1 d₊ = -q^k y 1 d₊^*` (scalar abstracted as `cQ2`). -/
  | Q2 : Rel q cQ2 (zz 𝕜 1 * dp 𝕜) (cQ2 • (yy 𝕜 1 * dps 𝕜))
  /-- `y i` commutes with `T j` when `i ≠ j`, `i ≠ j+1`. -/
  | yTcomm (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) : Rel q cQ2 (yy 𝕜 i * T 𝕜 j) (T 𝕜 j * yy 𝕜 i)
  /-- `z i` commutes with `T j` when `i ≠ j`, `i ≠ j+1`. -/
  | zTcomm (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) : Rel q cQ2 (zz 𝕜 i * T 𝕜 j) (T 𝕜 j * zz 𝕜 i)
  /-- `y i` commutes with `d₋`. -/
  | ydm (i : ℕ) : Rel q cQ2 (yy 𝕜 i * dm 𝕜) (dm 𝕜 * yy 𝕜 i)
  /-- `z i` commutes with `d₋`. -/
  | zdm (i : ℕ) : Rel q cQ2 (zz 𝕜 i * dm 𝕜) (dm 𝕜 * zz 𝕜 i)
  /-- `y i` and `y j` commute. -/
  | yy_comm (i j : ℕ) : Rel q cQ2 (yy 𝕜 i * yy 𝕜 j) (yy 𝕜 j * yy 𝕜 i)
  /-- `z i` and `z j` commute. -/
  | zz_comm (i j : ℕ) : Rel q cQ2 (zz 𝕜 i * zz 𝕜 j) (zz 𝕜 j * zz 𝕜 i)
  /-- `z 1 T 1 y 1 = y 2 z 1 T 1`. -/
  | z1y1 : Rel q cQ2 (zz 𝕜 1 * T 𝕜 1 * yy 𝕜 1) (yy 𝕜 2 * zz 𝕜 1 * T 𝕜 1)
  /-- `y 1 T 1⁻¹ z 1 = z 2 y 1 T 1⁻¹`. -/
  | y1z1 : Rel q cQ2 (yy 𝕜 1 * Tinv 𝕜 1 * zz 𝕜 1) (zz 𝕜 2 * yy 𝕜 1 * Tinv 𝕜 1)
  /-- `T 1` commutes with `y 1 + y 2`. -/
  | T1symYa : Rel q cQ2 (T 𝕜 1 * (yy 𝕜 1 + yy 𝕜 2)) ((yy 𝕜 1 + yy 𝕜 2) * T 𝕜 1)
  /-- `T 1` commutes with `y 1 y 2`. -/
  | T1symYm : Rel q cQ2 (T 𝕜 1 * (yy 𝕜 1 * yy 𝕜 2)) ((yy 𝕜 1 * yy 𝕜 2) * T 𝕜 1)
  /-- `T 1` commutes with `z 1 + z 2`. -/
  | T1symZa : Rel q cQ2 (T 𝕜 1 * (zz 𝕜 1 + zz 𝕜 2)) ((zz 𝕜 1 + zz 𝕜 2) * T 𝕜 1)
  /-- `T 1` commutes with `z 1 z 2`. -/
  | T1symZm : Rel q cQ2 (T 𝕜 1 * (zz 𝕜 1 * zz 𝕜 2)) ((zz 𝕜 1 * zz 𝕜 2) * T 𝕜 1)

/-- The Dyck path algebra fragment `𝒜_{q,t}` as the quotient of the free algebra
by the defining relations. -/
abbrev Aqt (q cQ2 : 𝕜) : Type _ := RingQuot (Rel q cQ2)

end DyckAlgebra
