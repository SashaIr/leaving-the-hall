import RequestProject.Aqt.Rep

/-!
# The `Θ` operator

This file uses the convention of the source throughout:

* `w = (1 + u y₁)⁻¹`,
* `s = u w y₁ z₁`,
* `s* = u (1 - z₁) y₁`,
* `Θ(d₊) = (1 - s)d₊`, and
* `Θ(d₊*) = (1 + s*)⁻¹d₊*`.

It isolates the finite algebraic identities behind the power-series argument.
The inverse `w` is supplied as two-sided inverse data, so the lemmas apply in
any algebra modelling the relevant completion.
-/

namespace DyckAlgebra
namespace Theta

variable {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]

/-- `s = u w y z`. -/
def s (u : 𝕜) (w y z : A) : A := u • (w * y * z)

/-- `s* = u (1-z)y`. -/
def sStar (u : 𝕜) (y z : A) : A := u • ((1 - z) * y)

/-- An inverse of `1 + u y` commutes with `y`. -/
lemma w_comm_y (u : 𝕜) (w y : A)
    (hwL : (1 + u • y) * w = 1) (hwR : w * (1 + u • y) = 1) :
    w * y = y * w := by
  by_cases hu : u = 0 <;> simp_all +decide [add_mul, mul_add]
  apply_fun (fun x => u⁻¹ • (x - w)) at hwL hwR
  simp_all +decide

/-- First identity in `lem:theta_q2` of the source. -/
lemma y_mul_one_add_sStar (u : 𝕜) (w y z : A)
    (hwL : (1 + u • y) * w = 1) (hyz : y * z = z * y) :
    y * (1 + sStar u y z) = (1 + u • y) * (1 - s u w y z) * y := by
  unfold s sStar
  simp_all +decide [mul_sub, sub_mul, ← mul_assoc]
  simp +decide [mul_add, add_mul, mul_sub, mul_assoc]
  simp +decide only [← mul_assoc, smul_sub]
  rw [← hyz, add_sub_assoc]

/-- Second identity in `lem:theta_q2` of the source. -/
lemma z_mul_one_sub_s (u : 𝕜) (w y z : A)
    (hwL : (1 + u • y) * w = 1) (hwR : w * (1 + u • y) = 1) :
    z * (1 - s u w y z) = (1 + sStar u y z) * w * z := by
  unfold s sStar
  have hw_comm : w * y = y * w := w_comm_y u w y hwL hwR
  simp_all +decide [mul_assoc, add_mul, mul_add, sub_mul, mul_sub]
  simp_all +decide [← mul_assoc, smul_sub]
  replace hwL := congr_arg (· * z) hwL
  simp_all +decide [mul_assoc, add_mul]
  grind

/-
`1+s* = (1+uy)(1-s₂)`, where `s₂ = u w z y`.
-/
lemma one_add_sStar_eq (u : 𝕜) (w y z : A)
    (hwL : (1 + u • y) * w = 1) :
    1 + sStar u y z = (1 + u • y) * (1 - u • (w * z * y)) := by
  simp +decide [sStar, mul_sub, sub_mul];
  simp +decide [ ← mul_assoc, hwL ];
  rw [ smul_sub, add_sub_assoc ]

end Theta
end DyckAlgebra


/-!
# `Θ` respects the defining relations

This file enriches a representation with the formal parameter `u` and the
inverses required by the source convention `w=(1+uy₁)⁻¹` and
`minv=(1+s*)⁻¹`.  It defines the images
`Θ(d₊)=(1-s)d₊`, `Θ(d₊*)=minv d₊*`, and proves the relation-preservation and
product identities used to descend `Θ` to the quotient.
-/

namespace DyckAlgebra

open scoped BigOperators

universe v

/-- Descending Hecke word in a fixed-level toy environment. -/
def thetaTdown {A : Type*} [Ring A] (T : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => T (n + 1) * thetaTdown T n

/-- Descending inverse-Hecke word in a fixed-level toy environment. -/
def thetaTdownInv {A : Type*} [Ring A] (Tinv : ℕ → A) : ℕ → A
  | 0 => 1
  | n + 1 => Tinv (n + 1) * thetaTdownInv Tinv n

/-- The paper's recursively defined `y_i`, specialized to one generic level. -/
def thetaYY {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (q : 𝕜) (level : ℕ) (Tinv T : ℕ → A) (dp dm : A) : ℕ → A
  | 0 => 0
  | 1 => (q ^ (level - 1) * (q - 1))⁻¹ •
      ((dp * dm - dm * dp) * thetaTdown T (level - 1))
  | i + 2 => q • (Tinv (i + 1) * thetaYY q level Tinv T dp dm (i + 1) * Tinv (i + 1))

/-- The paper's recursively defined normalized word `z_i/(qt)`, at one level. -/
def thetaZZ {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    (q t : 𝕜) (level : ℕ) (T Tinv : ℕ → A) (dps dm : A) : ℕ → A
  | 0 => 0
  | 1 => ((q * t)⁻¹ * (q ^ level * (1 - q)⁻¹)) •
      ((dps * dm - dm * dps) * thetaTdownInv Tinv (level - 1))
  | i + 2 => q⁻¹ • (T (i + 1) * thetaZZ q t level T Tinv dps dm (i + 1) * T (i + 1))

/-- A fixed-generic-level algebraic environment for the finite `Θ` identities.

Unlike `Aqt`, this structure does not contain a family of level components or
vertex idempotents: `level` records one generic level, and all arrows are
interpreted in one ambient ring.  It nevertheless records all six `R` relations
and all six starred relations at that level.  Its `yy` and `zz` projections below
are definitions in `T`, `Tinv`, `dp`, `dm`, and `dps`, not structure fields.

This remains a calculation interface rather than an action of `Aqt`; genuine
actions of the quotient are represented by `AqtAction` in `Rep.lean`. -/
structure ThetaData (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) where
  carrier : Type v
  [ring : Ring carrier]
  [algebra : Algebra 𝕜 carrier]
  T : ℕ → carrier
  Tinv : ℕ → carrier
  /-- The level represented by this local environment. -/
  level : ℕ
  /-- The second scalar parameter, needed for the normalized starred words. -/
  t : 𝕜
  dp : carrier
  dm : carrier
  dps : carrier
  skein : ∀ i, (T i - 1) * (T i + q • 1) = 0
  braid : ∀ i, T i * T (i+1) * T i = T (i+1) * T i * T (i+1)
  Tcomm : ∀ i j, i + 1 < j → T i * T j = T j * T i
  TinvL : ∀ i, T i * Tinv i = 1
  TinvR : ∀ i, Tinv i * T i = 1
  R1 : ∀ i, 2 ≤ i → i ≤ level - 2 → dm * T i = T i * dm
  R2 : ∀ i, 1 ≤ i → dp * T i = T (i+1) * dp
  R1s : ∀ i, 2 ≤ i → i ≤ level - 2 → dm * Tinv i = Tinv i * dm
  R2s : ∀ i, 1 ≤ i → dps * Tinv i = Tinv (i+1) * dps
  R3 : T 1 * dp * dp = dp * dp
  R3s : Tinv 1 * dps * dps = dps * dps
  R4 : 2 ≤ level → dm * dm * T (level - 1) = dm * dm
  R4s : 2 ≤ level → dm * dm * Tinv (level - 1) = dm * dm
  R5 : 2 ≤ level → dm * (dp * dm - dm * dp) * T (level - 1) =
    q • ((dp * dm - dm * dp) * dm)
  R5s : 2 ≤ level → dm * (dps * dm - dm * dps) * Tinv (level - 1) =
    q⁻¹ • ((dps * dm - dm * dps) * dm)
  R6 : T 1 * (dp * dm - dm * dp) * dp = q • (dp * (dp * dm - dm * dp))
  R6s : Tinv 1 * (dps * dm - dm * dps) * dps = q⁻¹ • (dps * (dps * dm - dm * dps))
  Q1 : ∀ i, thetaZZ q t level T Tinv dps dm (i+1) * dp = dp * thetaZZ q t level T Tinv dps dm i
  Q1s : ∀ i, thetaYY q level Tinv T dp dm (i+1) * dps = dps * thetaYY q level Tinv T dp dm i
  /-- At level `k`, the normalized `(Q2)` coefficient is `-q^k`. -/
  Q2scalar : cQ2 = -(q ^ level)
  Q2 : thetaZZ q t level T Tinv dps dm 1 * dp = cQ2 • (thetaYY q level Tinv T dp dm 1 * dps)
  yTcomm : ∀ i j, i ≠ j ∧ i ≠ j + 1 → thetaYY q level Tinv T dp dm i * T j = T j * thetaYY q level Tinv T dp dm i
  zTcomm : ∀ i j, i ≠ j ∧ i ≠ j + 1 → thetaZZ q t level T Tinv dps dm i * T j = T j * thetaZZ q t level T Tinv dps dm i
  ydm : ∀ i, thetaYY q level Tinv T dp dm i * dm = dm * thetaYY q level Tinv T dp dm i
  zdm : ∀ i, thetaZZ q t level T Tinv dps dm i * dm = dm * thetaZZ q t level T Tinv dps dm i
  yy_comm : ∀ i j, thetaYY q level Tinv T dp dm i * thetaYY q level Tinv T dp dm j = thetaYY q level Tinv T dp dm j * thetaYY q level Tinv T dp dm i
  zz_comm : ∀ i j, thetaZZ q t level T Tinv dps dm i * thetaZZ q t level T Tinv dps dm j = thetaZZ q t level T Tinv dps dm j * thetaZZ q t level T Tinv dps dm i
  z1y1 : thetaZZ q t level T Tinv dps dm 1 * T 1 * thetaYY q level Tinv T dp dm 1 = thetaYY q level Tinv T dp dm 2 * thetaZZ q t level T Tinv dps dm 1 * T 1
  y1z1 : thetaYY q level Tinv T dp dm 1 * Tinv 1 * thetaZZ q t level T Tinv dps dm 1 = thetaZZ q t level T Tinv dps dm 2 * thetaYY q level Tinv T dp dm 1 * Tinv 1
  T1symYa : T 1 * (thetaYY q level Tinv T dp dm 1 + thetaYY q level Tinv T dp dm 2) = (thetaYY q level Tinv T dp dm 1 + thetaYY q level Tinv T dp dm 2) * T 1
  T1symYm : T 1 * (thetaYY q level Tinv T dp dm 1 * thetaYY q level Tinv T dp dm 2) = (thetaYY q level Tinv T dp dm 1 * thetaYY q level Tinv T dp dm 2) * T 1
  T1symZa : T 1 * (thetaZZ q t level T Tinv dps dm 1 + thetaZZ q t level T Tinv dps dm 2) = (thetaZZ q t level T Tinv dps dm 1 + thetaZZ q t level T Tinv dps dm 2) * T 1
  T1symZm : T 1 * (thetaZZ q t level T Tinv dps dm 1 * thetaZZ q t level T Tinv dps dm 2) = (thetaZZ q t level T Tinv dps dm 1 * thetaZZ q t level T Tinv dps dm 2) * T 1

attribute [instance] ThetaData.ring ThetaData.algebra

namespace ThetaData

/-- The derived `y_i` word; it is not structure data or a generator. -/
abbrev yy {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : ThetaData 𝕜 q cQ2) (i : ℕ) : ρ.carrier :=
  thetaYY q ρ.level ρ.Tinv ρ.T ρ.dp ρ.dm i

/-- The derived normalized `z_i/(qt)` word; it is not structure data or a generator. -/
abbrev zz {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : ThetaData 𝕜 q cQ2) (i : ℕ) : ρ.carrier :=
  thetaZZ q ρ.t ρ.level ρ.T ρ.Tinv ρ.dps ρ.dm i

end ThetaData

/-- A `ThetaData` environment enriched with the formal parameter `u` and the
power-series inverses needed to state `Θ`.  It records the finite identities
expected in the `u`-completion, without itself claiming to be an `Aqt` action.
In particular, existence of these inverses is data rather than a construction
of the completion. -/
structure DyckRepU (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) extends ThetaData 𝕜 q cQ2 where
  /-- The formal parameter `u`. -/
  u : 𝕜
  /-- `w i = (1 + u y_i)⁻¹`. -/
  w : ℕ → carrier
  wL : ∀ i, (1 + u • ThetaData.yy toThetaData i) * w i = 1
  wR : ∀ i, w i * (1 + u • ThetaData.yy toThetaData i) = 1
  /-- `minv = (1 + s*)⁻¹`, where `s* = u(1-z₁)y₁`. -/
  minv : carrier
  mL : (1 + (u • ThetaData.yy toThetaData 1 - u • (ThetaData.zz toThetaData 1 * ThetaData.yy toThetaData 1))) * minv = 1
  mR : minv * (1 + (u • ThetaData.yy toThetaData 1 - u • (ThetaData.zz toThetaData 1 * ThetaData.yy toThetaData 1))) = 1

namespace DyckRepU

variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

/-- The element `s = u w₁ y₁ z₁`. -/
def sElt : ρ.carrier := ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1)

/-- `Θ(d_+) = (1 - s) d_+`. -/
def Θdp : ρ.carrier := (1 - ρ.sElt) * ρ.dp

/-- `Θ(d_+^*) = (1 + s*)⁻¹ d_+^* = minv d_+^*`. -/
def Θdps : ρ.carrier := ρ.minv * ρ.dps

/-- `Θ(y₁) = (1 - s) y₁`. -/
def Θy1 : ρ.carrier := (1 - ρ.sElt) * ρ.yy 1

/-- `Θ(z₁) = minv z₁`. -/
def Θz1 : ρ.carrier := ρ.minv * ρ.zz 1

/-
`w i` commutes with `y i`.
-/
lemma w_comm_yy (i : ℕ) : ρ.w i * ρ.yy i = ρ.yy i * ρ.w i :=
  Theta.w_comm_y ρ.u (ρ.w i) (ρ.yy i) (ρ.wL i) (ρ.wR i)

/-
`w 1` commutes with `T j` for `j ≥ 2`.
-/
lemma w1_comm_T (j : ℕ) (hj : 2 ≤ j) : ρ.w 1 * ρ.T j = ρ.T j * ρ.w 1 := by
  have h_comm : (1 + ρ.u • ρ.yy 1) * ρ.w 1 = 1 ∧ ρ.w 1 * (1 + ρ.u • ρ.yy 1) = 1 := by
    exact ⟨ ρ.wL 1, ρ.wR 1 ⟩;
  have h_comm : (1 + ρ.u • ρ.yy 1) * ρ.T j = ρ.T j * (1 + ρ.u • ρ.yy 1) := by
    simp +decide [ add_mul, mul_add, ρ.yTcomm 1 j ( by omega ) ];
  apply_fun (fun x => ρ.w 1 * x) at h_comm;
  grind

/-- The inverse `w₁` commutes with `d₋`, because the derived word `y₁` does. -/
lemma w1_comm_dm : ρ.w 1 * ρ.dm = ρ.dm * ρ.w 1 := by
  have hy : (1 + ρ.u • ρ.yy 1) * ρ.dm = ρ.dm * (1 + ρ.u • ρ.yy 1) := by
    simp [add_mul, mul_add, ρ.ydm 1]
  calc
    ρ.w 1 * ρ.dm = ρ.w 1 * ρ.dm * ((1 + ρ.u • ρ.yy 1) * ρ.w 1) := by rw [ρ.wL 1, mul_one]
    _ = ρ.w 1 * (ρ.dm * (1 + ρ.u • ρ.yy 1)) * ρ.w 1 := by simp only [mul_assoc]
    _ = ρ.w 1 * ((1 + ρ.u • ρ.yy 1) * ρ.dm) * ρ.w 1 := by rw [hy]
    _ = (ρ.w 1 * (1 + ρ.u • ρ.yy 1)) * ρ.dm * ρ.w 1 := by simp only [mul_assoc]
    _ = ρ.dm * ρ.w 1 := by rw [ρ.wR 1, one_mul]

/-- The correction term `s` commutes with `d₋`. -/
lemma sElt_comm_dm : ρ.sElt * ρ.dm = ρ.dm * ρ.sElt := by
  unfold sElt
  simp only [smul_mul_assoc, mul_smul_comm]
  congr 1
  calc
    ρ.w 1 * ρ.yy 1 * ρ.zz 1 * ρ.dm
        = ρ.w 1 * ρ.yy 1 * (ρ.zz 1 * ρ.dm) := by simp only [mul_assoc]
    _ = ρ.w 1 * ρ.yy 1 * (ρ.dm * ρ.zz 1) := by rw [ρ.zdm 1]
    _ = ρ.w 1 * (ρ.yy 1 * ρ.dm) * ρ.zz 1 := by simp only [mul_assoc]
    _ = ρ.w 1 * (ρ.dm * ρ.yy 1) * ρ.zz 1 := by rw [ρ.ydm 1]
    _ = (ρ.w 1 * ρ.dm) * ρ.yy 1 * ρ.zz 1 := by simp only [mul_assoc]
    _ = (ρ.dm * ρ.w 1) * ρ.yy 1 * ρ.zz 1 := by rw [ρ.w1_comm_dm]
    _ = ρ.dm * (ρ.w 1 * ρ.yy 1 * ρ.zz 1) := by simp only [mul_assoc]

/-- Replacing `d₊` by `Θ(d₊)=(1-s)d₊` left-multiplies its commutator
with `d₋` by `1-s`.  This is the basic reason that the derived `y₁` formula
transforms without adding `y₁` as independent data. -/
lemma theta_comm_dp_dm :
    ρ.Θdp * ρ.dm - ρ.dm * ρ.Θdp =
      (1 - ρ.sElt) * (ρ.dp * ρ.dm - ρ.dm * ρ.dp) := by
  have hs : (1 - ρ.sElt) * ρ.dm = ρ.dm * (1 - ρ.sElt) := by
    simp [sub_mul, mul_sub, ρ.sElt_comm_dm]
  unfold Θdp
  rw [mul_assoc, ← mul_assoc ρ.dm, ← hs, mul_assoc]
  noncomm_ring

/-- Computing the paper's recursive definition of `y₁` after transforming
`d₊` gives exactly the previously used formula `(1-s)y₁`. -/
lemma thetaYY_one :
    thetaYY q ρ.level ρ.Tinv ρ.T ρ.Θdp ρ.dm 1 = ρ.Θy1 := by
  simp only [thetaYY, Θy1, ThetaData.yy]
  rw [ρ.theta_comm_dp_dm]
  simp only [mul_assoc, mul_smul_comm]

/-
`s` commutes with `T j` for `j ≥ 2`.
-/
lemma sElt_comm_T (j : ℕ) (hj : 2 ≤ j) : ρ.sElt * ρ.T j = ρ.T j * ρ.sElt := by
  unfold DyckRepU.sElt;
  simp +decide only [smul_mul_assoc, mul_smul_comm];
  simp +decide only [mul_assoc, ρ.zTcomm 1 j (by omega)];
  simp +decide only [← mul_assoc, ρ.yTcomm 1 j (by omega)];
  rw [ ρ.w1_comm_T j hj ]

/-
`Θ` respects `(R2)`: `Θ(d_+ T i) = Θ(T (i+1) d_+)` for `i ≥ 1`.
-/
lemma theta_R2 (i : ℕ) (h : 1 ≤ i) : ρ.Θdp * ρ.T i = ρ.T (i+1) * ρ.Θdp := by
  unfold DyckRepU.Θdp;
  have := ρ.R2 i h;
  simp_all +decide [ mul_assoc, sub_mul, mul_sub ];
  simp +decide only [← mul_assoc, sElt_comm_T ρ (i + 1) (by linarith)]

/-- The element `s* = u(1-z₁)y₁`, so `minv = (1+s*)⁻¹`. -/
def sStarElt : ρ.carrier := ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1)

/-- The starred correction term also commutes with `d₋`. -/
lemma sStarElt_comm_dm : ρ.sStarElt * ρ.dm = ρ.dm * ρ.sStarElt := by
  unfold sStarElt
  rw [sub_mul, mul_sub]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [ρ.ydm 1]
  change ρ.u • (ρ.dm * ρ.yy 1) - ρ.u • (ρ.zz 1 * ρ.yy 1 * ρ.dm) =
    ρ.u • (ρ.dm * ρ.yy 1) - ρ.u • (ρ.dm * (ρ.zz 1 * ρ.yy 1))
  have hprod : ρ.zz 1 * ρ.yy 1 * ρ.dm = ρ.dm * (ρ.zz 1 * ρ.yy 1) := by
    calc
      ρ.zz 1 * ρ.yy 1 * ρ.dm = ρ.zz 1 * (ρ.yy 1 * ρ.dm) := by simp only [mul_assoc]
      _ = ρ.zz 1 * (ρ.dm * ρ.yy 1) := by rw [ρ.ydm 1]
      _ = (ρ.zz 1 * ρ.dm) * ρ.yy 1 := by simp only [mul_assoc]
      _ = (ρ.dm * ρ.zz 1) * ρ.yy 1 := by rw [ρ.zdm 1]
      _ = ρ.dm * (ρ.zz 1 * ρ.yy 1) := by simp only [mul_assoc]
  rw [hprod]

/-- The inverse `(1+s*)⁻¹` commutes with `d₋`. -/
lemma minv_comm_dm : ρ.minv * ρ.dm = ρ.dm * ρ.minv := by
  have hs : (1 + ρ.sStarElt) * ρ.dm = ρ.dm * (1 + ρ.sStarElt) := by
    simp [add_mul, mul_add, ρ.sStarElt_comm_dm]
  have hmL : (1 + ρ.sStarElt) * ρ.minv = 1 := by
    simpa [sStarElt] using ρ.mL
  have hmR : ρ.minv * (1 + ρ.sStarElt) = 1 := by
    simpa [sStarElt] using ρ.mR
  calc
    ρ.minv * ρ.dm = ρ.minv * ρ.dm * ((1 + ρ.sStarElt) * ρ.minv) := by
      rw [hmL, mul_one]
    _ = ρ.minv * (ρ.dm * (1 + ρ.sStarElt)) * ρ.minv := by simp only [mul_assoc]
    _ = ρ.minv * ((1 + ρ.sStarElt) * ρ.dm) * ρ.minv := by rw [hs]
    _ = (ρ.minv * (1 + ρ.sStarElt)) * ρ.dm * ρ.minv := by simp only [mul_assoc]
    _ = ρ.dm * ρ.minv := by rw [hmR, one_mul]

/-- Replacing `d₊*` by `Θ(d₊*)=minv d₊*` left-multiplies its commutator
with `d₋` by `minv`. -/
lemma theta_comm_dps_dm :
    ρ.Θdps * ρ.dm - ρ.dm * ρ.Θdps =
      ρ.minv * (ρ.dps * ρ.dm - ρ.dm * ρ.dps) := by
  unfold Θdps
  rw [mul_assoc, ← mul_assoc ρ.dm, ← ρ.minv_comm_dm, mul_assoc]
  noncomm_ring

/-- Recomputing the recursively defined normalized `z₁/(qt)` after
transforming `d₊*` gives `minv z₁`. -/
lemma thetaZZ_one :
    thetaZZ q ρ.t ρ.level ρ.T ρ.Tinv ρ.Θdps ρ.dm 1 = ρ.Θz1 := by
  simp only [thetaZZ, Θz1, ThetaData.zz]
  rw [ρ.theta_comm_dps_dm]
  simp only [mul_assoc, mul_smul_comm]

/-
`y i` commutes with `T j inv` when `i ≠ j`, `i ≠ j+1`.
-/
lemma yy_comm_Tinv (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) :
    ρ.yy i * ρ.Tinv j = ρ.Tinv j * ρ.yy i := by
  have hcomm := ρ.yTcomm i j h
  calc
    ρ.yy i * ρ.Tinv j = 1 * ρ.yy i * ρ.Tinv j := by rw [one_mul]
    _ = (ρ.Tinv j * ρ.T j) * ρ.yy i * ρ.Tinv j := by rw [ρ.TinvR]
    _ = ρ.Tinv j * (ρ.T j * ρ.yy i) * ρ.Tinv j := by simp only [mul_assoc]
    _ = ρ.Tinv j * (ρ.yy i * ρ.T j) * ρ.Tinv j := by rw [hcomm]
    _ = ρ.Tinv j * ρ.yy i * (ρ.T j * ρ.Tinv j) := by simp only [mul_assoc]
    _ = ρ.Tinv j * ρ.yy i := by rw [ρ.TinvL, mul_one]

/-
`z i` commutes with `T j inv` when `i ≠ j`, `i ≠ j+1`.
-/
lemma zz_comm_Tinv (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) :
    ρ.zz i * ρ.Tinv j = ρ.Tinv j * ρ.zz i := by
  have h_comm : ρ.zz i * ρ.T j = ρ.T j * ρ.zz i := by
    exact ρ.zTcomm i j h;
  have h_comm_inv : ρ.Tinv j * ρ.T j = 1 := by
    exact ρ.TinvR j;
  have h_comm_inv : ρ.T j * ρ.Tinv j = 1 := by
    exact ρ.TinvL j;
  apply_fun ( · * ρ.Tinv j ) at h_comm;
  grind

/-
`s^*` commutes with `T j inv` for `j ≥ 2`.
-/
lemma sStarElt_comm_Tinv (j : ℕ) (hj : 2 ≤ j) :
    ρ.sStarElt * ρ.Tinv j = ρ.Tinv j * ρ.sStarElt := by
  unfold DyckRepU.sStarElt;
  simp +decide [mul_sub, sub_mul, mul_assoc];
  simp +decide only [ρ.yy_comm_Tinv 1 j (by omega), ← mul_assoc, ρ.zz_comm_Tinv 1 j (by omega)]

/-
`minv = (1 + s*)⁻¹` commutes with `T j inv` for `j ≥ 2`.
-/
lemma minv_comm_Tinv (j : ℕ) (hj : 2 ≤ j) :
    ρ.minv * ρ.Tinv j = ρ.Tinv j * ρ.minv := by
  have := ρ.mL;
  have := ρ.mR;
  convert congr_arg ( fun x => ρ.minv * x * ρ.Tinv j ) this using 1;
  · simp +decide [ this ];
  · have h_comm : (1 + (ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1))) * ρ.Tinv j = ρ.Tinv j * (1 + (ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1))) := by
      have := ρ.sStarElt_comm_Tinv j hj;
      simp_all +decide [ add_mul, mul_add, DyckRepU.sStarElt ];
    convert congr_arg ( fun x => ρ.minv * x * ρ.minv ) h_comm using 1 <;> simp +decide [mul_assoc];
    · simp +decide [ ← mul_assoc, this ];
    · simp +decide [‹(1 + (ρ.u • ρ.yy 1 - ρ.u • (ρ.zz 1 * ρ.yy 1))) * ρ.minv = 1›]

/-
`Θ` respects `(R2*)`: `Θ(d_+^* T i inv) = Θ(T (i+1) inv d_+^*)` for `i ≥ 1`.
-/
lemma theta_R2s (i : ℕ) (h : 1 ≤ i) : ρ.Θdps * ρ.Tinv i = ρ.Tinv (i+1) * ρ.Θdps := by
  rw [ DyckRepU.Θdps, mul_assoc, ρ.R2s i h, ← mul_assoc, ρ.minv_comm_Tinv ];
  · rw [ mul_assoc ];
  · linarith

/-- `s₂ = u w₁ z₁ y₁`, the companion of `s`. -/
def s2Elt : ρ.carrier := ρ.u • (ρ.w 1 * ρ.zz 1 * ρ.yy 1)

/-
`1+s* = (1+uy₁)(1-s₂)`.
-/
lemma sStar_factor : 1 + ρ.sStarElt = (1 + ρ.u • ρ.yy 1) * (1 - ρ.s2Elt) := by
  have := @DyckAlgebra.Theta.one_add_sStar_eq;
  convert this ρ.u ( ρ.w 1 ) ( ρ.yy 1 ) ( ρ.zz 1 ) ( ρ.wL 1 ) using 1;
  unfold DyckRepU.sStarElt Theta.sStar
  simp +decide [ sub_mul, smul_sub ]

/-
`(1 - s₂) minv = w₁`.
-/
lemma s2_mul_minv : (1 - ρ.s2Elt) * ρ.minv = ρ.w 1 := by
  have h_mul : ρ.w 1 * ((1 + ρ.u • ρ.yy 1) * (1 - ρ.s2Elt)) * ρ.minv = ρ.w 1 * 1 := by
    rw [ ← ρ.sStar_factor, mul_assoc ];
    exact congr_arg _ ρ.mL;
  convert h_mul using 1 <;> simp +decide [ ← mul_assoc, ρ.wR ]

/-
`(1 - s₂)` is right–invertible witnessed by `minv (1 + u y₁)`.
-/
lemma s2_mul_right_inv : (1 - ρ.s2Elt) * (ρ.minv * (1 + ρ.u • ρ.yy 1)) = 1 := by
  rw [ ← mul_assoc, ρ.s2_mul_minv, ρ.wR ]

/-
`(1 - s₂)` is left–invertible witnessed by `minv (1 + u y₁)`.
-/
lemma s2_mul_left_inv : (ρ.minv * (1 + ρ.u • ρ.yy 1)) * (1 - ρ.s2Elt) = 1 := by
  have := ρ.sStar_factor;
  convert ρ.mR using 1;
  rw [ mul_assoc, ← this ] ; simp +decide [ DyckRepU.sStarElt ]

/-
Core of `lem:theta_q2`: `minv z₁ (1 - s) = w₁ z₁`.
-/
lemma theta_z1_lhs : ρ.minv * ρ.zz 1 * (1 - ρ.sElt) = ρ.w 1 * ρ.zz 1 := by
  have h_comm : ρ.minv * (1 + ρ.sStarElt) = 1 := by
    convert ρ.mR using 1;
  have h_comm : ρ.zz 1 * (1 - ρ.sElt) = (1 + ρ.sStarElt) * ρ.w 1 * ρ.zz 1 := by
    convert DyckAlgebra.Theta.z_mul_one_sub_s _ _ _ _ _ _ using 1;
    · simp +decide [ Theta.sStar, DyckRepU.sStarElt ];
      simp +decide [sub_mul, smul_sub]
    · exact ρ.wL 1;
    · exact ρ.wR 1;
  grind +revert

/-
Core of `lem:theta_q2`: `(1 - s) y₁ minv = w₁ y₁`.

`w₁ y₁ (1 + u y₁) = y₁`.
-/
lemma w1_yy1_one_add : ρ.w 1 * ρ.yy 1 * (1 + ρ.u • ρ.yy 1) = ρ.yy 1 := by
  convert congr_arg ( fun x => ρ.yy 1 * x ) ( ρ.wR 1 ) using 1 ; simp +decide [mul_assoc, mul_add];
  · grind +suggestions;
  · rw [ mul_one ]

/-
The algebraic core of `theta_y1_rhs`: `(1 - s) y₁ = w₁ y₁ (1 + s*)`.
-/
lemma theta_y1_rhs_key :
    (1 - ρ.sElt) * ρ.yy 1 = ρ.w 1 * ρ.yy 1 * (1 + ρ.sStarElt) := by
  simp_all +decide [DyckRepU.sElt, DyckRepU.sStarElt];
  have := ρ.wR 1; simp_all +decide [mul_assoc, mul_add, sub_mul, mul_sub] ;
  replace this := congr_arg ( · * ρ.yy 1 ) this ; simp_all +decide [mul_assoc, add_mul];
  grind

lemma theta_y1_rhs : (1 - ρ.sElt) * ρ.yy 1 * ρ.minv = ρ.w 1 * ρ.yy 1 := by
  have hmL : (1 + ρ.sStarElt) * ρ.minv = 1 := ρ.mL
  calc (1 - ρ.sElt) * ρ.yy 1 * ρ.minv
      = (ρ.w 1 * ρ.yy 1 * (1 + ρ.sStarElt)) * ρ.minv := by rw [ρ.theta_y1_rhs_key]
    _ = ρ.w 1 * ρ.yy 1 * ((1 + ρ.sStarElt) * ρ.minv) := by rw [mul_assoc]
    _ = ρ.w 1 * ρ.yy 1 := by rw [hmL, mul_one]

/-
`Θ` respects `(Q2)`: `Θ(z₁ d_+) = cQ2 · Θ(y₁ d_+^*)`.
-/
lemma theta_Q2 : ρ.Θz1 * ρ.Θdp = cQ2 • (ρ.Θy1 * ρ.Θdps) := by
  convert congr_arg ( fun x : ρ.carrier => x * ρ.dp ) ρ.theta_z1_lhs using 1;
  · simp +decide [ mul_assoc, DyckRepU.Θz1, DyckRepU.Θdp ];
  · convert congr_arg ( fun x : ρ.carrier => cQ2 • ( x * ρ.dps ) ) ρ.theta_y1_rhs using 1;
    · simp +decide [ mul_assoc, DyckRepU.Θy1, DyckRepU.Θdps ];
    · convert congr_arg ( fun x : ρ.carrier => ρ.w 1 * x ) ρ.Q2 using 1 <;> simp +decide [ mul_assoc ]

/-- First identity of `cor:theta_yz`: the transformed product `z₁ d₊`
is multiplication on the left by the geometric-series factor `w₁`. -/
lemma theta_z1_dp : ρ.Θz1 * ρ.Θdp = ρ.w 1 * ρ.zz 1 * ρ.dp := by
  rw [DyckRepU.Θz1, DyckRepU.Θdp]
  rw [← mul_assoc, ρ.theta_z1_lhs, mul_assoc]

/-- Second identity of `cor:theta_yz`: the transformed product `y₁ d₊*`
is multiplication on the left by the geometric-series factor `w₁`. -/
lemma theta_y1_dps : ρ.Θy1 * ρ.Θdps = ρ.w 1 * ρ.yy 1 * ρ.dps := by
  rw [DyckRepU.Θy1, DyckRepU.Θdps]
  rw [← mul_assoc, ρ.theta_y1_rhs, mul_assoc]

end DyckRepU

end DyckAlgebra
