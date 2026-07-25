import RequestProject.Aqt.Theta

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

/-- A representation of `𝒜_{q,t}` enriched with the formal parameter `u` and the
power–series inverses needed to state `Θ`.  This models the `u`-completion
`𝒜_{q,t}[[u]]`. -/
structure DyckRepU (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) extends DyckRep 𝕜 q cQ2 where
  /-- The formal parameter `u`. -/
  u : 𝕜
  /-- `w i = (1 + u y_i)⁻¹`. -/
  w : ℕ → carrier
  wL : ∀ i, (1 + u • yy i) * w i = 1
  wR : ∀ i, w i * (1 + u • yy i) = 1
  /-- `minv = (1 + s*)⁻¹`, where `s* = u(1-z₁)y₁`. -/
  minv : carrier
  mL : (1 + (u • yy 1 - u • (zz 1 * yy 1))) * minv = 1
  mR : minv * (1 + (u • yy 1 - u • (zz 1 * yy 1))) = 1

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

/-
`y i` commutes with `T j inv` when `i ≠ j`, `i ≠ j+1`.
-/
lemma yy_comm_Tinv (i j : ℕ) (h : i ≠ j ∧ i ≠ j + 1) :
    ρ.yy i * ρ.Tinv j = ρ.Tinv j * ρ.yy i := by
  grind +suggestions

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
  simp +decide [ mul_sub, sub_mul, mul_assoc, mul_comm ];
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
    convert congr_arg ( fun x => ρ.minv * x * ρ.minv ) h_comm using 1 <;> simp +decide [ mul_assoc, this ];
    · simp +decide [ ← mul_assoc, this ];
    · simp +decide [ ← mul_assoc, ‹ ( 1 + ( ρ.u • ρ.yy 1 - ρ.u • ( ρ.zz 1 * ρ.yy 1 ) ) ) * ρ.minv = 1 › ]

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
  unfold DyckRepU.sStarElt Theta.sStar; simp +decide [ mul_assoc ] ;
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
      simp +decide [ sub_mul, mul_sub, smul_sub, sub_smul ];
    · exact ρ.wL 1;
    · exact ρ.wR 1;
  grind +revert

/-
Core of `lem:theta_q2`: `(1 - s) y₁ minv = w₁ y₁`.

`w₁ y₁ (1 + u y₁) = y₁`.
-/
lemma w1_yy1_one_add : ρ.w 1 * ρ.yy 1 * (1 + ρ.u • ρ.yy 1) = ρ.yy 1 := by
  convert congr_arg ( fun x => ρ.yy 1 * x ) ( ρ.wR 1 ) using 1 ; simp +decide [ mul_assoc, mul_add, add_mul ];
  · grind +suggestions;
  · rw [ mul_one ]

/-
The algebraic core of `theta_y1_rhs`: `(1 - s) y₁ = w₁ y₁ (1 + s*)`.
-/
lemma theta_y1_rhs_key :
    (1 - ρ.sElt) * ρ.yy 1 = ρ.w 1 * ρ.yy 1 * (1 + ρ.sStarElt) := by
  simp_all +decide [ Theta.s, Theta.sStar, DyckRepU.sElt, DyckRepU.sStarElt ];
  have := ρ.wR 1; simp_all +decide [ mul_assoc, mul_add, add_mul, sub_mul, mul_sub ] ;
  replace this := congr_arg ( · * ρ.yy 1 ) this ; simp_all +decide [ mul_assoc, add_mul, mul_add ];
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