import RequestProject.Aqt.Algebra

/-!
# Representations of the Dyck path algebra and the action on symmetric functions

A *representation* of the Dyck path algebra fragment is an associative
`𝕜`-algebra `C` together with elements playing the roles of the generators and
satisfying the defining relations.

The intended representation is the action on
`V = ⨁_k Λ ⊗ 𝕜[y_1^{±1}, …, y_k^{±1}]` from the paper (Proposition 2.5), where
`Λ` is the ring of symmetric functions; there the generators act as the explicit
operators `T_i, d_±, d_+^*` and multiplication by `y_i`.  Any such action is the
same data as an algebra homomorphism `𝒜_{q,t} → C`, which is the content of
`DyckRep.lift` below.
-/

namespace DyckAlgebra

open Pre

universe v

/-- A representation of the Dyck path algebra fragment: an algebra `carrier`
with elements interpreting the generators and satisfying the defining
relations.  This packages "an action of `𝒜_{q,t}`". -/
structure DyckRep (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) where
  /-- The underlying algebra of operators. -/
  carrier : Type v
  [ring : Ring carrier]
  [algebra : Algebra 𝕜 carrier]
  /-- Image of `T i`. -/
  T : ℕ → carrier
  /-- Image of `T i⁻¹`. -/
  Tinv : ℕ → carrier
  /-- Image of `d₊`. -/
  dp : carrier
  /-- Image of `d₋`. -/
  dm : carrier
  /-- Image of `d₊^*`. -/
  dps : carrier
  /-- Image of `y i` (multiplication by `y_i`). -/
  yy : ℕ → carrier
  /-- Image of `z i`. -/
  zz : ℕ → carrier
  skein : ∀ i, (T i - 1) * (T i + q • 1) = 0
  braid : ∀ i, T i * T (i+1) * T i = T (i+1) * T i * T (i+1)
  Tcomm : ∀ i j, i + 1 < j → T i * T j = T j * T i
  TinvL : ∀ i, T i * Tinv i = 1
  TinvR : ∀ i, Tinv i * T i = 1
  R2 : ∀ i, 1 ≤ i → dp * T i = T (i+1) * dp
  R2s : ∀ i, 1 ≤ i → dps * Tinv i = Tinv (i+1) * dps
  R3 : T 1 * dp * dp = dp * dp
  R3s : Tinv 1 * dps * dps = dps * dps
  R6 : T 1 * (dp * dm - dm * dp) * dp = q • (dp * (dp * dm - dm * dp))
  R6s : Tinv 1 * (dps * dm - dm * dps) * dps = q⁻¹ • (dps * (dps * dm - dm * dps))
  Q1 : ∀ i, zz (i+1) * dp = dp * zz i
  Q1s : ∀ i, yy (i+1) * dps = dps * yy i
  Q2 : zz 1 * dp = cQ2 • (yy 1 * dps)
  yTcomm : ∀ i j, i ≠ j ∧ i ≠ j + 1 → yy i * T j = T j * yy i
  zTcomm : ∀ i j, i ≠ j ∧ i ≠ j + 1 → zz i * T j = T j * zz i
  ydm : ∀ i, yy i * dm = dm * yy i
  zdm : ∀ i, zz i * dm = dm * zz i
  yy_comm : ∀ i j, yy i * yy j = yy j * yy i
  zz_comm : ∀ i j, zz i * zz j = zz j * zz i
  z1y1 : zz 1 * T 1 * yy 1 = yy 2 * zz 1 * T 1
  y1z1 : yy 1 * Tinv 1 * zz 1 = zz 2 * yy 1 * Tinv 1
  T1symYa : T 1 * (yy 1 + yy 2) = (yy 1 + yy 2) * T 1
  T1symYm : T 1 * (yy 1 * yy 2) = (yy 1 * yy 2) * T 1
  T1symZa : T 1 * (zz 1 + zz 2) = (zz 1 + zz 2) * T 1
  T1symZm : T 1 * (zz 1 * zz 2) = (zz 1 * zz 2) * T 1

attribute [instance] DyckRep.ring DyckRep.algebra

namespace DyckRep

variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRep 𝕜 q cQ2)

/-- The interpretation of a generator in a representation. -/
def genMap : Gen → ρ.carrier
  | Gen.T i => ρ.T i
  | Gen.Tinv i => ρ.Tinv i
  | Gen.dp => ρ.dp
  | Gen.dm => ρ.dm
  | Gen.dps => ρ.dps
  | Gen.y i => ρ.yy i
  | Gen.z i => ρ.zz i

/-- The algebra homomorphism `Pre 𝕜 = FreeAlgebra 𝕜 Gen →ₐ carrier`. -/
def preLift : Pre 𝕜 →ₐ[𝕜] ρ.carrier := FreeAlgebra.lift 𝕜 ρ.genMap

@[simp] lemma preLift_T (i : ℕ) : ρ.preLift (Pre.T 𝕜 i) = ρ.T i := by
  simp only [preLift, Pre.T, genMap, FreeAlgebra.lift_ι_apply]
@[simp] lemma preLift_Tinv (i : ℕ) : ρ.preLift (Pre.Tinv 𝕜 i) = ρ.Tinv i := by
  simp only [preLift, Pre.Tinv, genMap, FreeAlgebra.lift_ι_apply]
@[simp] lemma preLift_dp : ρ.preLift (Pre.dp 𝕜) = ρ.dp := by
  simp only [preLift, Pre.dp, genMap, FreeAlgebra.lift_ι_apply]
@[simp] lemma preLift_dm : ρ.preLift (Pre.dm 𝕜) = ρ.dm := by
  simp only [preLift, Pre.dm, genMap, FreeAlgebra.lift_ι_apply]
@[simp] lemma preLift_dps : ρ.preLift (Pre.dps 𝕜) = ρ.dps := by
  simp only [preLift, Pre.dps, genMap, FreeAlgebra.lift_ι_apply]
@[simp] lemma preLift_yy (i : ℕ) : ρ.preLift (Pre.yy 𝕜 i) = ρ.yy i := by
  simp only [preLift, Pre.yy, genMap, FreeAlgebra.lift_ι_apply]
@[simp] lemma preLift_zz (i : ℕ) : ρ.preLift (Pre.zz 𝕜 i) = ρ.zz i := by
  simp only [preLift, Pre.zz, genMap, FreeAlgebra.lift_ι_apply]

/-- `preLift` respects the defining relations. -/
lemma preLift_rel ⦃a b : Pre 𝕜⦄ (h : Rel q cQ2 a b) : ρ.preLift a = ρ.preLift b := by
  induction h with
  | skein i => simp only [map_mul, map_sub, map_add, map_smul, map_one, map_zero, preLift_T]; exact ρ.skein i
  | braid i => simp only [map_mul, preLift_T]; exact ρ.braid i
  | Tcomm i j h => simp only [map_mul, preLift_T]; exact ρ.Tcomm i j h
  | TinvL i => simp only [map_mul, map_one, preLift_T, preLift_Tinv]; exact ρ.TinvL i
  | TinvR i => simp only [map_mul, map_one, preLift_T, preLift_Tinv]; exact ρ.TinvR i
  | R2 i h => simp only [map_mul, preLift_T, preLift_dp]; exact ρ.R2 i h
  | R2s i h => simp only [map_mul, preLift_Tinv, preLift_dps]; exact ρ.R2s i h
  | R3 => simp only [map_mul, preLift_T, preLift_dp]; exact ρ.R3
  | R3s => simp only [map_mul, preLift_Tinv, preLift_dps]; exact ρ.R3s
  | R6 => simp only [map_mul, map_sub, map_smul, preLift_T, preLift_dp, preLift_dm]; exact ρ.R6
  | R6s => simp only [map_mul, map_sub, map_smul, preLift_Tinv, preLift_dps, preLift_dm]; exact ρ.R6s
  | Q1 i => simp only [map_mul, preLift_zz, preLift_dp]; exact ρ.Q1 i
  | Q1s i => simp only [map_mul, preLift_yy, preLift_dps]; exact ρ.Q1s i
  | Q2 => simp only [map_mul, map_smul, preLift_zz, preLift_dp, preLift_yy, preLift_dps]; exact ρ.Q2
  | yTcomm i j h => simp only [map_mul, preLift_yy, preLift_T]; exact ρ.yTcomm i j h
  | zTcomm i j h => simp only [map_mul, preLift_zz, preLift_T]; exact ρ.zTcomm i j h
  | ydm i => simp only [map_mul, preLift_yy, preLift_dm]; exact ρ.ydm i
  | zdm i => simp only [map_mul, preLift_zz, preLift_dm]; exact ρ.zdm i
  | yy_comm i j => simp only [map_mul, preLift_yy]; exact ρ.yy_comm i j
  | zz_comm i j => simp only [map_mul, preLift_zz]; exact ρ.zz_comm i j
  | z1y1 => simp only [map_mul, preLift_zz, preLift_T, preLift_yy]; exact ρ.z1y1
  | y1z1 => simp only [map_mul, preLift_yy, preLift_Tinv, preLift_zz]; exact ρ.y1z1
  | T1symYa => simp only [map_mul, map_add, preLift_T, preLift_yy]; exact ρ.T1symYa
  | T1symYm => simp only [map_mul, preLift_T, preLift_yy]; exact ρ.T1symYm
  | T1symZa => simp only [map_mul, map_add, preLift_T, preLift_zz]; exact ρ.T1symZa
  | T1symZm => simp only [map_mul, preLift_T, preLift_zz]; exact ρ.T1symZm

/-- The algebra homomorphism `𝒜_{q,t} → carrier` corresponding to a
representation: this is "the action of `𝒜_{q,t}`". -/
def lift : Aqt q cQ2 →ₐ[𝕜] ρ.carrier :=
  RingQuot.liftAlgHom 𝕜 ⟨ρ.preLift, ρ.preLift_rel⟩

end DyckRep

end DyckAlgebra
