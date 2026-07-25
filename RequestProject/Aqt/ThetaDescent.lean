import RequestProject.Aqt.ThetaHom

/-!
# `Θ` passes to the quotient

We assemble the relation–preservation lemmas into the statement that `Θ` *passes
to the quotient*: it descends to an algebra homomorphism out of a
generators-and-relations presentation.

To make this a clean, self-contained theorem we use the presentation `Aq0` on
the genuine Carlsson–Mellit generators `T i, T i⁻¹, d_+, d_-, d_+^*` subject to
the Hecke relations together with the `d`-intertwining relations `(R2)`, `(R2*)`:

  `{skein, braid, Tcomm, TinvL, TinvR, R2, R2*}`.

This is the free product `A_q ⋆ A_{q⁻¹}` modulo the shared relations, restricted
to the relations that involve only the true generators (the level–range
relations `(R1)`, `(R4)`, `(R5)` and the relations `(R3)`, `(R6)` and the
`z,y`–relations `(Q1)`, `(Q1*)`, `(Q2)` are not part of `Aq0`; the last are the
extra relations cutting out the full `𝒜_{q,t}`, and `Θ`'s compatibility with the
new relation `(Q2)` is recorded separately as an operator identity in
`RequestProject.Aqt.ThetaHom`).

The map `Θ` sends the generators to their images in the `u`-completion
(`DyckRepU`), and the theorem `DyckRepU.thetaDescent` produces the algebra
homomorphism `Aq0 → carrier`.
-/

namespace DyckAlgebra

open scoped BigOperators

/-- Generators of the core Carlsson–Mellit presentation. -/
inductive GenCore where
  | T (i : ℕ)
  | Tinv (i : ℕ)
  | dp
  | dm
  | dps
  deriving DecidableEq

variable (𝕜 : Type*) [Field 𝕜]

/-- The free algebra on the core generators. -/
abbrev PreCore : Type _ := FreeAlgebra 𝕜 GenCore

namespace PreCore
/-- Generator `T i`. -/
def T (i : ℕ) : PreCore 𝕜 := FreeAlgebra.ι 𝕜 (GenCore.T i)
/-- Generator `T i⁻¹`. -/
def Tinv (i : ℕ) : PreCore 𝕜 := FreeAlgebra.ι 𝕜 (GenCore.Tinv i)
/-- Generator `d₊`. -/
def dp : PreCore 𝕜 := FreeAlgebra.ι 𝕜 GenCore.dp
/-- Generator `d₋`. -/
def dm : PreCore 𝕜 := FreeAlgebra.ι 𝕜 GenCore.dm
/-- Generator `d₊^*`. -/
def dps : PreCore 𝕜 := FreeAlgebra.ι 𝕜 GenCore.dps
end PreCore

open PreCore

variable {𝕜}

/-- The defining relations of the core presentation. -/
inductive RelCore (q : 𝕜) : PreCore 𝕜 → PreCore 𝕜 → Prop
  | skein (i : ℕ) : RelCore q ((T 𝕜 i - 1) * (T 𝕜 i + q • 1)) 0
  | braid (i : ℕ) : RelCore q (T 𝕜 i * T 𝕜 (i+1) * T 𝕜 i) (T 𝕜 (i+1) * T 𝕜 i * T 𝕜 (i+1))
  | Tcomm (i j : ℕ) (h : i + 1 < j) : RelCore q (T 𝕜 i * T 𝕜 j) (T 𝕜 j * T 𝕜 i)
  | TinvL (i : ℕ) : RelCore q (T 𝕜 i * Tinv 𝕜 i) 1
  | TinvR (i : ℕ) : RelCore q (Tinv 𝕜 i * T 𝕜 i) 1
  | R2 (i : ℕ) (h : 1 ≤ i) : RelCore q (dp 𝕜 * T 𝕜 i) (T 𝕜 (i+1) * dp 𝕜)
  | R2s (i : ℕ) (h : 1 ≤ i) : RelCore q (dps 𝕜 * Tinv 𝕜 i) (Tinv 𝕜 (i+1) * dps 𝕜)

/-- The core Dyck path algebra presentation. -/
abbrev Aq0 (q : 𝕜) : Type _ := RingQuot (RelCore q)

namespace DyckRepU

variable {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

/-- The `Θ`-image of a core generator inside the completion `ρ`. -/
def thetaGen : GenCore → ρ.carrier
  | GenCore.T i => ρ.T i
  | GenCore.Tinv i => ρ.Tinv i
  | GenCore.dp => ρ.Θdp
  | GenCore.dm => ρ.dm
  | GenCore.dps => ρ.Θdps

/-- The free-algebra lift of the `Θ`-image map. -/
def thetaPre : PreCore 𝕜 →ₐ[𝕜] ρ.carrier := FreeAlgebra.lift 𝕜 ρ.thetaGen

@[simp] lemma thetaPre_T (i : ℕ) : ρ.thetaPre (PreCore.T 𝕜 i) = ρ.T i := by
  simp only [thetaPre, PreCore.T, thetaGen, FreeAlgebra.lift_ι_apply]
@[simp] lemma thetaPre_Tinv (i : ℕ) : ρ.thetaPre (PreCore.Tinv 𝕜 i) = ρ.Tinv i := by
  simp only [thetaPre, PreCore.Tinv, thetaGen, FreeAlgebra.lift_ι_apply]
@[simp] lemma thetaPre_dp : ρ.thetaPre (PreCore.dp 𝕜) = ρ.Θdp := by
  simp only [thetaPre, PreCore.dp, thetaGen, FreeAlgebra.lift_ι_apply]
@[simp] lemma thetaPre_dm : ρ.thetaPre (PreCore.dm 𝕜) = ρ.dm := by
  simp only [thetaPre, PreCore.dm, thetaGen, FreeAlgebra.lift_ι_apply]
@[simp] lemma thetaPre_dps : ρ.thetaPre (PreCore.dps 𝕜) = ρ.Θdps := by
  simp only [thetaPre, PreCore.dps, thetaGen, FreeAlgebra.lift_ι_apply]

/-- **`Θ` passes to the quotient.**  The `Θ`-image map on generators respects the
defining relations of the core presentation. -/
lemma thetaPre_relCore ⦃a b : PreCore 𝕜⦄ (h : RelCore q a b) :
    ρ.thetaPre a = ρ.thetaPre b := by
  induction h with
  | skein i =>
      simp only [map_mul, map_sub, map_add, map_smul, map_one, map_zero, thetaPre_T]
      exact ρ.skein i
  | braid i => simp only [map_mul, thetaPre_T]; exact ρ.braid i
  | Tcomm i j h => simp only [map_mul, thetaPre_T]; exact ρ.Tcomm i j h
  | TinvL i => simp only [map_mul, map_one, thetaPre_T, thetaPre_Tinv]; exact ρ.TinvL i
  | TinvR i => simp only [map_mul, map_one, thetaPre_T, thetaPre_Tinv]; exact ρ.TinvR i
  | R2 i h => simp only [map_mul, thetaPre_T, thetaPre_dp]; exact ρ.theta_R2 i h
  | R2s i h => simp only [map_mul, thetaPre_Tinv, thetaPre_dps]; exact ρ.theta_R2s i h

/-- The algebra homomorphism `Θ : Aq0 → carrier` obtained by passing `Θ` to the
quotient. -/
def thetaDescent : Aq0 q →ₐ[𝕜] ρ.carrier :=
  RingQuot.liftAlgHom 𝕜 ⟨ρ.thetaPre, ρ.thetaPre_relCore⟩

@[simp] lemma thetaDescent_mk (a : PreCore 𝕜) :
    ρ.thetaDescent (RingQuot.mkAlgHom 𝕜 (RelCore q) a) = ρ.thetaPre a := by
  simp only [thetaDescent, RingQuot.liftAlgHom_mkAlgHom_apply]

end DyckRepU

end DyckAlgebra
