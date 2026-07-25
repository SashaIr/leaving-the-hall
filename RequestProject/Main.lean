import RequestProject.Aqt.Algebra
import RequestProject.Aqt.Rep
import RequestProject.Aqt.ThetaDescent
import RequestProject.Aqt.PreserveKernel
import RequestProject.Aqt.DGamma

/-!
# The Dyck path algebra, its action, and `Θ`

The development now uses one convention consistently, namely the convention in
`main.tex`:

`w=(1+uy₁)⁻¹`, `s=uwy₁z₁`, `s*=u(1-z₁)y₁`,
`Θ(d₊)=(1-s)d₊`, and `Θ(d₊*)=(1+s*)⁻¹d₊*`.

The modules provide:

* `Algebra`: the generators-and-relations quotient `Aqt`;
* `Rep`: representations and the induced action homomorphism;
* `Theta`: the source identities and homomorphism lemmas in one module;
* `ThetaDescent`: descent through the same full quotient defined by `Algebra`;
* `PreserveKernel`: preservation of the action's `(I1)` and `(I2)` relations.
-/

namespace DyckAlgebra

/-- The presented Dyck path algebra. -/
example (𝕜 : Type*) [Field 𝕜] (q cQ2 : 𝕜) : Type _ := Aqt q cQ2

/-- An action is an algebra homomorphism from the full level-graded quotient. -/
example {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t) :
    Aqt q t →ₐ[𝕜] Module.End 𝕜 ρ.carrier := ρ.act

/-- A relation-preserving `Θ` assignment descends through that same quotient. -/
example {𝕜 C : Type*} [Field 𝕜] [Ring C] [Algebra 𝕜 C] {q t : 𝕜}
    (f : Gen → C)
    (hf : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b → thetaPre f a = thetaPre f b) :
    Aqt q t →ₐ[𝕜] C := thetaDescent f hf

/-- `Θ` preserves `(Q2)`. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) :
    ρ.Θz1 * ρ.Θdp = cQ2 • (ρ.Θy1 * ρ.Θdps) := ρ.theta_Q2

/-- The two product formulas of `cor:theta_yz`. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) :
    ρ.Θz1 * ρ.Θdp = ρ.w 1 * ρ.zz 1 * ρ.dp ∧
      ρ.Θy1 * ρ.Θdps = ρ.w 1 * ρ.yy 1 * ρ.dps :=
  ⟨ρ.theta_z1_dp, ρ.theta_y1_dps⟩

/-- The explicit inverse-form commutation relation with `D₁`. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) :
    ρ.thetaDOneWord = ρ.dPositiveSeries :=
  ρ.thetaDOneWord_eq_series

/-- The explicit inverse-form commutation relation with `e₁` at level zero. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
    (hlevel : ρ.level = 0) :
    ρ.thetaE1Word = ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord) :=
  ρ.thetaE1Word_eq hlevel

/-- `s*` annihilates `(d₊*)^k ε₀` for `k ≥ 1`. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
    (k : ℕ) (hk : 1 ≤ k) (e0 : ρ.carrier) (hq : q ≠ 0)
    (hI2 : ρ.yy 1 * ρ.dps ^ k * e0 =
      (-(q ^ k)⁻¹) • (ρ.dp * ρ.dps ^ (k - 1) * e0))
    (hQ2 : ρ.zz 1 * (ρ.dp * ρ.dps ^ (k - 1) * e0) =
      (-(q ^ k)) • (ρ.yy 1 * ρ.dps ^ k * e0)) :
    ρ.sStarElt * ρ.dps ^ k * e0 = 0 :=
  ρ.sStar_acts_as_0 k hk e0 hq hI2 hQ2

/-- `Θ` preserves `(I1)` at every level. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) (k : ℕ)
    (e0 : ρ.carrier)
    (hs : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI1 : (ρ.dm * ρ.dps - 1) * ρ.dps ^ k * e0 = 0) :
    (ρ.dm * ρ.Θdps - 1) * ρ.Θdps ^ k * e0 = 0 :=
  ρ.theta_preserve_I1_via_sStar k e0 hs hI1

/-- `Θ` preserves the corrected level-`k` `(I2)` relation. -/
example {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2) (k : ℕ)
    (e0 : ρ.carrier) (hcQ2 : cQ2 = -(q ^ k))
    (hs : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI2 : (ρ.dp + (q ^ k) • (ρ.yy 1 * ρ.dps)) * ρ.dps ^ k * e0 = 0) :
    (ρ.Θdp + (q ^ k) • (ρ.Θy1 * ρ.Θdps)) * ρ.Θdps ^ k * e0 = 0 :=
  ρ.theta_preserve_I2_qpow_via_sStar k e0 hcQ2 hs hI2

end DyckAlgebra
