import RequestProject.Aqt.PreserveKernel

/-!
# Conjugation and commutation with the `D_γ` operators

This module formalizes the operator-algebra part of the two results following
kernel preservation in `main.tex`.

For a nonempty natural composition `γ = (γ₁, …, γₗ)`, `dGamma` is the paper's
operator

```text
d₋ (-y₁)^(γ₁-1) z₁ (-y₁)^γ₂ z₁ ⋯ (-y₁)^γₗ z₁ d₊.
```

`thetaDGamma` is the same word with each generator replaced by its `Θ`-image.
The theorem `intertwine_dGamma` says that any operator implementing `Θ` on the
four generators also intertwines `D_γ` with its transformed word.  If that
operator has a right inverse, `thetaDGamma_eq_conjugate` gives the conjugation
identity from the source.

The generic theorem `theta_eq_conjugate` records the same argument for an
arbitrary algebra element `L`: the intertwining equation
`U L = Θ(L) U` implies `Θ(L) = U L U⁻¹`.

This is the strongest faithful statement available in the project's abstract
operator model.  Identifying `U` specifically with
`∑ uⁿ Θ_{eₙ}`, and extracting the source's shuffle-indexed coefficient formula,
requires a concrete graded symmetric-function representation and formal power
series, which are outside the present single-generic-level presentation.
-/

namespace DyckAlgebra
namespace DyckRepU

variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

/-- The final repeated block in the definition of `D_γ`. -/
def dGammaTail : List ℕ → ρ.carrier
  | [] => ρ.zz 1 * ρ.dp
  | g :: gs => ρ.zz 1 * (-ρ.yy 1) ^ g * dGammaTail gs

/-- The operator `D_γ` for a nonempty natural composition.  The empty list is
assigned `0`; all mathematical statements below work uniformly with that
convention. -/
def dGamma : List ℕ → ρ.carrier
  | [] => 0
  | g :: gs => ρ.dm * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs

/-- The tail word with every generator replaced by its `Θ`-image. -/
def thetaDGammaTail : List ℕ → ρ.carrier
  | [] => ρ.Θz1 * ρ.Θdp
  | g :: gs => ρ.Θz1 * (-ρ.Θy1) ^ g * thetaDGammaTail gs

/-- The generatorwise `Θ`-image of `D_γ`. -/
def thetaDGamma : List ℕ → ρ.carrier
  | [] => 0
  | g :: gs => ρ.dm * (-ρ.Θy1) ^ (g - 1) * ρ.thetaDGammaTail gs

/-- The level-zero word acting as multiplication by `e₁` in the paper. -/
def e1Word : ρ.carrier := ρ.dm * ρ.dp

/-- The alternative level-zero word for `D₁`.  On the concrete action it is
`d₋ (-y₁) d₊*`. -/
def dOneWord : ρ.carrier := ρ.dm * (-ρ.yy 1) * ρ.dps

/-- Algebraic replacement for the generating series `∑_{n≥1} u^(n-1) Dₙ`:
the inverse `w₁=(1+u y₁)⁻¹` is its geometric-series factor. -/
def dPositiveSeries : ρ.carrier := ρ.dm * ρ.w 1 * (-ρ.yy 1) * ρ.dps

/-- The word obtained by applying `Θ` to `e₁ = d₋d₊`. -/
def thetaE1Word : ρ.carrier := ρ.dm * ρ.Θdp

/-- The word obtained by applying `Θ` to `D₁ = d₋(-y₁)d₊*`. -/
def thetaDOneWord : ρ.carrier := ρ.dm * (-ρ.Θy1) * ρ.Θdps

/-- **Explicit `Θ`--`D₁` commutation relation.**  The transform of `D₁` is
the complete positive `D` generating series.  This is the finite inverse form
of `Θ D₁ = (∑_{n≥1} u^(n-1) Dₙ) Θ` before adjoining an external intertwiner. -/
theorem thetaDOneWord_eq_series : ρ.thetaDOneWord = ρ.dPositiveSeries := by
  unfold thetaDOneWord dPositiveSeries
  calc
    ρ.dm * -ρ.Θy1 * ρ.Θdps = -ρ.dm * (ρ.Θy1 * ρ.Θdps) := by noncomm_ring
    _ = -ρ.dm * (ρ.w 1 * ρ.yy 1 * ρ.dps) := by rw [ρ.theta_y1_dps]
    _ = ρ.dm * ρ.w 1 * -ρ.yy 1 * ρ.dps := by noncomm_ring

/-- **Explicit `Θ`--`e₁` commutation relation at level zero.**  Here `(Q2)`
has coefficient `-1`.  The correction is the positive `D` series with its
`D₁` term removed, matching
`[Θ,e₁] = ∑_{n≥2} u^(n-1) Dₙ · Θ` after introducing the intertwiner. -/
theorem thetaE1Word_eq (hlevel : ρ.level = 0) :
    ρ.thetaE1Word = ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord) := by
  have hc : cQ2 = -1 := by simpa [hlevel] using ρ.Q2scalar
  have hQ : ρ.zz 1 * ρ.dp = -(ρ.yy 1 * ρ.dps) := by
    simpa [hc] using ρ.Q2
  have hw : ρ.w 1 - 1 = -(ρ.u • (ρ.w 1 * ρ.yy 1)) := ρ.w1_sub_one
  unfold thetaE1Word e1Word dPositiveSeries dOneWord Θdp sElt
  rw [sub_mul, one_mul]
  have hs : ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.zz 1) * ρ.dp =
      -(ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps)) := by
    rw [smul_mul_assoc, mul_assoc (ρ.w 1 * ρ.yy 1), hQ]
    simp only [mul_neg, smul_neg, mul_assoc]
  rw [hs]
  have hcorr :
      ρ.dm * ρ.w 1 * (-ρ.yy 1) * ρ.dps - ρ.dm * (-ρ.yy 1) * ρ.dps =
        ρ.dm * (ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps)) := by
    have hmul := congrArg (fun x => ρ.dm * x * (-ρ.yy 1) * ρ.dps) hw
    simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc,
      mul_smul_comm, mul_assoc, one_mul, neg_neg] at hmul ⊢
    rw [neg_sub] at hmul
    rw [sub_eq_add_neg] at hmul
    simpa only [sub_neg_eq_add, neg_add_rev, neg_neg, add_comm] using hmul
  calc
    ρ.dm * (ρ.dp - -(ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps))) =
        ρ.dm * ρ.dp + ρ.dm * (ρ.u • (ρ.w 1 * ρ.yy 1 * ρ.yy 1 * ρ.dps)) := by
          rw [sub_neg_eq_add, mul_add]
    _ = ρ.dm * ρ.dp +
        (ρ.dm * ρ.w 1 * (-ρ.yy 1) * ρ.dps - ρ.dm * (-ρ.yy 1) * ρ.dps) := by rw [hcorr]


/-- Operator-form `Θ`--`D₁` commutation.  If `U` implements `Θ` on the
constituent generators, then
`U D₁ = (positive D series) U`. -/
theorem intertwine_dOne (U : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hps : U * ρ.dps = ρ.Θdps * U) :
    U * ρ.dOneWord = ρ.dPositiveSeries * U := by
  unfold dOneWord
  calc
    U * (ρ.dm * -ρ.yy 1 * ρ.dps) = (U * ρ.dm) * -ρ.yy 1 * ρ.dps := by
      simp only [mul_assoc]
    _ = (ρ.dm * U) * -ρ.yy 1 * ρ.dps := by rw [hm]
    _ = ρ.dm * (U * -ρ.yy 1) * ρ.dps := by simp only [mul_assoc]
    _ = ρ.dm * (-ρ.Θy1 * U) * ρ.dps := by rw [mul_neg, hy, neg_mul]
    _ = ρ.dm * -ρ.Θy1 * (U * ρ.dps) := by simp only [mul_assoc]
    _ = ρ.dm * -ρ.Θy1 * (ρ.Θdps * U) := by rw [hps]
    _ = ρ.thetaDOneWord * U := by simp only [thetaDOneWord, mul_assoc]
    _ = ρ.dPositiveSeries * U := by rw [ρ.thetaDOneWord_eq_series]

/-- Operator-form `Θ`--`e₁` commutation at level zero:
`U e₁ = (e₁ + positive-series - D₁) U`. -/
theorem intertwine_e1 (U : ρ.carrier) (hlevel : ρ.level = 0)
    (hm : U * ρ.dm = ρ.dm * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    U * ρ.e1Word =
      (ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord)) * U := by
  unfold e1Word
  calc
    U * (ρ.dm * ρ.dp) = (U * ρ.dm) * ρ.dp := by rw [mul_assoc]
    _ = (ρ.dm * U) * ρ.dp := by rw [hm]
    _ = ρ.dm * (U * ρ.dp) := by rw [mul_assoc]
    _ = ρ.dm * (ρ.Θdp * U) := by rw [hp]
    _ = ρ.thetaE1Word * U := by simp only [thetaE1Word, mul_assoc]
    _ = (ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord)) * U := by
      rw [ρ.thetaE1Word_eq hlevel]

/-- Intertwining is preserved by natural powers. -/
lemma intertwine_pow {U x tx : ρ.carrier} (h : U * x = tx * U) :
    ∀ n : ℕ, U * x ^ n = tx ^ n * U := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]

/-- Intertwining for the repeated tail of a `D_γ` word. -/
lemma intertwine_dGammaTail (U : ρ.carrier)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    ∀ gs : List ℕ, U * ρ.dGammaTail gs = ρ.thetaDGammaTail gs * U := by
  intro gs
  induction gs with
  | nil =>
    simp [dGammaTail, thetaDGammaTail]
    calc U * (ρ.zz 1 * ρ.dp) = (U * ρ.zz 1) * ρ.dp := by rw [mul_assoc]
      _ = (ρ.Θz1 * U) * ρ.dp := by rw [hz]
      _ = ρ.Θz1 * (U * ρ.dp) := by rw [mul_assoc]
      _ = ρ.Θz1 * (ρ.Θdp * U) := by rw [hp]
      _ = ρ.Θz1 * ρ.Θdp * U := by rw [mul_assoc]
  | cons g gs ih =>
    simp [dGammaTail, thetaDGammaTail]
    -- First establish that U intertwines -ρ.yy 1 with -ρ.Θy1
    have hy_neg : U * (-ρ.yy 1) = (-ρ.Θy1) * U := by
      calc U * (-ρ.yy 1) = -(U * ρ.yy 1) := by rw [mul_neg]
        _ = -(ρ.Θy1 * U) := by rw [hy]
        _ = (-ρ.Θy1) * U := by rw [neg_mul]
    -- Get the power version
    have hy_pow : U * (-ρ.yy 1) ^ g = (-ρ.Θy1) ^ g * U := intertwine_pow ρ hy_neg g
    -- Now rewrite step by step
    rw [mul_assoc (ρ.zz 1) ((-ρ.yy 1) ^ g) (ρ.dGammaTail gs)]
    rw [← mul_assoc U (ρ.zz 1) ((-ρ.yy 1) ^ g * ρ.dGammaTail gs)]
    rw [hz]
    rw [mul_assoc ρ.Θz1 U]
    rw [← mul_assoc U]
    rw [hy_pow]
    rw [mul_assoc ((-ρ.Θy1) ^ g) U]
    rw [ih]
    rw [← mul_assoc ((-ρ.Θy1) ^ g) (ρ.thetaDGammaTail gs) U]
    simp only [mul_assoc]

/-- The one-block assembly step for intertwining a `D_γ` word. -/
lemma intertwine_dGamma_cons (U : ρ.carrier) (g : ℕ) (gs : List ℕ)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    U * ρ.dGamma (g :: gs) = ρ.thetaDGamma (g :: gs) * U := by
  have hneg : U * (-ρ.yy 1) = (-ρ.Θy1) * U := by
    calc
      U * (-ρ.yy 1) = -(U * ρ.yy 1) := by rw [mul_neg]
      _ = -(ρ.Θy1 * U) := by rw [hy]
      _ = (-ρ.Θy1) * U := by rw [neg_mul]
  have hpow := ρ.intertwine_pow hneg (g - 1)
  have htail := ρ.intertwine_dGammaTail U hy hz hp gs
  simp only [dGamma, thetaDGamma]
  calc
    U * (ρ.dm * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs) =
        (U * ρ.dm) * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs := by
          simp only [mul_assoc]
    _ = (ρ.dm * U) * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs := by rw [hm]
    _ = ρ.dm * (U * (-ρ.yy 1) ^ (g - 1)) * ρ.dGammaTail gs := by
          simp only [mul_assoc]
    _ = ρ.dm * ((-ρ.Θy1) ^ (g - 1) * U) * ρ.dGammaTail gs := by rw [hpow]
    _ = ρ.dm * (-ρ.Θy1) ^ (g - 1) * (U * ρ.dGammaTail gs) := by
          simp only [mul_assoc]
    _ = ρ.dm * (-ρ.Θy1) ^ (g - 1) * (ρ.thetaDGammaTail gs * U) := by rw [htail]
    _ = ρ.dm * (-ρ.Θy1) ^ (g - 1) * ρ.thetaDGammaTail gs * U := by
          simp only [mul_assoc]

/-- **Commutation of `Θ` with `D_γ`.**  An operator which intertwines each
constituent generator with its `Θ`-image intertwines the complete `D_γ` word. -/
theorem intertwine_dGamma (U : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    ∀ γ : List ℕ, U * ρ.dGamma γ = ρ.thetaDGamma γ * U := by
  intro γ
  cases γ with
  | nil => simp [dGamma, thetaDGamma]
  | cons g gs => exact ρ.intertwine_dGamma_cons U g gs hm hy hz hp

/-- The abstract conjugation argument used in
`Θ(L) = Θ(u) L Θ(u)⁻¹`.  No left-inverse hypothesis is needed. -/
theorem theta_eq_conjugate {L thetaL U Uinv : ρ.carrier}
    (hintertwine : U * L = thetaL * U) (hright : U * Uinv = 1) :
    thetaL = U * L * Uinv := by
  calc thetaL = thetaL * 1 := by rw [mul_one]
    _ = thetaL * (U * Uinv) := by rw [hright]
    _ = thetaL * U * Uinv := by rw [mul_assoc]
    _ = U * L * Uinv := by rw [← hintertwine]

/-- The transformed `D_γ` word is conjugate to `D_γ` by any invertible operator
implementing `Θ` on its generators. -/
theorem thetaDGamma_eq_conjugate (γ : List ℕ) (U Uinv : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U)
    (hright : U * Uinv = 1) :
    ρ.thetaDGamma γ = U * ρ.dGamma γ * Uinv := by
  apply ρ.theta_eq_conjugate
  · exact ρ.intertwine_dGamma U hm hy hz hp γ
  · exact hright

end DyckRepU
end DyckAlgebra
