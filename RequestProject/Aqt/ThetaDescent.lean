import RequestProject.Aqt.Theta

/-!
# Descending `Θ` through the actual `A_{q,t}` quotient

There is no second algebra in this file.  The source is exactly `Aqt q t` and
the relation family is exactly `Rel q t`, both defined in `Algebra.lean`.

The completed target and the generator images are represented abstractly: this
keeps the quotient argument independent of a particular implementation of
formal power series.  The hypothesis of `thetaDescent` is precisely the theorem
that the proposed generator assignment preserves every constructor of `Rel`,
including (R1)--(R6), their starred versions, and (Q1)--(Q2).
-/

namespace DyckAlgebra

universe v

variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜}
variable {C : Type v} [Ring C] [Algebra 𝕜 C]

/-- Extend a proposed `Θ`-image of the genuine generators to the free algebra. -/
def thetaPre (thetaGen : Gen → C) : Pre 𝕜 →ₐ[𝕜] C :=
  FreeAlgebra.lift 𝕜 thetaGen

@[simp] theorem thetaPre_generator (thetaGen : Gen → C) (g : Gen) :
    thetaPre thetaGen (FreeAlgebra.ι 𝕜 g) = thetaGen g := by
  simp [thetaPre]

/-- **`Θ` passes to the quotient.**  Any assignment on the genuine generators
that preserves the full relation family of `Algebra.lean` induces an algebra
homomorphism from that same `Aqt`; no auxiliary presentation is used. -/
def thetaDescent (thetaGen : Gen → C)
    (preserves : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b →
      thetaPre thetaGen a = thetaPre thetaGen b) :
    Aqt q t →ₐ[𝕜] C :=
  RingQuot.liftAlgHom 𝕜 ⟨thetaPre thetaGen, preserves⟩

@[simp] theorem thetaDescent_mk (thetaGen : Gen → C)
    (preserves : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b →
      thetaPre thetaGen a = thetaPre thetaGen b)
    (a : Pre 𝕜) :
    thetaDescent thetaGen preserves (RingQuot.mkAlgHom 𝕜 (Rel q t) a) =
      thetaPre thetaGen a := by
  simp [thetaDescent]

end DyckAlgebra
