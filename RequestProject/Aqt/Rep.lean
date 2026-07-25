import RequestProject.Aqt.Algebra

/-!
# Actions of the Dyck path algebra

This module contains only representations of the actual quotient algebra
`Aqt q t` defined in `Algebra.lean`.  An `AqtAction` consists of a graded
vector space (represented here by its total carrier) and an algebra
homomorphism from `Aqt q t` to its algebra of linear endomorphisms.

For the action from the paper, the carrier is

`V = ⨁_k Λ ⊗ 𝕜[y_1^{±1}, …, y_k^{±1}]`,

where `Λ` is the ring of symmetric functions.  The homomorphism sends the
classes of the generators to the operators `T_i`, `d_±`, and `d_+^*`.
Consequently all defining relations hold because the source is already the
quotient by `Rel q t`.

The small, single-level operator interface needed for the finite `Θ`
calculations is deliberately defined in `Theta.lean`, rather than being called
an action of `Aqt`.
-/

namespace DyckAlgebra

universe v

/-- A linear action of the genuine level-graded quotient `Aqt q t`.

The field `act` is the representation homomorphism
`Aqt q t → End_𝕜(V)`.  Thus this structure cannot be instantiated merely by
listing unrelated operators and relations: its action must factor through the
actual quotient from `Algebra.lean`. -/
structure AqtAction (𝕜 : Type*) [Field 𝕜] (q t : 𝕜) where
  /-- The total carrier of the graded representation. -/
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module 𝕜 carrier]
  /-- The algebra homomorphism defining the action. -/
  act : Aqt q t →ₐ[𝕜] Module.End 𝕜 carrier

attribute [instance] AqtAction.addCommGroup AqtAction.module

namespace AqtAction

variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t)

/-- Apply an algebra element to a vector in the representation. -/
def apply (a : Aqt q t) (v : ρ.carrier) : ρ.carrier := ρ.act a v

@[simp] theorem apply_add (a b : Aqt q t) (v : ρ.carrier) :
    ρ.apply (a + b) v = ρ.apply a v + ρ.apply b v := by
  simp [apply]

@[simp] theorem apply_mul (a b : Aqt q t) (v : ρ.carrier) :
    ρ.apply (a * b) v = ρ.apply a (ρ.apply b v) := by
  simp [apply]

@[simp] theorem apply_one (v : ρ.carrier) : ρ.apply 1 v = v := by
  simp [apply]

end AqtAction

end DyckAlgebra
