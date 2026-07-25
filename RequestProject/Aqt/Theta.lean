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
  simp +decide [ sStar, mul_sub, sub_mul, hwL ];
  simp +decide [ ← mul_assoc, hwL ];
  rw [ smul_sub, add_sub_assoc ]

end Theta
end DyckAlgebra