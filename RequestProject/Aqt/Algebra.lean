import Mathlib

/-!
# The level-graded Dyck path algebra `A_{q,t}`

This is a generators-and-relations presentation of the path algebra in
Definition 3.1 and Definition 3.9 of the accompanying source.  Levels are part
of the generator data.  Thus `dp k : k ⟶ k+1`, `dm k : k+1 ⟶ k`, and `T k i`
is the loop `T_i` at level `k`.  The idempotents `eps k` record the vertices.

Only `ε_k`, `T_i`, `T_i⁻¹`, `d₊`, `d₋`, and `d₊*` are generators.  In
particular, `y_i` and `z_i` are the recursively defined words `yy` and `zz`
below; they are not generators.  Both copies of (R1)--(R6), including the
previously omitted (R1), (R4), and (R5), occur in `Rel`.
-/

namespace DyckAlgebra

open scoped BigOperators

/-- Generating arrows in the level-graded presentation. -/
inductive Gen where
  | eps (k : ℕ)
  | T (k i : ℕ)
  | Tinv (k i : ℕ)
  | dp (k : ℕ)
  | dm (k : ℕ)
  | dps (k : ℕ)
  deriving DecidableEq

variable (𝕜 : Type*) [Field 𝕜]

abbrev Pre : Type _ := FreeAlgebra 𝕜 Gen

namespace Pre

def eps (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.eps k)
def T (k i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.T k i)
def Tinv (k i : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.Tinv k i)
def dp (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.dp k)
def dm (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.dm k)
def dps (k : ℕ) : Pre 𝕜 := FreeAlgebra.ι 𝕜 (.dps k)

/-- `T_n T_{n-1} ⋯ T_1` at level `k`. -/
def Tdown (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 1
  | n + 1 => T 𝕜 k (n + 1) * Tdown k n

/-- `T_n⁻¹ T_{n-1}⁻¹ ⋯ T_1⁻¹` at level `k`. -/
def TdownStar (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 1
  | n + 1 => Tinv 𝕜 k (n + 1) * TdownStar k n

/-- The loop `[d₊,d₋]` at level `k`. -/
def comm (k : ℕ) : Pre 𝕜 :=
  if k = 0 then -(dm 𝕜 0 * dp 𝕜 0)
  else dp 𝕜 (k - 1) * dm 𝕜 (k - 1) - dm 𝕜 k * dp 𝕜 k

/-- The loop `[d₊*,d₋]` at level `k`. -/
def commStar (k : ℕ) : Pre 𝕜 :=
  if k = 0 then -(dm 𝕜 0 * dps 𝕜 0)
  else dps 𝕜 (k - 1) * dm 𝕜 (k - 1) - dm 𝕜 k * dps 𝕜 k

/-- The derived elements `y_i`; index zero is a harmless totalization outside
of the mathematical range `1 ≤ i ≤ k`. -/
def yy (q : 𝕜) (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 0
  | 1 => (q ^ (k - 1) * (q - 1))⁻¹ • (comm 𝕜 k * Tdown 𝕜 k (k - 1))
  | i + 2 => q • (Tinv 𝕜 k (i + 1) * yy q k (i + 1) * Tinv 𝕜 k (i + 1))

/-- The derived normalized elements `z_i/(qt)` from the starred copy. -/
def zz (q t : 𝕜) (k : ℕ) : ℕ → Pre 𝕜
  | 0 => 0
  | 1 => ((q * t)⁻¹ * (q ^ k * (1 - q)⁻¹)) •
      (commStar 𝕜 k * TdownStar 𝕜 k (k - 1))
  | i + 2 => q⁻¹ • (T 𝕜 k (i + 1) * zz q t k (i + 1) * T 𝕜 k (i + 1))

end Pre

open Pre

variable {𝕜}

/-- Defining relations of the full level-graded `A_{q,t}` presentation. -/
inductive Rel (q t : 𝕜) : Pre 𝕜 → Pre 𝕜 → Prop
  -- vertex/path support
  | eps_idem (k) : Rel q t (eps 𝕜 k * eps 𝕜 k) (eps 𝕜 k)
  | eps_orth (k l) (h : k ≠ l) : Rel q t (eps 𝕜 k * eps 𝕜 l) 0
  | T_support (k i) : Rel q t (eps 𝕜 k * T 𝕜 k i * eps 𝕜 k) (T 𝕜 k i)
  | Tinv_support (k i) : Rel q t (eps 𝕜 k * Tinv 𝕜 k i * eps 𝕜 k) (Tinv 𝕜 k i)
  | dp_support (k) : Rel q t (eps 𝕜 (k+1) * dp 𝕜 k * eps 𝕜 k) (dp 𝕜 k)
  | dm_support (k) : Rel q t (eps 𝕜 k * dm 𝕜 k * eps 𝕜 (k+1)) (dm 𝕜 k)
  | dps_support (k) : Rel q t (eps 𝕜 (k+1) * dps 𝕜 k * eps 𝕜 k) (dps 𝕜 k)
  -- Hecke relations
  | skein (k i) (hi : 1 ≤ i ∧ i < k) :
      Rel q t ((T 𝕜 k i - eps 𝕜 k) * (T 𝕜 k i + q • eps 𝕜 k)) 0
  | braid (k i) (hi : 1 ≤ i ∧ i + 1 < k) :
      Rel q t (T 𝕜 k i * T 𝕜 k (i+1) * T 𝕜 k i)
        (T 𝕜 k (i+1) * T 𝕜 k i * T 𝕜 k (i+1))
  | Tcomm (k i j) (h : 1 ≤ i ∧ i + 1 < j ∧ j < k) :
      Rel q t (T 𝕜 k i * T 𝕜 k j) (T 𝕜 k j * T 𝕜 k i)
  | TinvL (k i) (hi : 1 ≤ i ∧ i < k) : Rel q t (T 𝕜 k i * Tinv 𝕜 k i) (eps 𝕜 k)
  | TinvR (k i) (hi : 1 ≤ i ∧ i < k) : Rel q t (Tinv 𝕜 k i * T 𝕜 k i) (eps 𝕜 k)
  -- A_q: R1--R6
  | R1 (k i) (h : 2 ≤ i ∧ i ≤ k - 2) :
      Rel q t (dm 𝕜 (k-1) * T 𝕜 k i) (T 𝕜 (k-1) i * dm 𝕜 (k-1))
  | R2 (k i) (h : 1 ≤ i ∧ i < k) :
      Rel q t (dp 𝕜 k * T 𝕜 k i) (T 𝕜 (k+1) (i+1) * dp 𝕜 k)
  | R3 (k) : Rel q t (T 𝕜 (k+2) 1 * dp 𝕜 (k+1) * dp 𝕜 k) (dp 𝕜 (k+1) * dp 𝕜 k)
  | R4 (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-2) * dm 𝕜 (k-1) * T 𝕜 k (k-1)) (dm 𝕜 (k-2) * dm 𝕜 (k-1))
  | R5 (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-1) * comm 𝕜 k * T 𝕜 k (k-1))
        (q • (comm 𝕜 (k-1) * dm 𝕜 (k-1)))
  | R6 (k) : Rel q t (T 𝕜 (k+1) 1 * comm 𝕜 (k+1) * dp 𝕜 k)
      (q • (dp 𝕜 k * comm 𝕜 k))
  -- A_{q⁻¹}: starred R1--R6
  | R1s (k i) (h : 2 ≤ i ∧ i ≤ k - 2) :
      Rel q t (dm 𝕜 (k-1) * Tinv 𝕜 k i) (Tinv 𝕜 (k-1) i * dm 𝕜 (k-1))
  | R2s (k i) (h : 1 ≤ i ∧ i < k) :
      Rel q t (dps 𝕜 k * Tinv 𝕜 k i) (Tinv 𝕜 (k+1) (i+1) * dps 𝕜 k)
  | R3s (k) : Rel q t (Tinv 𝕜 (k+2) 1 * dps 𝕜 (k+1) * dps 𝕜 k) (dps 𝕜 (k+1) * dps 𝕜 k)
  | R4s (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-2) * dm 𝕜 (k-1) * Tinv 𝕜 k (k-1)) (dm 𝕜 (k-2) * dm 𝕜 (k-1))
  | R5s (k) (hk : 2 ≤ k) :
      Rel q t (dm 𝕜 (k-1) * commStar 𝕜 k * Tinv 𝕜 k (k-1))
        (q⁻¹ • (commStar 𝕜 (k-1) * dm 𝕜 (k-1)))
  | R6s (k) : Rel q t (Tinv 𝕜 (k+1) 1 * commStar 𝕜 (k+1) * dps 𝕜 k)
      (q⁻¹ • (dps 𝕜 k * commStar 𝕜 k))
  -- gluing relations of A_{q,t}; yy and zz are the derived words above
  | Q1 (k i) (hi : 1 ≤ i ∧ i ≤ k) :
      Rel q t (zz 𝕜 q t (k+1) (i+1) * dp 𝕜 k) (dp 𝕜 k * zz 𝕜 q t k i)
  | Q1s (k i) (hi : 1 ≤ i ∧ i ≤ k) :
      Rel q t (yy 𝕜 q (k+1) (i+1) * dps 𝕜 k) (dps 𝕜 k * yy 𝕜 q k i)
  | Q2 (k) : Rel q t (zz 𝕜 q t (k+1) 1 * dp 𝕜 k)
      ((-(q ^ k)) • (yy 𝕜 q (k+1) 1 * dps 𝕜 k))

/-- The full level-graded Dyck path algebra. -/
abbrev Aqt (q t : 𝕜) : Type _ := RingQuot (Rel q t)

end DyckAlgebra
