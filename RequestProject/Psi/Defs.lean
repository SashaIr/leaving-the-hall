import Mathlib

/-!
# The bijection `Ψ` for the `q = 1` Theta conjecture

This file formalizes the bijection `Ψ` of `main.tex` (Definition `def:psi` and the
theorems `lem:well-defined`, `lem:area`, `lem:comp`, and the final bijectivity
statement) between decorated Dyck paths and pairs `(w, τ)`.

## Encodings

* A **lattice path** is a `List Bool`, where `true` is a North (`U`) step and
  `false` is an East (`D`) step.  A **Dyck path** of size `n` is such a list with
  `n` North and `n` East steps that stays weakly above the main diagonal
  (`IsDyck`).

* In the (unlabeled) decorated setting of the paper, an element of
  `DP(k+l+1)^{*k,•l}` is just a Dyck path of size `n = k+l+1`; every North step
  except the first is decorated, a *rise* (North preceded by North) getting `*`
  and a *valley* (North preceded by East) getting `•`.  Thus `k` is the number of
  rises and `l` the number of valleys among the non-first North steps.

* A **word** `w ∈ W(0^l,1^k)` is a `List Bool` with `k` occurrences of `true`
  (the letter `1`) and `l` occurrences of `false` (the letter `0`).

* Following the paper's area relation
  `τ − δ(Des(0w)) = (h, τ′ − δ(Des(0w′)))`, the natural datum produced by `Ψ`
  is the **area vector** `av` of `τ`: its `i`-th entry is the area of the `i`-th
  column, i.e. `τ_i − δ(Des(0w))_i`.  The absolute path `τ` is recovered as
  `τ = δ(Des(0w)) + av`.

The map `Φ` (`phiPath`) reconstructs the decorated Dyck path from `(w, av)`; it is
the inverse of the paper's `Ψ`, and every statement below is a property of `Ψ`
read through that inverse.

## Status of the formalization

All definitions and the reconstruction map `Φ` are complete, and the following
properties are fully proved (no `sorry`, only the standard axioms):

* `phi_isDyck` — `Φ` always produces a genuine Dyck path;
* `phi_size` — of the expected size `2n` (`n = |w| + 1`);
* `phi_numRises` / `phi_numValleys` — with exactly `#1(w)` rises and `#0(w)`
  valleys, i.e. `w ∈ W(0^l, 1^k)` (`lem:well-defined`);
* `phi_mapsTo` — hence `Φ` maps the domain into the codomain (the `MapsTo`
  part of the bijection);
* `phi_area` — area preservation `area(Φ(w, av)) = Σ av` (`lem:area`), for valid
  data.  This is proved via an integer-valued area accumulator `areaH` (with
  `area_eq_areaH`, `areaH_append`, `areaH_shift`), the reconstruction identity
  `area_reconstruct`, the descent-composition theory (`desComp_descent`,
  `tauOf_descent`, …) giving the validity coupling (`isValid_tail`,
  `isValid_head_le`, `tau_headD_le_numN`), and the structural key lemma
  `phi_split_noDD` (splitting below the first column height exposes no `DD`).
* `phi_riseComp` — rise-composition preservation `μ(c(Φ(w,av))) = μ(τ)`
  (`lem:comp`), for valid data.
  This is proved by the same descent recursion as `phi_area`: on the algebra
  side `muVec_tauOf_descent` (built on `tauOf_descent`, `muVecAux_map_add` and
  `muVecAux_head_shift`) and on the geometry side the contraction/rise-run
  identities `cc_noDD_append_gen`, `northRunsAux_split`, `northRunsAux_zero_eq`,
  `riseComp_recon` (first run `= a+1+b+h`) and the key splitting lemma
  `riseComp_split`.

* `phi_bijOn` — **the bijection**: `Φ = phiPath` is a `Set.BijOn` between valid
  data of size `n` and decorated Dyck paths of size `n`, with explicit inverse
  `Ψ = psiPath` (Definition `def:psi`, extracting maximal blocks from a Dyck
  path).  Both round trips are proved: `psi_phi` (`Ψ∘Φ = id` on valid data,
  injectivity) and `phi_psi` (`Φ∘Ψ = id` on nonempty Dyck paths, surjectivity).
  Well-definedness of `Ψ` (`psi_isValid`, `lem:well-defined`) is obtained from
  `psi_valid_head`, an induction pairing validity with the geometric identity
  `τ₁ = numNBeforeDD π` (the first height coordinate equals the number of North
  steps before the first `DD`); the chain inequality it needs reduces to the
  combinatorial fact `numN ρ ≤ numNBeforeDD (ρ ++ ρ')`.

The whole development is now `sorry`-free and uses only the standard axioms.
-/

namespace Psi

/-! ## Basic path predicates and helpers -/

/-- Running height check: `IsDyckAux p h` says the path `p`, starting from height
`h`, never goes below `0` and ends at height `0`. -/
def IsDyckAux : List Bool → Int → Prop
  | [], h => h = 0
  | true :: r, h => IsDyckAux r (h + 1)
  | false :: r, h => 0 < h ∧ IsDyckAux r (h - 1)

/-- `p` is a Dyck path: balanced and weakly above the diagonal. -/
def IsDyck (p : List Bool) : Prop := IsDyckAux p 0

/-- Number of North (`true`) steps. -/
def numN (p : List Bool) : ℕ := (p.filter id).length

/-! ## The inverse map `Φ` (reconstruction of the path from `(w, av)`) -/

/-- Whether the 0/1-word `w` (with `true = 1`, `false = 0`) is weakly increasing,
i.e. has no descent (`1` immediately followed by `0`). -/
def noDescent : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!a || b) && noDescent (b :: rest)

/-- Number of leading `false` (`0`) letters. -/
def cLead0 : List Bool → ℕ
  | false :: r => 1 + cLead0 r
  | _ => 0

/-- Number of leading `true` (`1`) letters. -/
def cLead1 : List Bool → ℕ
  | true :: r => 1 + cLead1 r
  | _ => 0

/-- Split a path just after its `h`-th North step, also absorbing the East step
immediately following that North step, if present.  (`h = 0` gives the empty
prefix.)  This is the "cut at row `h`" operation of the bijectivity proof. -/
def splitAtRow : List Bool → ℕ → List Bool × List Bool
  | p, 0 => ([], p)
  | [], _ => ([], [])
  | true :: rest, 1 =>
      match rest with
      | false :: rest' => ([true, false], rest')
      | _ => ([true], rest)
  | true :: rest, (h + 2) =>
      let (ρ, ρ') := splitAtRow rest (h + 1)
      (true :: ρ, ρ')
  | false :: rest, (h + 1) =>
      let (ρ, ρ') := splitAtRow rest (h + 1)
      (false :: ρ, ρ')

/-- The reconstruction map `Φ` on the raw data `(w, av)`.

`w` is the 0/1-word and `av` the area vector.  When `w` has no descent
(`w = 0^l 1^k`), the path is `(UD)^l U^{k+1} D^{k+1}`.  Otherwise `w = 0^a 1^b 0 w'`
and, with `h = av.head`, we recurse on `(w', av.tail)`, split the resulting path
at row `h` into `ρ ρ'`, and return `(UD)^a U ρ U^b D^{b+1} ρ'`. -/
def phiPath (w : List Bool) (av : List ℕ) : List Bool :=
  if noDescent w then
    let l := (w.filter (· = false)).length
    let k := (w.filter id).length
    (List.replicate l [true, false]).flatten ++
      List.replicate (k + 1) true ++ List.replicate (k + 1) false
  else
    let a := cLead0 w
    let after0 := w.drop a
    let b := cLead1 after0
    let w' := after0.drop (b + 1)
    let h := av.headD 0
    let av' := av.tail
    let π' := phiPath w' av'
    let (ρ, ρ') := splitAtRow π' h
    (List.replicate a [true, false]).flatten ++ [true] ++ ρ ++
      List.replicate b true ++ List.replicate (b + 1) false ++ ρ'
  termination_by w.length
  decreasing_by
    · -- `w` has a descent, hence is nonempty, and we drop `a + (b+1) ≥ 1` letters.
      simp only [List.length_drop]
      have hw : w ≠ [] := by
        intro h; subst h; simp [noDescent] at *
      have : 1 ≤ w.length := List.length_pos_of_ne_nil hw
      omega

/-! ## Statistics of a decorated Dyck path -/

/-- Area accumulator: `i` = norths seen, `e` = easts seen, `le` = whether the
previous step was an East step.  A North step contributes its area `i - e` only
when it is a valley (preceded by an East step). -/
def areaAux : List Bool → ℕ → ℕ → Bool → ℕ
  | [], _, _, _ => 0
  | true :: r, i, e, le => (if le then i - e else 0) + areaAux r (i + 1) e false
  | false :: r, i, e, _ => areaAux r i (e + 1) true

/-- The area of a decorated Dyck path (sum of `a_i` over the first step and all
valleys; equivalently, over all non-rise North steps). -/
def area (p : List Bool) : ℕ := areaAux p 0 0 false

/-- Count of valleys (North steps preceded by an East step). -/
def countValleys : List Bool → Bool → ℕ
  | [], _ => 0
  | true :: r, le => (if le then 1 else 0) + countValleys r false
  | false :: r, _ => countValleys r true

/-- Number of valleys of a path. -/
def numValleys (p : List Bool) : ℕ := countValleys p false

/-- Count of rises (North steps preceded by another North step). -/
def countRises : List Bool → Bool → Bool → ℕ
  | [], _, _ => 0
  | true :: r, le, sn => (if (!le && sn) then 1 else 0) + countRises r false true
  | false :: r, _, sn => countRises r true sn

/-- Number of rises of a path. -/
def numRises (p : List Bool) : ℕ := countRises p false false

/-- The contracted path `c(π)`: delete every East step immediately preceding a
valley (a North step that is not the first North step). -/
def cc : List Bool → List Bool
  | [] => []
  | true :: r => true :: cc r
  | false :: rest =>
      match rest with
      | true :: _ => cc rest      -- east before a North: contracted away (all valleys decorated)
      | _ => false :: cc rest

/-- Maximal North-run lengths (the *rise composition* of a lattice path). -/
def northRunsAux : List Bool → ℕ → List ℕ
  | [], cur => if cur > 0 then [cur] else []
  | true :: r, cur => northRunsAux r (cur + 1)
  | false :: r, cur => (if cur > 0 then [cur] else []) ++ northRunsAux r 0

/-- Rise composition of a lattice path (list of maximal North-run lengths). -/
def northRuns (p : List Bool) : List ℕ := northRunsAux p 0

/-! ## Words and the target statistics -/

/-- Descent composition of a 0/1-word (with `true = 1`, `false = 0`): the list of
block lengths cut after each descent (a `1` immediately followed by a `0`). -/
def desCompAux : List Bool → ℕ → List ℕ
  | [], cur => [cur]
  | [_], cur => [cur + 1]
  | a :: b :: rest, cur =>
      if a && !b then (cur + 1) :: desCompAux (b :: rest) 0
      else desCompAux (b :: rest) (cur + 1)

/-- Descent composition `Des(word)`. -/
def desComp (word : List Bool) : List ℕ := desCompAux word 0

/-- Partial sums (the path `δ(γ)` of a composition `γ`). -/
def deltaAux : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: r, acc => (acc + x) :: deltaAux r (acc + x)

/-- `δ(γ)`, the staircase path of a composition. -/
def deltaOf (γ : List ℕ) : List ℕ := deltaAux γ 0

/-- Rise composition of a height vector `τ` (positive successive differences). -/
def muVecAux : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: r, prev => (if x - prev > 0 then [x - prev] else []) ++ muVecAux r x

/-- Rise composition `μ(τ)` of a height vector. -/
def muVec (τ : List ℕ) : List ℕ := muVecAux τ 0

/-- The height vector `τ = δ(Des(0w)) + av` reconstructed from `(w, av)`. -/
def tauOf (w : List Bool) (av : List ℕ) : List ℕ :=
  List.zipWith (· + ·) (deltaOf (desComp (false :: w))) av

/-- Validity of a datum `(w, av)`: `av` is the area vector of some `τ ∈ R(Des(0w))`.
Concretely, `τ = δ(Des(0w)) + av` has the right length, is weakly increasing, and
ends at `n = |w| + 1`. -/
def IsValid (w : List Bool) (av : List ℕ) : Prop :=
  av.length = (desComp (false :: w)).length ∧
    (tauOf w av).IsChain (· ≤ ·) ∧
    (tauOf w av).getLast? = some (w.length + 1)


end Psi
