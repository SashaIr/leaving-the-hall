# Guide to the `RequestProject.Psi` development

The modules under `RequestProject/Psi/`, re-exported by `Psi.lean`, formalize the combinatorial bijection in the part of
[`main.tex`](../main.tex) beginning with Definition `def:psi`.  The bijection relates
unlabelled decorated Dyck paths to binary words together with paths above a
staircase.  It also preserves the two statistics needed in the paper: area and
rise composition.

The development is self-contained apart from Mathlib.  It does not depend on the
algebraic implementation of `A_qt` or `Theta` in the other Lean modules.

## 1. The mathematical statement

For nonnegative integers `k` and `l`, the paper considers a bijection

```text
Ψ : DP(k+l+1)^{*k,•l}
      ↔ {(w, τ) | w ∈ W(0^l,1^k), τ ∈ R(Des(0w))}.
```

In the unlabelled setting used here, every North step except the first is
implicitly decorated:

- a North step preceded by North is a decorated **rise** (`*`);
- a North step preceded by East is a decorated **valley** (`•`).

Consequently, the underlying Dyck path alone determines all decorations.  A
path with `k` rises and `l` valleys has size `k + l + 1`.

The desired statistic identities are

```text
area(π)       = area(τ),
μ(c(π))       = μ(τ),
```

where `c(π)` contracts the East step immediately before each valley and `μ` is
rise composition.

## 2. The principal encoding choice

A lattice path is represented by `List Bool`:

```text
true  = U = North,
false = D = East.
```

The paper returns the absolute height vector `τ`.  Lean instead stores its
**area vector**

```text
av = τ - δ(Des(0w)).
```

The absolute vector is recovered by

```lean
tauOf w av = deltaOf (desComp (false :: w)) + av
```

with pointwise list addition.  This choice makes area preservation become the
simple formula

```lean
area (phiPath w av) = av.sum
```

in `phi_area`.

Thus the Lean pair `(w, av)` corresponds to the paper's pair `(w, τ)`, not to a
pair `(w, τ)` literally.  This distinction is important when reading
`psiPath`, `phiPath`, and `IsValid`.

## 3. Basic objects and statistics

### Dyck paths

`IsDyckAux p h` scans a Boolean path while maintaining its height above the
main diagonal.  A North step raises the height and an East step requires a
strictly positive current height before lowering it.  The path must finish at
height zero.  The public predicate is

```lean
def IsDyck (p : List Bool) : Prop := IsDyckAux p 0
```

`numN` and the later helper `numE` count North and East steps.

The section beginning with `runHeight` introduces an equivalent, more
compositional interface:

- `runHeight p h` is the final height after traversing `p` from `h`;
- `validFrom p h` says no prefix goes below zero;
- `isDyckAux_iff` connects these notions to `IsDyckAux`.

Most proofs about concatenated pieces use this interface rather than unfolding
`IsDyckAux` directly.

### Path statistics

The definitions `countValleys` and `countRises` remember the preceding step and
count the two possible decorations.  Their public wrappers are `numValleys`
and `numRises`.

`areaAux` scans the path while tracking the numbers of North and East steps
already seen.  Only the first North step and valley North steps contribute to
the decorated area.  The later integer-valued `areaH` is an auxiliary version
that behaves better under concatenation and height shifts.

`cc` implements the contraction `c(π)`: an East step immediately followed by a
North step is deleted.  `northRuns` then returns the lengths of maximal North
runs.  Therefore the Lean expression for the left-hand rise composition is

```lean
northRuns (cc π).
```

### Word-side statistics

- `desComp` cuts a binary word after every descent `10`.
- `deltaOf` takes partial sums of a composition and represents the staircase
  `δ`.
- `muVec` records the positive successive differences of a height vector.  It
  is the word-side version of rise composition.
- `tauOf w av` reconstructs `τ` from the stored area vector.

A datum is accepted by

```lean
def IsValid (w : List Bool) (av : List ℕ) : Prop :=
  av.length = (desComp (false :: w)).length ∧
  (tauOf w av).IsChain (· ≤ ·) ∧
  (tauOf w av).getLast? = some (w.length + 1)
```

These three conditions say that `τ` has the expected number of columns, is
weakly increasing, and ends at the total size.  This is the concrete Lean
encoding of `τ ∈ R(Des(0w))`.

## 4. Why the file defines `Φ` before `Ψ`

The paper first presents

```text
Ψ : decorated Dyck path → (word, height vector).
```

The Lean file starts instead with an explicit inverse

```text
Φ = phiPath : (word, area vector) → decorated Dyck path.
```

This direction is convenient for proofs: the first descent of the word gives a
canonical recursive decomposition, and the head of `av` says exactly where to
split the smaller path.

The helper operations are:

- `noDescent w`: whether `w` contains no adjacent `10`;
- `cLead0 w` and `cLead1 w`: lengths of leading zero and one blocks;
- `splitAtRow p h`: split `p` immediately after its `h`-th North step, also
  absorbing an immediately following East step.

If `w` has no descent, then `w = 0^l 1^k` and `phiPath` returns the base path

```text
(UD)^l U^(k+1) D^(k+1).
```

Otherwise the canonical decomposition is

```text
w = 0^a 1^b 0 w'.
```

Writing `h` for the first entry of `av`, Lean recursively constructs
`π' = phiPath w' av'`, splits it as `π' = ρρ'` at row `h`, and returns

```text
(UD)^a U ρ U^b D^(b+1) ρ'.
```

This is exactly the inverse construction in the proof of the main theorem in
`main.tex`.

## 5. Properties proved about `Φ`

The first group of headline results establishes that reconstruction has the
right shape:

- `phi_isDyck`: `phiPath w av` is a Dyck path;
- `phi_size`: its length is `2 * (w.length + 1)`;
- `phi_numValleys`: its number of valleys is the number of zeroes in `w`;
- `phi_numRises`: its number of rises is the number of ones in `w`.

Notably, `phi_isDyck` holds even for raw, invalid data.  Validity becomes
necessary for the statistic arguments because it controls where the recursive
split may occur.

### Area preservation

The proof of `phi_area` follows the recursive construction.  Its main pieces
are:

1. `areaH_append` and `areaH_shift`, which make area calculations over
   concatenated paths manageable;
2. `hasDD`, which detects two consecutive East steps;
3. `phi_split_noDD`, which proves that the prefix `ρ` selected at the valid row
   has no `DD`;
4. descent-composition lemmas such as `desComp_descent` and `tauOf_descent`,
   which describe how `τ` changes when `0^a 1^b 0` is prepended;
5. validity lemmas `isValid_tail`, `isValid_head_le`, and
   `tau_headD_le_numN`, which justify the recursive call and split bound;
6. `area_reconstruct`, which computes the area added by one reconstruction
   step.

The resulting theorem is

```lean
theorem phi_area (w) (av) (h : IsValid w av) :
  area (phiPath w av) = av.sum
```

and is the formal counterpart of `lem:area`.

### Rise-composition preservation

The theorem `phi_riseComp` proves

```lean
northRuns (cc (phiPath w av)) = muVec (tauOf w av)
```

for valid data.  This fills in the argument marked `TODO` in `main.tex`.

On the word side, `muVec_tauOf_descent` describes the effect of a recursive
word block on `μ(τ)`.  On the path side, `cc_noDD_append_gen`,
`northRunsAux_split`, `riseComp_split`, and `riseComp_recon` describe contraction
and North runs across the same reconstruction.  The key fact is that the first
new North run has length

```text
a + 1 + h + b,
```

matching the first positive increment of the reconstructed height vector; the
remaining runs agree by induction.

## 6. The actual forward map `Ψ`

`psiPath` is the computable implementation of the paper's `Ψ`:

```lean
def psiPath (π : List Bool) : List Bool × List ℕ
```

Again, its second output is `av`, not the absolute vector `τ`.

One recursive iteration does the following.

1. `cUDraw` greedily counts leading `UD` pairs.  `cUD` reduces this count by one
   when the whole path is a string of `UD` pairs, ensuring that the remaining
   Dyck path is nonempty.  This determines `a`.
2. Remove `(UD)^a U`, leaving `rest`.
3. `firstDDidx rest` locates the first `DD`.  This identifies the distinguished
   block `U^b D^(b+1)` from the paper.
4. The North run immediately before that `DD` and the East run beginning there
   determine the maximal possible `b`.
5. Remove that block and write the remaining path as `ρ ++ ρ'`.
6. If the remainder is nonempty, recursively compute `(w', av')` and return

   ```text
   (0^a 1^b 0 w', numN(ρ) :: av').
   ```

   Here `numN ρ` is the area-vector entry `h` used by `phiPath`.
7. If the remainder is empty, return the base datum `(0^a 1^b, [0])` (or
   `(0^a, [0])` in the no-`DD` branch).

The recursion terminates because every non-base step removes at least the
initial `U` and the distinguished East step; `take_drop_len_le` supplies the
list-length estimate used by Lean's termination checker.

The numerous lemmas following `psiPath` show that this executable search really
recovers the canonical parameters.  In particular:

- `psiPath_base` evaluates it on `(UD)^a U^(b+1) D^(b+1)`;
- `psiPath_step` evaluates it on a general reconstructed step;
- `psi_rest_struct` proves that the first-`DD` calculation produces the desired
  `ρ`, `b`, and `ρ'` decomposition;
- `dyck_leading`, `dyck_residual`, and related lemmas show that the recursively
  remaining path is again a Dyck path.

## 7. The two round trips

The central inverse identities are:

```lean
psi_phi : IsValid w av → psiPath (phiPath w av) = (w, av)

phi_psi : IsDyck π → π ≠ [] →
          phiPath (psiPath π).1 (psiPath π).2 = π
```

`psi_phi` proceeds by the recursion defining `phiPath`; validity supplies the
correct split row and proves that the prefix has no `DD`, after which
`psiPath_step` recognizes the construction.

`phi_psi` is harder in the other direction.  It analyzes the first `DD`, proves
that the extracted residual path is Dyck, invokes the induction hypothesis on
that shorter path, and then uses `phiPath_block` to rebuild the original path.

Together, these identities give injectivity and surjectivity with an explicit
inverse, rather than merely a cardinality argument.

## 8. Well-definedness of `Ψ`

A round trip alone does not show that `psiPath π` satisfies `IsValid`, so the
last major section proves this separately.

The auxiliary statistic

```lean
numNBeforeDD π
```

counts North steps before the first pair of consecutive East steps.  The
strengthened induction theorem `psi_valid_head` proves two facts at once:

```text
1. psiPath π is valid;
2. the first coordinate of tauOf (psiPath π) is numNBeforeDD π.
```

The second fact is the invariant needed for the first.  In a recursive
 decomposition `ρ ++ ρ'`, the new area entry is `numN ρ`; the lemma
`numN_le_numNBeforeDD_append` shows it is bounded by the first coordinate of the
recursively produced `τ`.  Then `isValid_cons` proves that prepending
`0^a 1^b 0` and the new area entry preserves validity.

The user-facing consequence is `psi_isValid`.

## 9. Packaging the bijection

The file packages the two sides by size:

```lean
def Dom (n) := {(w, av) | w.length + 1 = n ∧ IsValid w av}
def Cod (n) := {π | IsDyck π ∧ π.length = 2 * n}
```

`phi_mapsTo` and `psi_mapsTo` establish that `Φ` and `Ψ` map these sets into one
another.  The final theorem is

```lean
theorem phi_bijOn (n : ℕ) (hn : 1 ≤ n) :
  Set.BijOn (fun p => phiPath p.1 p.2) (Dom n) (Cod n)
```

with `psiPath` as the inverse.

The formal statement is indexed only by total size `n`, rather than separately
by `k` and `l`.  This is equivalent to the paper's finer indexing because
`phi_numRises` and `phi_numValleys` prove that the numbers of ones and zeroes in
`w` are exactly the numbers of rises and valleys of the corresponding path.

Although the final `Set.BijOn` is stated for `Φ`, the explicit inverse theorems
show equally that `Ψ` is the desired bijection in the direction used by the
paper.

## 10. Recovering the paper's preservation statements for `Ψ`

The main statistic theorems are phrased for `phiPath`, because that direction
supports cleaner induction.  For a nonempty Dyck path `π`, set

```text
(w, av) = psiPath π,
τ       = tauOf w av.
```

Then:

1. `psi_isValid` says `(w, av)` is valid;
2. `phi_psi` rewrites `phiPath w av` to `π`;
3. `phi_area` gives `area π = av.sum`, which is the area between `τ` and its
   staircase `δ(Des(0w))`;
4. `phi_riseComp` gives `northRuns (cc π) = muVec τ`.

This is exactly the area- and rise-composition-preserving property asserted for
`Ψ` in `main.tex`.

## 11. The example from `main.tex`

For the paper's example,

```text
w   = 001110010
τ   = (8, 10, 10)
δ   = (6,  9, 10)
```

so the Lean area vector is

```text
av = τ - δ = (2, 1, 0).
```

Accordingly, `psiPath` returns `(w, [2, 1, 0])`, while
`tauOf w [2, 1, 0]` recovers `[8, 10, 10]`.  The theorem `phi_area` reads the
area as `2 + 1 + 0 = 3`, and `phi_riseComp` identifies both rise compositions
with `[8, 2]`.

## 12. Suggested reading order

The file is large because the paper's geometric statements must be reduced to
precise list manipulations.  A practical reading order is:

1. `IsDyck`, `area`, `numValleys`, `numRises`, `cc`, and `northRuns`;
2. `desComp`, `deltaOf`, `muVec`, `tauOf`, and `IsValid`;
3. `phiPath` and its explanatory docstring;
4. the headline reconstruction theorems `phi_isDyck`, `phi_size`,
   `phi_numValleys`, and `phi_numRises`;
5. `phi_area` and `phi_riseComp`, initially treating their preceding helper
   sections as implementation detail;
6. `psiPath`, `psiPath_base`, and `psiPath_step`;
7. the round trips `psi_phi` and `phi_psi`;
8. `psi_valid_head`, `psi_isValid`, and finally `phi_bijOn`.

All proofs in `Psi.lean` are complete: the module contains no `sorry` or
`admit`.
