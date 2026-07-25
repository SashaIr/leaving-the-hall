# Source correspondence and formalization scope

The accompanying [`main.tex`](../main.tex) is the mathematical source.

## Dyck path algebra and `Θ`

`RequestProject/Aqt/Algebra.lean` now follows the level-graded path-algebra
presentation: vertices are represented by `ε_k`; arrows and loops carry their
levels; and (R1)--(R6) together with (R1*)--(R6*) are all constructors of the
single relation family `Rel`.  The `y_i` and `z_i` words are defined recursively
from the genuine generators rather than added as generators.

`ThetaDescent.lean` uses this same `Rel` and `Aqt`, not a reduced auxiliary
quotient.  Its universal descent theorem takes preservation of every relation
as its hypothesis.  The finite calculations establishing the source formulas
for `Θ(d₊)` and `Θ(d₊*)` are collected in `Theta.lean` and use a local abstract
operator interface (`DyckRepU`).

The concrete plethystic symmetric-function carrier and a concrete formal-power-
series completion remain abstract.  `AqtAction` is nevertheless a genuine
linear representation of the quotient: its `act` field has type
`Aqt q t →ₐ[𝕜] Module.End 𝕜 V`.  The separate `ThetaData`/`DyckRepU` structures
in `Theta.lean` are explicitly local calculation environments, not purported
actions of `Aqt`; their completion inverses are supplied as two-sided inverse
data.

## The `Ψ` bijection

The modules in `RequestProject/Psi/` formalize the unlabelled decorated path
bijection used in the `q = 1` combinatorics. Decorations are determined by the
underlying path. Lean stores the area vector `av`, while the paper writes the
absolute vector `τ`; `tauOf` converts between these presentations.

The formal result includes both inverse identities, well-definedness, area
preservation, rise-composition preservation, and the final set-level bijection.

## Remaining abstraction boundary

Identifying the abstract operator implementing conjugation with the paper's
classical symmetric-function generating series still requires a concrete
symmetric-function model.  The algebra itself and the source of quotient
descent, however, are now the full level-graded presentation described above.
