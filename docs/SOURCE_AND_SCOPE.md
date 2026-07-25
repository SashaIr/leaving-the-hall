# Source correspondence and formalization scope

The accompanying [`main.tex`](../main.tex) is the mathematical source.  This
page records exactly which source claims are represented by Lean declarations.

## Dyck path algebra

`RequestProject/Aqt/Algebra.lean` gives a level-graded generators-and-relations
presentation named `Aqt`.  It includes explicit vertices and path support,
level-indexed generators, all unstarred and starred `(R1)`--`(R6)`, and the
three gluing relations.  Its `y_i` and normalized `z_i/(qt)` are recursive words,
not generators.  See [`AQT_FILES.md`](AQT_FILES.md) for encoding and
specialization differences from the paper.

## What the Theta development proves

`Theta.lean` does not operate directly on `Aqt`.  `ThetaData` is a one-level
calculation interface in an arbitrary ring.  It now contains local assumptions
for all six unstarred and all six starred `R` relations, and defines `yy` and
`zz` recursively from `T`, `Tinv`, `dp`, `dm`, and `dps`.  The gluing and
commutation facts needed by the calculations remain structure fields.  The
structure suppresses path typing and level changes, so it is not equivalent to
the quotient presentation in `Algebra.lean`.

`DyckRepU` additionally assumes the two-sided inverses that would exist in the
relevant completion.  Within that interface Lean proves the displayed finite
identities for `Θ(d₊)`, `Θ(d₊*)`, local `(R2)`, local `(R2*)`, `(Q2)`, and the
product formulas of `cor:theta_yz`.

`ThetaDescent.lean` proves the universal statement that **any** assignment on
the genuine generators preserving every constructor of `Rel` descends to an
algebra homomorphism from `Aqt`.  The preservation proof is a hypothesis.  The
project therefore does not yet connect the fixed-level calculations to a
constructed endomorphism of the completed, full level-graded `Aqt`.

## Symmetric functions and kernel preservation

`AqtAction` is the correct abstract type of an action of the full quotient, but
no concrete symmetric-function/Laurent-polynomial carrier or plethystic action
is constructed.  `PreserveKernel.lean` proves conditional ring identities from
explicit annihilator and level-specific hypotheses; it does not prove kernel
preservation for a concrete action instance.

`DGamma.lean` proves abstract word-intertwining and conjugation facts and the
explicit inverse-form relations with the level-zero words `e₁` and `D₁`.  Its
word `D⁺ = d₋(1+uy₁)⁻¹(-y₁)d₊*` represents the full positive `D` series, and
the proved relations are `Θ(D₁)=D⁺` and `Θ(e₁)=e₁+D⁺-D₁`, together with their
intertwiner forms.  Turning these inverse identities into coefficientwise
formal-series sums still requires a formal completion.  The file does not
identify its abstract conjugating operator with the paper's symmetric-function
series, nor formalize the shuffle-indexed coefficient formula.

## The `Ψ` bijection

The modules in `RequestProject/Psi/` formalize the unlabelled decorated-path
bijection used in the `q = 1` combinatorics.  Decorations are determined by the
underlying path.  Lean stores an area vector `av`, while the paper writes the
absolute vector `τ`; `tauOf` converts between them.  The formal development
proves both inverse identities, well-definedness, area preservation,
rise-composition preservation, and the final set-level bijection.

## Concise status

Machine-checked here:

* the full presented quotient `Aqt`;
* abstract actions as homomorphisms out of that quotient;
* fixed-level finite Theta identities under the documented assumptions;
* the universal quotient-descent mechanism;
* conditional kernel and abstract conjugation consequences;
* the complete unlabelled `Ψ` bijection development.

Not constructed here:

* the paper's concrete symmetric-function representation;
* a formal power-series/completed `Aqt`;
* a proof that the particular paper Theta assignment preserves every relation
  of the genuine level-graded quotient;
* the identification with classical symmetric-function Theta operators and the
  shuffle coefficient expansions.
