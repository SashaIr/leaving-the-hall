# Source correspondence and formalization scope

The accompanying [`main.tex`](../main.tex) is the mathematical source for the
project.  The Lean development covers two portions of it, at different levels
of abstraction.

## Dyck path algebra and `Θ`

The modules in `RequestProject/Aqt/` formalize a generators-and-relations
fragment sufficient for the current `Θ` descent and kernel-preservation
arguments.  The full paper uses an infinite graded path algebra with vertex
idempotents, level-dependent ranges and coefficients, an explicit action on
symmetric functions, and formal power-series completions.  Lean instead uses:

- one generic level;
- an abstract `(Q2)` scalar `cQ2`;
- abstract operator representations (`DyckRep`);
- explicit two-sided inverse data for completion elements.

Thus `DyckRep.lift` rigorously captures any concrete action satisfying the
relations, while the concrete plethystic action on symmetric functions is not
implemented as a datatype.  `thetaDescent` is a homomorphism out of the core
presentation `Aq0`; `(Q2)` compatibility is a separate theorem.  Statements
requiring the omitted graded structure are exposed with the corresponding
facts as hypotheses rather than silently assumed.

## The `Ψ` bijection

The modules in `RequestProject/Psi/` formalize the unlabelled decorated path
bijection used in the `q = 1` combinatorics.  Decorations are determined by the
underlying path: a noninitial North step is a rise or a valley according to its
predecessor.  Lean stores the area vector `av`, while the paper writes the
absolute vector `τ`; `tauOf` converts between these presentations.

The formal result includes both inverse identities, well-definedness, area
preservation, rise-composition preservation, and the final set-level
bijection.

## Outside the present model

Other portions of `main.tex`—including the full concrete symmetric-function
operator theory, the complete graded algebra, and all later applications—need
additional formal infrastructure beyond the current abstract presentation.
This distinction matters when interpreting an operator identity: an abstract
conjugation theorem can be proved for any represented algebra with an
intertwining invertible operator, whereas identifying that operator with the
paper's generating series of classical symmetric-function `Θ` operators
requires a concrete symmetric-function model and its generation results.
