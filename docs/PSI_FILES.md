# `Ψ` combinatorial development: file guide

`RequestProject/Psi.lean` is an umbrella module.  It imports the final module
below, which transitively imports the complete development while preserving the
original public import path.  All declarations use namespace `Psi`.

## `Psi/Defs.lean`

Defines Boolean path encodings, the Dyck predicate, reconstruction `phiPath`,
path statistics, descent compositions, staircase vectors, `tauOf`, and
`IsValid`.

## `Psi/PathLemmas.lean`

Proves generic list, height, validity, splitting, valley-counting, and basic
construction lemmas used throughout the development.

## `Psi/PhiBasic.lean`

Establishes the first fundamental properties of reconstruction `Φ = phiPath`:
`phi_isDyck`, `phi_size`, `phi_numValleys`, and `phi_numRises`.

## `Psi/Area.lean`

Develops the integer height/area accumulator, no-double-East (`hasDD`)
machinery, descent-staircase theory, and validity/splitting lemmas.  It
culminates in

```lean
phi_area : area (phiPath w av) = av.sum
```

for valid data.

## `Psi/RiseComp.lean`

Develops contraction, North-run, and `muVec` identities and proves
`phi_riseComp`, the preservation of rise composition.

## `Psi/Forward.lean`

Defines the domains `Dom` and `Cod`, the forward map `psiPath`, and its
computational decomposition lemmas.  It proves `psi_phi`: applying `Ψ` after
`Φ` returns valid source data.

## `Psi/Inverse.lean`

Analyzes run structure and the leading `(UD)^a` decomposition of Dyck paths.
It proves `phi_psi`: reconstruction after the forward map returns the original
nonempty Dyck path.

## `Psi/Bijection.lean`

Proves well-definedness of `Ψ`, including validity of the produced pair, and
finishes with `psi_mapsTo` and

```lean
phi_bijOn : Set.BijOn (fun x => phiPath x.1 x.2) (Dom n) (Cod n).
```

For the mathematical encoding and a worked example, see
[`PSI_BIJECTION.md`](PSI_BIJECTION.md).
