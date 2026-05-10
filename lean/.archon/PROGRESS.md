# Project Progress

## Current Stage
complete

## Scope

This Archon run was for the standalone `ClassicalGroup` formalization only.
`InducedOrbitToy/*` objectives were intentionally ignored.

## Objective

Clear every remaining `sorry` in `ClassicalGroup` with verified Lean proofs.

## Final Verification Snapshot

Checked by the main session on 2026-05-10T04:55+08:00:

```bash
rg -n "\\bsorry\\b" ClassicalGroup/*.lean
# no output

lake env lean ClassicalGroup/NormalForms.lean
# exit 0

lake build ClassicalGroup
# Build completed successfully (8035 jobs)
# only two pre-existing ClassicalGroup/Lemmas.lean unnecessary-simpa warnings
```

## Solved Declarations

All former `ClassicalGroup/NormalForms.lean` proof holes are now closed:

- `orthogonalAdaptedBasis_exists`
- `symplecticAdaptedBasis_exists`
- `cstarAdaptedBasis_exists`
- `dstarAdaptedBasis_exists`

Consequent wrappers also compile through closed proofs:

- `symplecticNormalFormIso`
- `cstarNormalFormIso`
- `dstarNormalFormIso`
- `normalForm_Dstar`

## Completion condition

The completion condition for this run is satisfied: `rg -n "sorry" ClassicalGroup/*.lean`
returns no proof `sorry`s, and `lake build ClassicalGroup` succeeds.
