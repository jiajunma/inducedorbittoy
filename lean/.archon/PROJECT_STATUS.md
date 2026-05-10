# Project Status

## Overall Progress

- **Scope:** standalone `ClassicalGroup` formalization only.
- **Stage:** complete.
- **Total sorry:** 0 in `ClassicalGroup/*.lean`.
- **Solved:**
  - `ClassicalGroup/NormalForms.lean :: orthogonalAdaptedBasis_exists`
  - `ClassicalGroup/NormalForms.lean :: symplecticAdaptedBasis_exists`
  - `ClassicalGroup/NormalForms.lean :: cstarAdaptedBasis_exists`
  - `ClassicalGroup/NormalForms.lean :: dstarAdaptedBasis_exists`
- **Build state:** `lake build ClassicalGroup` succeeds with only the two pre-existing
  `ClassicalGroup/Lemmas.lean` unnecessary-`simpa` warnings.
- **Current ClassicalGroup sorry locations:** none.

## Completion Note

The standalone `ClassicalGroup` objective for this run is complete. Do not reopen these solved
proofs unless Lean reports a regression.
