# InducedOrbitToy/Basic.lean

## Status: NO WORK (file already complete)

Per `.archon/PROGRESS.md` (Round 8) under "Files NOT assigned this round":

> `InducedOrbitToy/Basic.lean` — already done; no sorries.

This file is not assigned for Round 8. The prover performed the
prescribed verification-only steps and made no edits.

## Verification

- `grep -n sorry InducedOrbitToy/Basic.lean` → no matches.
- `lake env lean InducedOrbitToy/Basic.lean` → exits cleanly with
  no output (no errors, no warnings).
- File contents byte-for-byte unchanged from the start of Round 8.

## File Inventory (for reference, not edited)

Predicates / structures defined in this file (all sorry-free, frozen):

- `IsEpsSymm`, `IsSkewAdjoint` (Section `Predicates`).
- `IsPerfectPairing`, `IsPaired`, `IsIsotropic` (Section `Pairing`).
- `PairedSpaces` structure (and `attribute [instance]` block).
- `X0Setup` structure (and `attribute [instance]` block).
- `c` definition; `c_eq_finrank_quotient` theorem (proved via
  `Submodule.finrank_quotient_add_finrank` +
  `LinearMap.finrank_range_add_finrank_ker` + `omega`).
- `SliceSetup` structure with `paired`, `L1`, `L0`, `L1'`, `L0'`,
  `isComplL`, `isComplL'`, `L1_paired`, `L0_paired`,
  `L1_isotropic_L0'`, `L0_isotropic_L1'` fields.
- `SliceSetup.E`, `SliceSetup.E'`, `SliceSetup.lambda`, `SliceSetup.V`,
  `SliceSetup.ambientForm`, `SliceSetup.flagE`, `SliceSetup.flagEV0`.
- `IsParabolic` predicate.
- `UnipotentRadical` `Submodule` definition (`carrier`,
  `zero_mem'`, `add_mem'`, `smul_mem'` all proved).

## No edits performed

No declarations were added, removed, or modified. No helper lemmas
were introduced. The file remains the immutable foundation that
downstream files (`X0Geometry.lean`, `LocalForms.lean`, `Slice.lean`,
`NormalForm.lean`, `Orbits.lean`) depend on.

## Round 8 work happens elsewhere

The active Round 8 objectives are in:

- `InducedOrbitToy/NormalForm.lean` (`pNormalForm_witnesses` body).
- `InducedOrbitToy/Orbits.lean` (`sIndependenceAndOrbitCriterion`).
- `InducedOrbitToy/Slice.lean` (`parabolic_decompose`, optional).
