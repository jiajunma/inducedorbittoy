# InducedOrbitToy/X0Geometry.lean

## Status: NO WORK THIS ROUND

Per `PROGRESS.md` (Round 4 plan), this file is **not assigned** this round:

> `InducedOrbitToy/X0Geometry.lean` — already done (closed in session 4);
> no work.

The harness dispatched a prover anyway; per the "Files NOT assigned this
round" / "non-objective files" instructions, the prover should verify
in-isolation compilation, write a brief no-work report, and **not edit
anything**.

## Verification

### File contents
- Zero `sorry` occurrences (verified by Grep — the only string match is a
  stale docstring sentence on line 28: "All proof obligations are left as
  `sorry` for the prover stage." This is a leftover comment from
  autoformalize and not a live proof obligation. Not modified — proof
  bodies and statements are sorry-free, and PROGRESS.md instructs not to
  edit this file.)
- Theorems present and sorry-free:
  - `ker_le_orthogonal_range`
  - `orthogonal_range_eq_ker`
  - `finrank_quotient_range_eq_finrank_ker`
  - `finrank_Vplus_eq_c`
  - `VplusEquivQuotientRange`
  - `vplusKerPairing`
  - `vplusKerPairing_isPerfPair`
  - `DualTransposeData` (structure)
  - `sDual_restrict_ker_isIso`
  - `x0Geometry`

### LSP diagnostics (`lean_diagnostic_messages`)
Only one item, expected and pre-existing:

```
warning: unused variable `hlambda`
  at line 221, column 36
```

This is the documented unused-variable lint on the
`hlambda : lambda.IsPerfPair` hypothesis of `sDual_restrict_ker_isIso`.
PROGRESS.md (Verified State block, lines 24–27) says verbatim:

> InducedOrbitToy/X0Geometry.lean:221:35: unused variable hlambda —
> pre-existing, do not remove; the hypothesis is part of the
> autoformalised statement of `sDual_restrict_ker_isIso`.

No errors. No new warnings. File compiles in isolation.

### Cross-file impact of Round 4 cascades
This file imports only `InducedOrbitToy.Basic`. Round 4's Tier S #2
(tightening `UnipotentRadical` with a 4th `IsSkewAdjoint` conjunct) and
Tier S #3 (additive Lagrangian fields on `SliceSetup`) **do not affect
any declaration in `X0Geometry.lean`**:

- `UnipotentRadical` is not referenced here.
- `SliceSetup` is not referenced here (only `X0Setup` is used).

So mid-round / end-of-round cascades from Basic.lean cannot break this
file. Confirmed by Grep: no occurrences of `UnipotentRadical`,
`SliceSetup`, `IsSkewAdjoint`, or any of the new field names in
`X0Geometry.lean`.

## Edits made
None. File untouched (per "non-objective files" rules).

## Next steps
None for this file. It is closed and stable.
