# Completed Autoformalize Tasks

## Round 1 (autoformalize)

- `InducedOrbitToy/Basic.lean` — bundled API (`X0Setup`, `SliceSetup`, `PairedSpaces`, predicates, `c`, ambient `V`, ambient form, flag, `IsParabolic`, `UnipotentRadical`). Verified: `lake build` ✅, 0 axioms.

## Round 1.5 (out-of-sequence autoformalize)

- `InducedOrbitToy/X0Geometry.lean` — autoformalize layer for `lem:x0-geometry`.  Seven theorem stubs with `sorry` proofs; the aggregate `theorem x0Geometry` is sorry-free.  Post-review reconciliation removed local duplicates of `IsEpsSymm` / `IsSkewAdjoint`.  Verified by plan agent: `lake build` ✅, 0 axioms.  *Optional bundled-signature refactor scheduled for Round 2 objective 1.*

## Round 2 (autoformalize)

- `InducedOrbitToy/X0Geometry.lean` — bundled signature refactor complete.
- `InducedOrbitToy/Slice.lean` — autoformalized `lem:parametrize-x0-plus-u` and `lem:unipotent-conjugation`.
- `InducedOrbitToy/NormalForm.lean` — autoformalized `prop:p-normal-form` and `prop:kernel-image`.
- `InducedOrbitToy/LocalForms.lean` — autoformalized `lem:local-form-classes`.
- `InducedOrbitToy/Orbits.lean` — autoformalized orbit and multiplicity statements.

## Early Prover Progress

- `InducedOrbitToy/Basic.lean :: c_eq_finrank_quotient` — proved by rank-nullity:
  `Submodule.finrank_quotient_add_finrank`, `LinearMap.finrank_range_add_finrank_ker`, then `omega`.
- `InducedOrbitToy/Orbits.lean :: multiplicityNonDeg` and `multiplicityOddCase` — no longer sorries; both are now direct consequences of the abstract `MultiplicityTheory` package.
- `InducedOrbitToy/X0Geometry.lean :: finrank_quotient_range_eq_finrank_ker` — follows from `c_eq_finrank_quotient`.
- `InducedOrbitToy/X0Geometry.lean :: finrank_Vplus_eq_c` and `VplusEquivQuotientRange` — use `Submodule.quotientEquivOfIsCompl` with `S.isCompl.symm`.
- `InducedOrbitToy/X0Geometry.lean :: ker_le_orthogonal_range` — direct expansion of `mem_orthogonal_iff` and `S.skew`.
- `InducedOrbitToy/X0Geometry.lean :: orthogonal_range_eq_ker` — use `S.epsSymm` to derive `IsRefl`, then `finrank_orthogonal`, rank-nullity, and `Submodule.eq_of_le_of_finrank_eq`.
