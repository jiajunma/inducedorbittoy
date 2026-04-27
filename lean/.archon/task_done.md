# Completed Tasks

## Round 1 (autoformalize)

- `InducedOrbitToy/Basic.lean` — bundled API (`X0Setup`, `SliceSetup`,
  `PairedSpaces`, predicates, `c`, ambient `V`, ambient form, flag,
  `IsParabolic`, `UnipotentRadical`). `lake build` ✅, 0 axioms.

## Round 1.5 (out-of-sequence autoformalize)

- `InducedOrbitToy/X0Geometry.lean` — autoformalize layer for
  `lem:x0-geometry`. Seven theorem stubs with `sorry` proofs; the
  aggregate `theorem x0Geometry` is sorry-free. Post-review reconciliation
  removed local duplicates of `IsEpsSymm` / `IsSkewAdjoint`. `lake build`
  ✅, 0 axioms.

## Round 2 (autoformalize)

- `InducedOrbitToy/X0Geometry.lean` — bundled signature refactor complete.
- `InducedOrbitToy/Slice.lean` — autoformalized `lem:parametrize-x0-plus-u`
  and `lem:unipotent-conjugation`.
- `InducedOrbitToy/NormalForm.lean` — autoformalized `prop:p-normal-form`
  and `prop:kernel-image`.
- `InducedOrbitToy/LocalForms.lean` — autoformalized `lem:local-form-classes`.
- `InducedOrbitToy/Orbits.lean` — autoformalized orbit and multiplicity
  statements.

## Early Prover Progress

- `InducedOrbitToy/Basic.lean :: c_eq_finrank_quotient` — proved by
  rank-nullity: `Submodule.finrank_quotient_add_finrank`,
  `LinearMap.finrank_range_add_finrank_ker`, then `omega`.
- `InducedOrbitToy/Orbits.lean :: multiplicityNonDeg` and
  `multiplicityOddCase` — direct consequences of the abstract
  `MultiplicityTheory` package.
- `InducedOrbitToy/X0Geometry.lean :: finrank_quotient_range_eq_finrank_ker`
  — follows from `c_eq_finrank_quotient`.
- `InducedOrbitToy/X0Geometry.lean :: finrank_Vplus_eq_c` and
  `VplusEquivQuotientRange` — use `Submodule.quotientEquivOfIsCompl` with
  `S.isCompl.symm`.
- `InducedOrbitToy/X0Geometry.lean :: ker_le_orthogonal_range` — direct
  expansion of `mem_orthogonal_iff` and `S.skew`.
- `InducedOrbitToy/X0Geometry.lean :: orthogonal_range_eq_ker` — use
  `S.epsSymm` to derive `IsRefl`, then `finrank_orthogonal`, rank-nullity,
  and `Submodule.eq_of_le_of_finrank_eq`.

## Prover Round 1 (session 3 — five-file parallel)

Net: 22 → 8 declaration-use `sorry`. `lake build` ✅, 0 custom axioms.

### `InducedOrbitToy/X0Geometry.lean`
- `vplusKerPairing_isPerfPair` (line 111) — closed via
  `LinearMap.IsPerfPair.of_injective`, `LinearMap.BilinForm.orthogonal_orthogonal`,
  with `S.formV0.IsRefl` extracted from `S.epsSymm`.

### `InducedOrbitToy/Slice.lean` (7 of 9 closed)
- `Cdual` (term-mode) — constructed via `S.lambda.toPerfPair.symm`.
- `Cdual_pairing_eq` — via `LinearMap.apply_symm_toPerfPair_self`.
- `parametrizeX0PlusU_mem` — block-matrix lift on `S.V = S.E × S.V0 × S.E'`.
- `parametrizeX0PlusU_uniqueness` — probe at `(0, 0, e')` plus `LinearMap.ext`.
- `uD` (term-mode) — explicit block-matrix formula
  `(e + Cdual D v + ½ Cdual D (D e'), v + D e', e')`, with
  `(2 : F)⁻¹ + (2 : F)⁻¹ = 1` via `rw [← two_mul, mul_inv_cancel₀ hChar]`.
- `uD_neg_inverse` — `linear_combination (norm := abel_nf)` per component.
- `uD_conj_XCB` — block-matrix expansion + helper `Cdual_X0_apply`,
  `S.epsSymm`, `S.skew`, `eps_sq_eq_one`, `IsSkewB B`.

Helpers introduced (private, reusable inside Slice.lean):
`lambda_isPerfPair`, `XCB_apply`, `X0Lift_apply`, `uD_apply`,
`Cdual_neg`, `Cdual_pairing` (no-Nondeg variant), `Cdual_X0_apply`,
`eps_sq_eq_one`.

### `InducedOrbitToy/NormalForm.lean` (1 of 5 closed)
- `kernelImage_dim` — rank-nullity via
  `LinearMap.finrank_range_add_finrank_ker`,
  `Submodule.finrank_map_subtype_eq`, custom `submoduleProdEquiv`,
  `change Module.finrank F S.paired.E + _ = _` then `omega`.

Helpers introduced (private, reusable): `XST_apply`,
`kerXST_submod_le_ker`, `submoduleProdEquiv`, `finrank_submodule_prod`.

### `InducedOrbitToy/LocalForms.lean` (3 of 3 closed)
- `localFormClasses_finite`, `localFormClasses_open`, `localFormClasses`
  — all closed via Path A: enriched the `ClassifyBilinearForms` typeclass
  body so each public theorem becomes a one-line typeclass projection.

Key lesson (carry forward): polymorphic typeclasses over multi-universe
structures must be declared with explicit `class C.{u, v, w, x}`; `Type*`
placeholders in class fields do not unify across uses.

### `InducedOrbitToy/Orbits.lean` (2 of 3 closed)
- `inducedOrbits` — `subset_closure` on `IndPG`, with helpers
  `embO0_X0_eq_X0Lift`, `X0_mem_O0`, `XCB_apply`, `X0Lift_apply`,
  `XCB_sub_X0Lift_mem_unipotent`, `XST_sub_X0Lift_mem_unipotent`,
  `XST_mem_O0PlusU`. Uses `Ring.inverse_one (M₀ := Module.End F S.V0)`.
- `main` — direct decomposition into the four conjuncts, forwarding to
  `inducedOrbits`, `sIndependenceAndOrbitCriterion`, `multiplicityNonDeg`.
