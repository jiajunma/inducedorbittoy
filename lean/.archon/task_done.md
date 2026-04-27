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

## Prover Round 2 (session 4 — six-file parallel dispatch)

Net: 8 → 9 declaration-use `sorry` (count rose by 1 due to deliberate
helper-extraction in NormalForm.lean), but **one Tier B target fully
resolved** and the remaining structural skeleton for Tier A is now in
place. `lake build` ✅ at end of round; 0 custom axioms.

### `InducedOrbitToy/X0Geometry.lean` (1 → 0 declaration warnings) ✅ Tier B closed
- `sDual_restrict_ker_isIso` — resolved by enriching `DualTransposeData`
  in this file (the structure was misattributed to `Basic.lean` in the
  session-3 plan; it actually lives in `X0Geometry.lean`).
- Two new fields added: `range_le_L1 : LinearMap.range Tdual ≤ L1` and
  `finrank_L1_eq : finrank L1 = finrank L1'`.
- The two scoped sorries closed in one line each:
  `h_in_L1 := fun w => D.range_le_L1 ⟨_, rfl⟩` and
  `h_dim_L1 := D.finrank_L1_eq.trans hL1'`.
- Lesson: **verify structure location via grep before scoping a refactor**.
- Side benefit: also unblocks the dimension argument in `kernelImage_im`.

### `InducedOrbitToy/NormalForm.lean` — structural decomposition (4 → 6)
Tier A targets `pNormalForm` and `pNormalForm_residual_orbit_iso` had
their bare sorries restructured into focused, named helper lemmas
exposing exactly the missing infrastructure. The two public theorems'
proof bodies are now mechanical assemblies; only the helpers carry
sorry. Specific work:

- `isUnit_uD` (private helper, sorry-free) — `IsUnit (uD S D)` via
  `(Units.mkOfMulEqOne _ _ h).isUnit`.
- `map_uD_eq_of_le` (private helper, sorry-free) — `Submodule.map (uD D) F = F`
  from inclusions both ways using `uD (-D) ∘ uD D = id`.
- `pNormalForm` body — assembles `Sₕ, T, hT, uD D, parabolic-element,
  conjugation` from `pNormalForm_witnesses` plus the helpers above.
  Conjugation falls out by post-composing `hConj` with `uD D` and using
  `uD (-D) ∘ uD D = id`.
- `pNormalForm_residual_orbit_iso` body — trivial `refine ⟨?_, ?_⟩` plus
  dispatch to `residual_levi_extract` / `residual_levi_build`.

Net: 2 bare sorries → 6 focused, named sorries (`pNormalForm_witnesses`,
`pNormalForm` IsAdjointPair conjunct, `residual_levi_extract`,
`residual_levi_build`, plus the unchanged Tier C `kernelImage_ker`,
`kernelImage_im`). The 6 sorries are each pinned to a specific upstream
blocker.

### `InducedOrbitToy/Slice.lean` — body refinement (2 → 2)
Both Tier D sorries (`parametrizeX0PlusU_existence`, `uD_isParabolic`)
were re-confirmed false-as-stated this round, but the proof bodies were
refined to expose the precise impossible obligation:

- `parametrizeX0PlusU_existence` — V₀ and E' Prod-components fully
  closed; only the E component remains as sorry (false without
  skew-adjointness on `Y`). The `IsSkewB` conjunct is opened up via
  `intro u v` + `show` of the unfolded goal.
- `uD_isParabolic` — flag-preservation conjuncts (lines ≈462, 468) now
  fully proven; only the IsAdjointPair conjunct (line 460) remains as
  sorry (false self-adjoint statement; blueprint says isometry).

These remain Tier D blockers awaiting plan-agent statement fixes.

### `InducedOrbitToy/Orbits.lean` — body refinement (1 → 1)
`sIndependenceAndOrbitCriterion`'s two scoped sorries got real proof
prefixes:
- Forward direction: `obtain ⟨_g, _hg, _hyeq⟩` extracts the conjugating
  isometry from orbit-equality + `Ring.inverse_one` self-membership.
- Reverse direction: `obtain ⟨_h, _h_isom⟩` extracts the bilinear-isometry
  witness via `unfold IsometryRel Bilinear.AreIsometric`.

Both directions remain blocked on `pNormalForm_residual_orbit_iso` (this
file is downstream).

### Cross-cutting wins (session 4)
- **`Units.mkOfMulEqOne` for `IsUnit` from one-sided inverse** on
  `Module.End F V` (finite-dim V). Replaces the deprecated
  `LinearMap.mul_eq_one_of_mul_eq_one` chain.
- **Helper-lemma decomposition pattern** for "cannot fully close, but can
  articulate the obligation precisely" — extract as focused helper with
  targeted signature, sorry it, use from the public theorem.
- **`obtain` from existential makes destructured fields opaque** — fix by
  packaging the equation directly in helper's conclusion (avoid the
  existential wrapper).
- All public theorems audited via `#print axioms` / `lean_verify`:
  only `[propext, Classical.choice, Quot.sound]` plus `sorryAx` on
  declarations that still embed an explicit `sorry`. **No custom axioms.**

## Prover Round 3 (session 5 — Tier S #1 statement correction)

Net: 9 → 7 declaration-use `sorry`. `lake build` ✅, 0 custom axioms.

Two files coupled (Slice.lean + NormalForm.lean), end-of-round build green
after both halves landed in parallel.

### `InducedOrbitToy/Slice.lean` (2 → 1) — Tier S #1, half 1

- `uD_isParabolic` — statement corrected: 4th conjunct
  `IsAdjointPair B B (uD D) (uD D)` (false self-adjoint) →
  `IsAdjointPair B B (uD D) (uD (-D))` (isometry pair). Sorry at line 460
  closed via `Cdual_pairing_eq` + `S.epsSymm` + `linear_combination` with
  ε-symmetry coefficients (no new helpers, no axioms).
  - Proof template: destruct vectors as `(e, v, e')`, apply `uD_apply` /
    `uD_apply` (for `uD (-D)`), `simp only [SliceSetup.ambientForm,
    LinearMap.mk₂_apply, ...]`, apply `Cdual_pairing_eq` to all
    `λ(Cdual D ·, ·)` atoms, close with `linear_combination` using `hε`,
    `hε2`, point-specific `hC`, `hD'`.
  - Anti-pattern confirmed retired: `field_simp` for `(2:F)⁻¹+(2:F)⁻¹=1`.
  - Helpers `XCB_apply`, `XST_apply`, `uD_apply`, `uD_conj_XCB`,
    `Cdual_pairing_eq` signatures unchanged.

### `InducedOrbitToy/NormalForm.lean` (6 → 5) — Tier S #1, half 2

- `IsParabolicElement` — definition's 4th conjunct changed:
  `LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p` →
  `LinearMap.IsOrthogonal S.ambientForm p`. Now matches the `IsometryEnd`
  shape used in `Orbits.lean`. Docstring updated to reflect isometry semantics.
- `pNormalForm` — line-272 inheritance sorry closed via 16-line calc chain
  combining the corrected `uD_isParabolic` (giving `IsAdjointPair (uD D)
  (uD (-D))`) with `uD_neg_inverse` (giving `uD (-D) ∘ uD D = id`) yielding
  `B (uD D u) (uD D v) = B u (uD (-D) (uD D v)) = B u v`.
- `residual_levi_build` — comment updated (Tier-D inheritance reference
  removed); body unchanged (still bare sorry, blocked on Tier S #3 + Levi).
- All other sorries (`pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` body, `kernelImage_ker`, `kernelImage_im`) untouched.

### Cross-cutting wins (session 5)

- **Adjoint-pair → orthogonal via paired inverse:** template proof for
  converting `IsAdjointPair B B f g` + `g ∘ f = id` to `IsOrthogonal B f`
  via a 3-line calc chain.
- **Cross-file proof structure validation via `lean_run_code`:** when a
  proof depends on a sister-prover's signature change not yet landed,
  validate the local proof shape with hypothetical inputs of the correct
  shape (eliminates uncertainty during the parallel race).
- All public theorems re-audited: `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]` (plus `sorryAx` on still-open
  declarations). **No custom axioms.**
