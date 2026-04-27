# Recommendations for Round 8 Plan Agent

## Round 7 outcome at a glance

- **Sorry count:** 5 → **3** (−2 net). Plan target was 5 → 2; achieved 2 of 3.
- **Closed:** `residual_levi_extract`, `residual_levi_build` (both sorry-free, ~290 lines combined).
- **Tier S #5 signature restructure landed** (Sₕ : L1' ≃ₗ Vplus, Levi factor d exposed).
- **Public consumer `pNormalForm_residual_orbit_iso` is sorry-free** with clean axiom audit.
- **Deferred:** `pNormalForm_witnesses` body — single isolated `sorry` at line 216 with documented four-step plan in the body docstring.

## Recommended Round 8 plan

### Option A — single-file, single-objective focus on the last NormalForm sorry

**Assign one prover to `NormalForm.lean :: pNormalForm_witnesses` body (line 216).**

This is the only thing remaining inside the NormalForm pipeline; closing it makes `pNormalForm` sorry-free and propagates the cleanliness through the entire downstream chain.

**Four-step body plan** (already written into the in-file docstring above the `sorry`):

1. **Build `(Sₕ, d)` from `_hRank : rank Cbar = c`.**
   - `dL0' : S.L0' →ₗ[F] LinearMap.ker (Cbar S C)` via `LinearMap.codRestrict` (need to first show `S.L0' ≤ ker (Cbar)` — but we want them *equal* via dim-matching).
   - Use `LinearEquiv.ofBijective` on the codrestricted map, with bijectivity from `Module.finrank` equality (consume `_hRank` plus the `c` accountancy in `X0Setup`).
   - Lift to `d : S.E' ≃ₗ[F] S.E'` extending the L0'-iso by `id` on L1' — same `Submodule.prodEquivOfIsCompl` pattern as `extendL0'IsoToE'` in the Round 7 helper.
   - `Sₕ : S.L1' ≃ₗ[F] S.Vplus` via `Cbar` restricted to L1' under the `_hRank` dim-matching.

2. **Set `(C', B') := (C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm)` and apply `leviGL_E_conj_XCB`.**
   - `leviGL_E_conj_XCB` (Slice.lean Round 6) gives `leviGL_E d ∘ XCB(C, B) = XCB(C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm) ∘ leviGL_E d`.
   - After this rewrite, the LHS is in normal form for the unipotent step.

3. **Build `D` such that `X0 ∘ D = C' - CST Sₕ`.**
   - `C' - CST Sₕ` lands in `range X0` by construction (the L0' part of C' is zero by Step 1, and the L1' part equals `CST Sₕ` by definition of `Sₕ`).
   - Use `S.isCompl : Vplus ⊕ range X0 = V0` plus the surjectivity of `X0` onto its range to extract `D` via `LinearMap.range_eq_top` machinery, or equivalently via `Submodule.IsCompl.linearProjOfIsCompl` + `LinearMap.codRestrict`.
   - `T` reads off the `B`-block residual after the unipotent normalisation.

4. **Combine via `uD_conj_XCB` + `parametrizeX0PlusU_uniqueness` + `uD_neg_inverse`.**
   - `uD_conj_XCB` (Slice.lean) gives the unipotent half of the conjugation.
   - Compose with the Levi half (Step 2 result) to get the full equation.
   - `parametrizeX0PlusU_uniqueness` identifies the resulting C''/B'' with `CST Sₕ` and `BST T`.

**Key Mathlib pieces:**
- `LinearEquiv.ofBijective` (Step 1).
- `LinearMap.codRestrict` + `LinearMap.range_eq_top` (Step 3).
- `Submodule.prodEquivOfIsCompl` (Step 1, mirroring `extendL0'IsoToE'`).
- `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness` (Slice.lean — Step 3 + 4).
- `uD_conj_XCB`, `leviGL_E_conj_XCB`, `uD_neg_inverse` (Slice.lean Round 5/6).

**Estimated effort:** ~150 lines. Within a single round if the prover is focused.

**Stop condition:** if the d-construction (Step 1) proves intractable due to `Module.finrank` plumbing, the prover may extract Step 1 as a separate `private def` skeleton and continue with Steps 2-4 against an opaque `(Sₕ, d)`. This still yields a useful body; the sorry can localise to the d-construction helper.

### Option B — parallel multi-file dispatch (closes 2 sorries in one round)

If the harness dispatches multiple provers, try:

- **Prover 1: `NormalForm.lean :: pNormalForm_witnesses`** (Option A above).
- **Prover 2: `Orbits.lean :: sIndependenceAndOrbitCriterion`** (lines 358 + 376) — now structurally unblocked because `pNormalForm_residual_orbit_iso` is sorry-free.

The two are **independent** at the source level (no edit overlap; NormalForm prover edits lines 200-240, Orbits prover edits lines 320-380). End-of-round merge is conflict-free.

**Orbits prover's plan (per session-8 task_results report):**
- **Forward direction (line 358):** From `_hg : IsometryEnd S g` and conjugation equation `_hyeq`, show `g ∈ P` (i.e., `IsParabolicElement S g`). This is the parabolic-decomposition step. **Workaround if `parabolic_decompose` (Slice.lean) is not closed:** use a direct argument via flag-stability under isometries plus the conjugation equation.
- **Reverse direction (line 376):** Apply `pNormalForm_residual_orbit_iso` to lift `_h : L0' ≃ₗ[F] L0'` (from `IsometryRel`) to a P-element `p` with `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p`. Use `IsParabolicElement → IsometryEnd` to membership-witness `p` for `GOrbit`.
- **Hypothesis additions:** Both directions need `(Nondegenerate, (2 : F) ≠ 0, Sₕ₁ = Sₕ₂)` added to the `sIndependenceAndOrbitCriterion` statement, OR strengthening `pNormalForm_residual_orbit_iso` to absorb them. The session-8 prover recommended **option (b)** — restate `pNormalForm_residual_orbit_iso` to fold them in — because it keeps the public statement of `sIndependenceAndOrbitCriterion` clean.
- **Stale comments to refresh:** lines 357 of Orbits.lean still reference the now-removed `L0_isotropic` field (replaced by Lagrangian quartet in session 6). Refresh during the edit pass.

### NOT recommended for Round 8

- **Closing `parabolic_decompose` (Slice.lean line 1089).** Round 7's NormalForm work used Option B and did not need it. Three sub-constructions required (~85 lines per `informal/levi.md §6.6`). Skip unless Orbits.lean requires it for the forward direction. **If Orbits requires it**, prefer the workaround (direct flag-stability argument) over closing `parabolic_decompose`.

## Targets closest to completion (priority order)

1. **`pNormalForm_witnesses`** (NormalForm.lean line 216) — single isolated sorry, well-documented body plan, ~150 lines. **Top priority.** Closes the only remaining sorry inside the NormalForm pipeline; makes `pNormalForm` sorry-free.

2. **`sIndependenceAndOrbitCriterion`** (Orbits.lean lines 358 + 376) — two scoped sorries, structurally unblocked, ~80 lines combined (forward + reverse). Now possible because `pNormalForm_residual_orbit_iso` is sorry-free. May need a `pNormalForm_residual_orbit_iso` signature tweak (option (b) above).

3. **`parabolic_decompose`** (Slice.lean line 1089) — three sub-constructions, ~85 lines, **optional** unless Orbits forward direction needs it.

## Approaches that showed promise but need more work

- **`set p_uv := p (0, 0, (v : E'))` for opaque p-of-test-vector abbreviations.** Worked well in `residual_levi_extract` once the prover learned NOT to also `set` the sum `(Cdual ... + T₂ ...)`. Reusable pattern: `set` for opaque applications, never `set` for sums you'll later need to `LinearMap.add_apply`-rewrite.

- **`extendL0'IsoToE'` block-extension via `prodEquivOfIsCompl` + `prodCongr`.** Clean construction; reusable for any other "extend an iso on one summand by id on the complementary summand" need. The two bridge lemmas (`projL1' ∘ d.symm = projL1'`, `projL0' ∘ d.symm = h.symm ∘ projL0'`) are also reusable.

- **`XST_apply` private helper for explicit unfolding.** When a proof needs the explicit unfolding of a multi-let block-matrix def, write a `private theorem _apply` near the top of the consuming section. Saves ~10 lines per consumer; pattern is the standard project-local style (`SliceSetup.ambientForm`-style).

## Targets blocked (do not assign)

- **None.** All three remaining sorries are now structurally unblocked:
  - `pNormalForm_witnesses` has the Levi machinery in scope (Round 6) and the consumer-correctness proof in scope (Round 7's `residual_levi_*` are sorry-free).
  - `sIndependenceAndOrbitCriterion` has `pNormalForm_residual_orbit_iso` sorry-free in scope.
  - `parabolic_decompose` has all the sub-pieces (`leviGL_*`, `parametrizeX0PlusU_existence`) sorry-free in scope.

## Reusable proof patterns discovered (Round 7)

These flow into PROJECT_STATUS.md's knowledge base. Augments session 8 list.

1. **`prodEquivOfIsCompl` symm via `Submodule.toLinearMap_prodEquivOfIsCompl_symm`.** The symm coerces to `(linearProjOfIsCompl p q h).prod (linearProjOfIsCompl q p _)`, i.e., `prodEq.symm e' = (projL1' e', projL0' e')` for our `IsCompl L1' L0'`. Bypasses unfolding through `LinearEquiv.trans`.

2. **`set ... with hdef` for opaque shorthands, BUT NOT for sums you'll later `LinearMap.add_apply`-rewrite.** Identifies a specific failure mode: `set lhs_E := Cdual ... + T₂ ...` opaquefies the sum, breaking subsequent `rw [add_apply]`.

3. **`congr 1` does NOT split through outer `LinearMap.comp`.** For `XCB(A, B) = XCB(A', B') ∘ leviGL_E d`-style equations where the outer is `LinearMap.comp`, `congr 1` doesn't yield 2 component goals. Better: prove `A = A'` and `B = B'` as separate `have`s and chain `rw [hA, hB]`.

4. **Linearity in 1st arg of `S.paired.pairing`: `map_add` first, then `add_apply`.** The pattern `pairing (a + b) c = pairing a c + pairing b c` reduces via `LinearMap.map_add` (LHS first arg) followed by `LinearMap.add_apply` (resulting `(f + g) c`); reversed order fails.

5. **`(qFun l : L0').val = qFunRaw l` is *definitionally* equal** when `qFun = LinearMap.codRestrict L0' qFunRaw _`. Use `(qFun l : E') = 0 → qFunRaw l = 0` via `exact h_val` (no `simpa`).

6. **Trailing `rfl` after `simp only [..., map_zero]` is "No goals" lint.** `simp only` with `map_zero` already closes `f 0 = 0`. Drop it.

7. **LinearEquiv at definition; pass directly at use site.** When a private theorem strengthens `Sₕ` from LinearMap to LinearEquiv, the consumer call site that expects LinearMap should pass `Sₕ` directly (Lean auto-coerces via LinearEquiv.toLinearMap-via-CoeFun). Explicit coercion at the call site fails type-check.

8. **`S.V` ≡ `S.paired.E'` abbrev boundary requires explicit type ascription in helper defs.** When defining helpers like `extendL0'IsoToE' S h : E' ≃ E'`, every `↑d.symm e'` application needs `(d.symm : S.paired.E' →ₗ[F] S.paired.E')` to bridge the abbrev. Otherwise: `Application type mismatch: argument e' has type S.V but expected S.paired.E'`.

9. **`XST_apply` private helper near top of consuming section.** When a proof needs explicit unfolding of a multi-let block-matrix def, write a `private theorem _apply` early in the section.

## End-of-round housekeeping

- **Stale comments to refresh next round:** `NormalForm.lean` lines 344, 357 still contain comment refs to the now-removed `L0_isotropic` field (replaced by Lagrangian quartet in session 6). They compile cleanly but should be refreshed during any edit pass through this region.
- **Task results files:** processed/round6/ should be moved to processed/round7/ at the start of Round 8 to maintain history. The current task_results files (`InducedOrbitToy_NormalForm.lean.md`, `InducedOrbitToy_Slice.lean.md`, `Orbits.lean.md`, `X0Geometry.lean.md`) reflect the Round 7 work and should be archived under processed/round7/ before the new round starts.
