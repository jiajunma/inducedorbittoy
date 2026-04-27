# Prover Backlog

`lake build` is green (verified 2026-04-28, end of Round 4); 0 custom
axioms; **6 declaration-use `sorry` warnings** remain (down from 7 at end
of Round 3). The remaining sorries split into the tiers below — see
`PROGRESS.md` for the per-round assignments and `PROJECT_STATUS.md` for
the inter-target dependency graph.

## Tier S — plan-agent statement / structural fixes

(Tier S #1 — `uD_isParabolic` IsAdjointPair conjunct + `IsParabolicElement`
4th conjunct — was **resolved in session 5 / Round 3**.)

(Tier S #2 — `UnipotentRadical` tightened with the 4th `IsSkewAdjoint`
conjunct — was **resolved in Round 4**, with cascading consumers
`parametrizeX0PlusU_mem` / `parametrizeX0PlusU_existence`,
`XCB_sub_X0Lift_mem_unipotent`, `XST_sub_X0Lift_mem_unipotent`,
`XST_mem_O0PlusU`, `inducedOrbits`, `main` all updated.)

(Tier S #3 — `SliceSetup` Lagrangian fields `L0_paired`,
`L1_isotropic_L0'`, `L0_isotropic_L1'` (replacing the mis-named
`L0_isotropic`) — were **added in Round 4**. Audit confirmed the old
field had no live consumers, only stale comments in `NormalForm.lean`.)

### Tier S #4 — `kernelImage_ker` signature: `Sₕ : LinearEquiv` (not `LinearMap`)

- **File affected:** `InducedOrbitToy/NormalForm.lean` (signature of
  `kernelImage_ker`, line 495).
- **Change:** re-type the `Sₕ` parameter from `S.L1' →ₗ[F] S.Vplus` to
  `S.L1' ≃ₗ[F] S.Vplus` (mirrors `kernelImage_dim` and `kernelImage_im`,
  which already do this). Update the call site at `kernelImage_dim` line
  611 — currently `rw [kernelImage_ker S _hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) T _hT]`,
  which after retype should drop the explicit coercion (or keep it
  consistent with `kernelImage_im`'s pattern).
- **Sorries unblocked:** the Sₕ-injectivity step inside `kernelImage_ker`
  (lines 537/543).
- **Assigned this round (Round 5).**

## Tier A — provable now, no statement changes needed; needs new infrastructure

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` (line 195, private)

Existence of `(Sₕ, D, T)` such that
`IsSkewT T ∧ uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T`.

- **Blocker:** Levi-action machinery is missing from `Slice.lean`. Need:
  - `leviGL_E : (S.E' ≃ₗ[F] S.E') →* Module.End F S.V` — block-diagonal
    embedding of `GL(E')`.
  - `leviGL_V0 : (S.V0 ≃ₗ[F] S.V0) →* Module.End F S.V` — same for `GL(V0)`.
  - `levi_conj_XCB` lemma giving the action on `XCB` parameters per
    blueprint lines 277–278:
    `m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` for
    `m = leviGL_E d ∘ leviGL_V0 g₀`.
- **Plan:** Round 6 — add the Levi machinery to `Slice.lean` as additive
  code. Then this helper closes via:
  - choose `d ∈ GL(E')` so `d(L0') = ker Cbar` (uses `_hRank`),
  - choose `d|_{L1'}` so `Cbar|_{L1'} = Sₕ` (uses surjectivity of `Cbar`),
  - `D := X0⁻¹ on (C - CST Sₕ)` (uses surjectivity of `X0` onto
    `range X0` plus a section choice via `Vplus`-complement).

### `InducedOrbitToy/NormalForm.lean :: residual_levi_extract` (line 319, private)

Forward direction of `pNormalForm_residual_orbit_iso`: from a parabolic
`p` realising the conjugation, extract `h : L0' ≃ₗ L0'`.

- **Blocker:** Levi/unipotent decomposition lemma `parabolic_decompose :
  ∀ p, IsParabolicElement S p → ∃ D m, p = uD D ∘ leviGL m`.
- **Plan:** Round 6 — once Levi machinery lands, write the decomposition
  lemma (~30 lines) and discharge this helper (~20 lines).

### `InducedOrbitToy/NormalForm.lean :: residual_levi_build` (line 348, private)

Backward direction of `pNormalForm_residual_orbit_iso`: given an isometry
`h`, build a parabolic `p`.

- **Blocker:** Tier S #3 fields are now in place (Round 4); the remaining
  blocker is the Levi machinery. The `L0_paired` field gives the
  perfect-pairing dual `(h⁻¹)^∨ : L0 → L0` needed for the `L0` block.
- **Plan:** Round 6 — ~40 lines once Levi machinery lands. Comment
  references at lines 344, 357 to old `L0_isotropic` need a docstring
  refresh in this round (they are stale).

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 324)

- **Blocker:** depends on `pNormalForm_residual_orbit_iso` being fully
  sorry-free (i.e. on `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` all closing). The current statement also lacks
  `Nondegenerate` / `(2 : F) ≠ 0` hypotheses — the prover may need to add
  them and reduce the two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s
  existence half.
- **Plan:** Round 7 (after all Tier A items above land).

## Tier C — needs Tier S #4 (Sₕ as LinearEquiv); Tier S #3 fields already in

### `InducedOrbitToy/NormalForm.lean :: kernelImage_ker` (line 495)
### `InducedOrbitToy/NormalForm.lean :: kernelImage_im` (line 590)

Both blocked on:
- `Sₕ` typed as `LinearEquiv` (Tier S #4 fixes this for `kernelImage_ker`;
  `kernelImage_im` already uses `LinearEquiv`).
- Lagrangian condition `λ(L1, L0') = 0` — **now in place** as Round 4's
  `S.L1_isotropic_L0'`.
- `sDual_restrict_ker_isIso` from `X0Geometry.lean` — already closed in
  session 4 (Round 2).

The `kernelImage_im` reverse direction also needs `S^∨|_{ker X0} : ker X0
≃ L1` (the now-resolved `sDual_restrict_ker_isIso`). With Tier S #4 + the
in-place Lagrangian condition, both sorries close mechanically.

**Plan:** Round 5 (this round).

## Completed (carried forward)

See `task_done.md` for the full list. Highlights:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient` (with
  Round-4 Tier S #2 / #3 structural updates).
- All `X0Geometry.lean` lemmas (including `sDual_restrict_ker_isIso`
  closed in session 4).
- 9 of 9 `Slice.lean` declaration sorries (incl. `Cdual`, `uD`,
  `uD_conj_XCB`, `uD_isParabolic`, **and `parametrizeX0PlusU_existence`
  closed in Round 4**).
- 1 of 5 original `NormalForm.lean` sorries (`kernelImage_dim`); 2 helpers
  added sorry-free in session 4 (`isUnit_uD`, `map_uD_eq_of_le`); the
  inheritance sorry in `pNormalForm` closed in session 5; 5 sorries
  remain (Tier S #4 + Tier C this round, Tier A next round).
- 3 of 3 `LocalForms.lean` sorries (typeclass-projection refactor).
- 2 of 3 `Orbits.lean` sorries (`inducedOrbits`, `main`); cascade for
  Tier S #2 landed in Round 4 (`XCB_sub_X0Lift_mem_unipotent`,
  `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`).
- All `multiplicity*` lemmas via `MultiplicityTheory`.
