# Prover Backlog

`lake build` is green (verified 2026-04-28); 0 custom axioms; **7
declaration-use `sorry` warnings** remain (down from 9 at end of session 4
after Tier S #1 landed in session 5). The remaining sorries split into the
tiers below — see `PROGRESS.md` for the per-round assignments and
`PROJECT_STATUS.md` for the inter-target dependency graph.

## Tier S — plan-agent statement / structural fixes

(Tier S #1 — `uD_isParabolic` IsAdjointPair conjunct + `IsParabolicElement`
4th conjunct — was **resolved in session 5 / Round 3**.)

### Tier S #2 — `UnipotentRadical` is too loose (missing skew-adjointness)

- **Files affected:** `InducedOrbitToy/Basic.lean` (definition).
- **Change:** add a 4th conjunct to `UnipotentRadical S` requiring
  `IsSkewAdjoint S.ambientForm f` (the form-preservation that
  distinguishes 𝔲 = 𝔭 ∩ 𝔤 from the loose 𝔭).
- **Cascading consumers** (each will need a small upgrade):
  - `Slice.lean :: parametrizeX0PlusU_existence` — closes (the new
    conjunct is exactly what was missing for the IsSkewB and E-component
    sorries).
  - `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent` — currently proves
    membership in the *old* (loose) `UnipotentRadical` without any skew
    hypothesis on `(C, B)`; the conclusion no longer holds in the tight
    form unless `(C, B)` come from a skew `T`. The cleanest fix: keep the
    helper but add a hypothesis `(hskew : IsSkewAdjoint S.ambientForm
    (XCB C B - X0Lift S))`, OR fold the helper's logic into a new
    `XST_sub_X0Lift_mem_unipotent` that takes `IsSkewT T` and proves
    skew-adjointness directly from `S.skew` + `IsSkewT T`.
  - `Orbits.lean :: XST_sub_X0Lift_mem_unipotent` — needs a proof that
    `XST T - X0Lift` is skew-adjoint when `T` is skew. The proof
    decomposes through `S.skew` (X₀ skew on V₀) + `S.epsSymm` + the IsSkewT
    hypothesis. Caller `inducedOrbits` already has `_hT : T ∈ Tset_circ`
    which unfolds to `IsSkewT T ∧ rank T = MaximalRank`, so the skew
    hypothesis is in scope.
  - `Orbits.lean :: main` — same; uses `XST_sub_X0Lift_mem_unipotent`
    transitively via `inducedOrbits`.
- **Sorries unblocked:** `Slice.lean:232` (`parametrizeX0PlusU_existence`),
  including its 2 internal scoped sorries (lines 256, 294).
- **Assigned this round (Round 4).**

### Tier S #3 — `SliceSetup` Lagrangian conditions (additive fields)

The blueprint's Lagrangian decomposition `E = L1 ⊕ L0`, `E' = L1' ⊕ L0'`
with the pairing satisfying:
- `L1` ↔ `L1'` perfect (already there as `L1_paired`),
- `L0` ↔ `L0'` perfect (MISSING — the planned `L0_paired` field),
- `λ(L1, L0') = 0` (MISSING — the cross-isotropy needed by
  `kernelImage_ker` / `kernelImage_im` / `residual_levi_build`),
- `λ(L0, L1') = 0` (MISSING — symmetric to above).

**Note on the existing `L0_isotropic` field:** its current name suggests
`λ(L0, L0') = 0`, but the blueprint says `L0 ↔ L0'` is *perfect-paired*,
not annihilating. The existing field is therefore either mis-named (it
should be `L1_isotropic_L0' : λ(L1, L0') = 0` and/or
`L0_isotropic_L1' : λ(L0, L1') = 0`) or is a vestigial placeholder. The
prover for `Basic.lean` should audit and decide whether to rename or keep
+ supplement. Existing consumers using `L0_isotropic` will need to be
checked.

- **Files affected:** `InducedOrbitToy/Basic.lean` (`SliceSetup`
  structure).
- **Change:** add fields:
  - `L0_paired : IsPaired paired.pairing L0 L0'`
  - `L1_isotropic_L0' : IsIsotropic paired.pairing L1 L0'`
  - `L0_isotropic_L1' : IsIsotropic paired.pairing L0 L1'`
  Audit existing `L0_isotropic` (currently typed as
  `IsIsotropic paired.pairing L0 L0'`); if unused, remove. If used, leave
  in place but flag.
- **Cascading consumers:** none (purely additive at the structure level —
  any existing `SliceSetup` instance just gets new fields).
- **Sorries unblocked:**
  - `NormalForm.lean :: kernelImage_ker` (lines 537+543, 2 internal
    scoped sorries) — uses `λ(L1, L0') = 0` + Sₕ injective.
  - `NormalForm.lean :: kernelImage_im` (line 595) — uses
    `λ(L1, L0') = 0`.
  - `NormalForm.lean :: residual_levi_build` (line 363, body) — uses
    `L0_paired` to dualize `h⁻¹ : L0' ≃ L0'` to `(h⁻¹)^∨ : L0 → L0`.
- **Assigned this round (Round 4) — additive only; close work in Round 5+.**

### Tier S #4 — `kernelImage_ker` signature: `Sₕ : LinearEquiv` (not `LinearMap`)

- **File affected:** `InducedOrbitToy/NormalForm.lean` (signature of
  `kernelImage_ker`, line 495).
- **Change:** re-type the `Sₕ` parameter from `S.L1' →ₗ[F] S.Vplus` to
  `S.L1' ≃ₗ[F] S.Vplus` (pulling the iso to the surface; mirrors
  `kernelImage_dim` and `kernelImage_im` which already do this). Update
  the call sites in any callers (audit `Orbits.lean`).
- **Sorries unblocked:** the Sₕ-injectivity step inside `kernelImage_ker`
  (line 537/543).
- **Deferred to Round 5** (after Tier S #3 lands).

## Tier A — provable now, no statement changes needed; needs new infrastructure

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` (line 210, private)

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

### `InducedOrbitToy/NormalForm.lean :: residual_levi_extract` (line 330, private)

Forward direction of `pNormalForm_residual_orbit_iso`: from a parabolic
`p` realising the conjugation, extract `h : L0' ≃ₗ L0'`.

- **Blocker:** Levi/unipotent decomposition lemma `parabolic_decompose :
  ∀ p, IsParabolicElement S p → ∃ D m, p = uD D ∘ leviGL m`.
- **Plan:** Round 6 — once Levi machinery lands, write the decomposition
  lemma (~30 lines) and discharge this helper (~20 lines).

### `InducedOrbitToy/NormalForm.lean :: residual_levi_build` (line 363, private)

Backward direction of `pNormalForm_residual_orbit_iso`: given an isometry
`h`, build a parabolic `p`.

- **Blocker:** Tier S #3 (Lagrangian fields) plus the Levi machinery.
- **Plan:** Round 6 — ~40 lines once both upstreams land.

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 242)

- **Blocker:** depends on `pNormalForm_residual_orbit_iso` being fully
  sorry-free (i.e. on `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` all closing). The current statement also lacks
  `Nondegenerate` / `(2 : F) ≠ 0` hypotheses — the prover may need to add
  them and reduce the two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s
  existence half.
- **Plan:** Round 7 (after all Tier A items above land).

## Tier C — needs Tier S #3 (Lagrangian) + Tier S #4 (Sₕ as LinearEquiv)

### `InducedOrbitToy/NormalForm.lean :: kernelImage_ker` (line 495)
### `InducedOrbitToy/NormalForm.lean :: kernelImage_im` (line 590)

Both blocked on:
- Lagrangian condition `λ(L1, L0') = 0` (Tier S #3 adds this as
  `L1_isotropic_L0'`),
- `Sₕ` typed as `LinearEquiv` (Tier S #4 fixes this for `kernelImage_ker`;
  `kernelImage_im` already uses `LinearEquiv`).

The `kernelImage_im` reverse direction also needs `S^∨|_{ker X0} : ker X0
≃ L1` (the now-resolved `sDual_restrict_ker_isIso`). With that and the
Lagrangian condition, both sorries close mechanically.

**Plan:** Round 5 (after Tier S #3 + #4 land).

## Tier D — autoformalization statement bugs

### `InducedOrbitToy/Slice.lean :: parametrizeX0PlusU_existence` (line 232)

Body has 2 internal scoped sorries (E component of the equality at line
294 and the IsSkewB conjunct at line 256). Both close once Tier S #2
lands (`UnipotentRadical` tightened with skew-adjointness).
**Assigned this round (Round 4).**

(`uD_isParabolic` — Tier D — was resolved in session 5 / Round 3 via
Tier S #1.)

## Completed (carried forward)

See `task_done.md` for the full list. Highlights:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient`.
- All `X0Geometry.lean` lemmas (including `sDual_restrict_ker_isIso`
  closed in session 4).
- 8 of 9 `Slice.lean` sorries (incl. `Cdual`, `uD`, `uD_conj_XCB`, and
  `uD_isParabolic` closed in session 5).
- 1 of 5 original `NormalForm.lean` sorries (`kernelImage_dim`); 2 helpers
  added sorry-free in session 4 (`isUnit_uD`, `map_uD_eq_of_le`); the
  inheritance sorry in `pNormalForm` closed in session 5.
- 3 of 3 `LocalForms.lean` sorries (typeclass-projection refactor).
- 2 of 3 `Orbits.lean` sorries (`inducedOrbits`, `main`).
- All `multiplicity*` lemmas via `MultiplicityTheory`.
