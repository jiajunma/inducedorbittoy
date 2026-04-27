# Prover Backlog

`lake build` is green (verified 2026-04-28); 0 custom axioms; **9
declaration-use `sorry` warnings** remain. The remaining sorries split
into four tiers — see `PROGRESS.md` for per-round assignments and the
inter-target dependency graph in `PROJECT_STATUS.md`.

## Tier S — plan-agent statement / structural fixes

Out-of-band corrections that the plan agent must instruct the prover to
make to autoformalised statements (or to structures). These are **not
prover sorries** in the usual sense; they unblock multiple downstream
sorries at once.

### Tier S #1 — `IsParabolicElement` is the wrong predicate (isometry, not self-adjoint)

- **Files affected:** `InducedOrbitToy/NormalForm.lean` (definition),
  `InducedOrbitToy/Slice.lean` (consumer `uD_isParabolic`).
- **Change:**
  - `Slice.lean :: uD_isParabolic` (line 442–460): change the IsAdjointPair
    conjunct from `IsAdjointPair B B (uD D) (uD D)` to
    `IsAdjointPair B B (uD D) (uD (-D))` and discharge the now-true sorry
    at line 460.
  - `NormalForm.lean :: IsParabolicElement` (line 86–89): change the 4th
    conjunct from `IsAdjointPair S.ambientForm S.ambientForm p p` to
    `LinearMap.IsOrthogonal S.ambientForm p` (matches the predicate
    `IsometryEnd` already used in `Orbits.lean`). Update `pNormalForm`'s
    proof body (line 250–272) so the now-`IsOrthogonal` conjunct is
    discharged from the new `uD_isParabolic` plus `uD_neg_inverse`. The
    Tier-D inheritance sorry at line 272 closes.
- **Sorries unblocked when this lands:**
  - `Slice.lean:460` (inside `uD_isParabolic`),
  - `NormalForm.lean:272` (the IsAdjointPair conjunct of `pNormalForm`'s
    `IsParabolicElement` discharge),
  - The IsParabolicElement-internal portion of `NormalForm.lean:336`
    (`residual_levi_build`).
- **Assigned this round (Round 3).**

### Tier S #2 — `UnipotentRadical` is too loose (missing skew-adjointness)

- **File affected:** `InducedOrbitToy/Basic.lean` (definition).
- **Change:** add a 4th conjunct to `UnipotentRadical S` requiring
  `IsSkewAdjoint S.ambientForm f` (the form-preservation that
  distinguishes 𝔲 = 𝔭 ∩ 𝔤 from the loose 𝔭).
- **Cascading consumers** (each will need a small upgrade):
  - `Slice.lean :: parametrizeX0PlusU_existence` — closes (the new
    conjunct is exactly what was missing for the IsSkewB and E-component
    sorries).
  - `Orbits.lean :: inducedOrbits` — already calls
    `XST_sub_X0Lift_mem_unipotent`; needs an analogous proof that
    `XST T - X0Lift` is skew-adjoint.
  - `Orbits.lean :: main` — same; needs the skew-adjointness lemma.
- **Sorries unblocked:** `Slice.lean:232` (`parametrizeX0PlusU_existence`),
  including its 2 internal scoped sorries.
- **Deferred to Round 4 / 5** (large-cascade refactor).

### Tier S #3 — `SliceSetup` missing Lagrangian condition `λ(L0, L0') = 0`

Wait — `L0_isotropic` already gives `λ(L0, L0') = 0`. The gap is the
*paired* (perfect-pairing) version on `L0 × L0'`, used to dualize
`h⁻¹ : L0' ≃ L0'` to obtain `(h⁻¹)^∨ : L0 → L0`.

- **File affected:** `InducedOrbitToy/Basic.lean` (`SliceSetup` structure).
- **Change:** add field `L0_paired : IsPaired paired.pairing L0 L0'`
  (alongside the existing weaker `L0_isotropic`). This is a purely
  additive field — existing proofs continue to compile.
- **Cascading consumers:** none (purely additive at the structure level).
- **Sorries unblocked:**
  - `NormalForm.lean:336` (`residual_levi_build`),
  - structural pieces of `NormalForm.lean:482` (`kernelImage_ker`),
  - structural pieces of `NormalForm.lean:577` (`kernelImage_im`).
- **Deferred to Round 4 / 5.**

### Tier S #4 — `kernelImage_ker` signature: `Sₕ : LinearEquiv` (not `LinearMap`)

- **File affected:** `InducedOrbitToy/NormalForm.lean` (signature of
  `kernelImage_ker`, line 482).
- **Change:** re-type the `Sₕ` parameter from `S.L1' →ₗ[F] S.Vplus` to
  `S.L1' ≃ₗ[F] S.Vplus` (pulling the iso to the surface; mirrors
  `kernelImage_dim` and `kernelImage_im` which already do this). Update
  the call sites in `Orbits.lean` to pass the iso.
- **Sorries unblocked:** the Sₕ-injectivity step inside `kernelImage_ker`.
- **Deferred to Round 4 / 5.**

## Tier A — provable now, no statement changes needed; needs new infrastructure

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` (line 196, private)

Existence of `(Sₕ, D, T)` such that `IsSkewT T ∧ uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T`.

- **Blocker:** Levi-action machinery is missing from `Slice.lean`. Need:
  - `leviGL_E : (S.E' ≃ₗ[F] S.E') →* Module.End F S.V` — block-diagonal
    embedding of `GL(E')`.
  - `leviGL_V0 : (S.V0 ≃ₗ[F] S.V0) →* Module.End F S.V` — same for `GL(V0)`.
  - `levi_conj_XCB` lemma giving the action on `XCB` parameters per
    blueprint lines 277–278:
    `m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` for
    `m = leviGL_E d ∘ leviGL_V0 g₀`.
- **Plan:** Round 4 — add the Levi machinery to `Slice.lean` as additive
  code. Then this helper closes via:
  - choose `d ∈ GL(E')` so `d(L0') = ker Cbar` (uses `_hRank`),
  - choose `d|_{L1'}` so `Cbar|_{L1'} = Sₕ` (uses surjectivity of `Cbar`),
  - `D := X0⁻¹ on (C - CST Sₕ)` (uses surjectivity of `X0` onto
    `range X0` plus a section choice via `Vplus`-complement).

### `InducedOrbitToy/NormalForm.lean :: residual_levi_extract` (line 307, private)

Forward direction of `pNormalForm_residual_orbit_iso`: from a parabolic
`p` realising the conjugation, extract `h : L0' ≃ₗ L0'`.

- **Blocker:** Levi/unipotent decomposition lemma `parabolic_decompose :
  ∀ p, IsParabolicElement S p → ∃ D m, p = uD D ∘ leviGL m`.
- **Plan:** Round 4 — once Levi machinery lands, write the decomposition
  lemma (~30 lines) and discharge this helper (~20 lines).

### `InducedOrbitToy/NormalForm.lean :: residual_levi_build` (line 336, private)

Backward direction of `pNormalForm_residual_orbit_iso`: given an isometry
`h`, build a parabolic `p`.

- **Blocker:** Tier S #3 (`SliceSetup` `L0_paired` field) plus the Levi
  machinery from Round 4. After Tier S #1 lands the IsParabolicElement
  inheritance is no longer a blocker.
- **Plan:** Round 4 / 5 — ~40 lines once both upstreams land.

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 242)

- **Blocker:** depends on `pNormalForm_residual_orbit_iso` being fully
  sorry-free (i.e. on `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` all closing). The current statement also lacks
  `Nondegenerate` / `(2 : F) ≠ 0` hypotheses — the prover may need to add
  them and reduce the two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s
  existence half.
- **Plan:** Round 5 (after all Tier A items above land).

## Tier C — needs Tier S #3 (Lagrangian) + Tier S #4 (Sₕ as LinearEquiv)

### `InducedOrbitToy/NormalForm.lean :: kernelImage_ker` (line 482)
### `InducedOrbitToy/NormalForm.lean :: kernelImage_im` (line 577)

Both blocked on:
- Lagrangian condition `λ(L1, L0') = 0` (already implicit, but needs to
  be exposed; closely related to Tier S #3),
- `Sₕ` typed as `LinearEquiv` (Tier S #4 fixes this for `kernelImage_ker`;
  `kernelImage_im` already uses `LinearEquiv`).

The `kernelImage_im` reverse direction also needs `S^∨|_{ker X0} : ker X0
≃ L1` (the now-resolved `sDual_restrict_ker_isIso`). With that and the
Lagrangian condition, both sorries close mechanically.

**Plan:** Round 4 / 5 (after Tier S #3 + #4 land).

## Tier D — autoformalization statement bugs (deferred until Tier S addressed)

### `InducedOrbitToy/Slice.lean :: parametrizeX0PlusU_existence` (line 232)

Body has 2 internal scoped sorries (E component of the equality and the
IsSkewB conjunct). Both close once Tier S #2 lands (`UnipotentRadical`
tightened with skew-adjointness).

### `InducedOrbitToy/Slice.lean :: uD_isParabolic` (line 442)

Body has 1 internal scoped sorry (the IsAdjointPair self-adjoint conjunct,
which is *false* as stated — blueprint says isometry). Closes once Tier
S #1 lands (statement change to `IsAdjointPair (uD D) (uD (-D))`).
**Assigned this round (Round 3).**

## Completed (carried forward)

See `task_done.md` for the full list. Highlights:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient`.
- All 7 `X0Geometry.lean` lemmas (including `sDual_restrict_ker_isIso`
  closed in session 4).
- 7 of 9 `Slice.lean` sorries (incl. `Cdual`, `uD`, `uD_conj_XCB`).
- 1 of 5 original `NormalForm.lean` sorries (`kernelImage_dim`); 2 helpers
  added sorry-free in session 4 (`isUnit_uD`, `map_uD_eq_of_le`).
- 3 of 3 `LocalForms.lean` sorries (typeclass-projection refactor).
- 2 of 3 `Orbits.lean` sorries (`inducedOrbits`, `main`).
- All `multiplicity*` lemmas via `MultiplicityTheory`.
