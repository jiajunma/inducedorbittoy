# Prover Backlog

`lake build` is green (verified 2026-04-28, end of Round 5); 0 custom
axioms; **4 declaration-use `sorry` warnings** remain (down from 6 at
end of Round 4). The remaining sorries split into the tiers below — see
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

(Tier S #4 — `kernelImage_ker`'s `Sₕ` re-typed to `S.L1' ≃ₗ[F] S.Vplus`
— was **resolved in Round 5 / session 7**. `kernelImage_dim` call site
updated to drop the explicit `LinearMap` coercion. The closure of
`kernelImage_ker` and `kernelImage_im` followed mechanically once the
re-typing landed.)

### Tier S #5 (provisional) — `pNormalForm_witnesses` may need restructuring

The current statement of `pNormalForm_witnesses` (lines 195–203 of
`InducedOrbitToy/NormalForm.lean`) glosses over the Levi step (see the
docstring's "subtlety" note). Strictly speaking, the helper as written
is provable only when the input `(C, B)` is *already* Levi-normalized
(`ker Cbar = L0'`, `Cbar|_{L1'} = Sₕ`).

The plan is to handle this in **Round 7** as part of the closure work —
either restructure the helper to internalize the Levi step (preferred)
or split `pNormalForm` to do Levi-then-uD explicitly.

The exact form of the restructure depends on what Round 6 delivers. Hold
the decision until Round 6's Levi machinery lands; the Round 7 prover
will pick the cleanest signature based on Slice.lean's actual API.

## Tier A — provable now once Levi machinery is in place

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` (line 195, private)

Existence of `(Sₕ, D, T)` such that
`IsSkewT T ∧ uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T`.

- **Blocker:** Levi-action machinery is missing from `Slice.lean`. Need:
  - `leviGL_E : (S.E' ≃ₗ[F] S.E') →* Module.End F S.V` — block-diagonal
    embedding of `GL(E')`.
  - `leviGL_V0 : (subgroup of `S.V0 ≃ₗ S.V0` preserving `formV0`)
    →* Module.End F S.V` — same for `G_0` (isometries of `V_0`).
  - `levi_conj_XCB` lemma giving the action on `XCB` parameters per
    blueprint lines 277–278:
    `m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` for
    `m = leviGL_E d ∘ leviGL_V0 g₀`.
  - Optionally: `parabolic_decompose` (any `IsParabolicElement` factors
    as `uD D ∘ leviGL_E d ∘ leviGL_V0 g₀`).
- **Plan:** Round 6 — add Levi machinery to `Slice.lean` (additive).
  Round 7 — close this helper using:
  - choose `d ∈ GL(E')` so `d(L0') = ker Cbar` (uses `_hRank`),
  - choose `d|_{L1'}` so `Cbar|_{L1'} = Sₕ` (uses surjectivity of `Cbar`),
  - `D := X0⁻¹ on (C - CST Sₕ)` (uses surjectivity of `X0` onto
    `range X0` plus a section choice via `Vplus`-complement).

### `InducedOrbitToy/NormalForm.lean :: residual_levi_extract` (line 319, private)

Forward direction of `pNormalForm_residual_orbit_iso`: from a parabolic
`p` realising the conjugation, extract `h : L0' ≃ₗ L0'`.

- **Blocker:** Levi/unipotent decomposition lemma `parabolic_decompose :
  ∀ p, IsParabolicElement S p → ∃ D d g₀, p = uD D ∘ leviGL_E d ∘ leviGL_V0 g₀`.
- **Plan:** Round 6 — Slice.lean's `parabolic_decompose` lands. Round 7 —
  discharge this helper (~20 lines): apply `parabolic_decompose` to `p`,
  the unipotent `uD D` part doesn't affect the residual `L0' → L0` block
  (per blueprint lines 305–309), so the iso `h` comes from `d|_{L0'}`.

### `InducedOrbitToy/NormalForm.lean :: residual_levi_build` (line 348, private)

Backward direction of `pNormalForm_residual_orbit_iso`: given an isometry
`h : L0' ≃ₗ L0'`, build a parabolic `p` realising the conjugation.

- **Blocker:** the perfect-pairing dual `(h⁻¹)^∨ : L0 → L0` plus the
  block-decomposition of `S.V` along `L1 ⊕ L0 ⊕ V0 ⊕ L1' ⊕ L0'`. The
  `S.L0_paired` field (Round 4 / Tier S #3) is the perfect-pairing
  needed for the dual transpose.
- **Plan:** Round 6 — Slice.lean's `leviGL_E` machinery makes the block
  construction available. Round 7 — discharge this helper (~40 lines):
  build `d : E' ≃ₗ E'` as `(h⁻¹)^∨ ⊕ id_{L1'}` along `IsCompl L1' L0'`
  (or rather, build `d` so `d|_{L0'} = h` and `d|_{L1'} = id`); set
  `p := leviGL_E d`. The perfect-pairing dual forces the `L0` block to
  be `(h⁻¹)^∨` automatically. Refresh stale comments at lines 344, 357.

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 324)

- **Blocker:** depends on `pNormalForm_residual_orbit_iso` being fully
  sorry-free (i.e. on `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` all closing). The current statement also lacks
  `Nondegenerate` / `(2 : F) ≠ 0` hypotheses — the prover may need to
  add them and reduce the two-`Sₕ` case to single-`Sₕ` via
  `pNormalForm`'s existence half.
- **Plan:** Round 8 (after all Round 6 + Round 7 Tier A items land).

## Completed (carried forward)

See `task_done.md` for the full list. Highlights:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient` (with
  Round-4 Tier S #2 / #3 structural updates).
- All `X0Geometry.lean` lemmas (including `sDual_restrict_ker_isIso`
  closed in session 4).
- 9 of 9 `Slice.lean` declaration sorries (incl. `Cdual`, `uD`,
  `uD_conj_XCB`, `uD_isParabolic`, `parametrizeX0PlusU_existence`).
- 3 of 5 original `NormalForm.lean` sorries (`kernelImage_dim` from
  Round 1, `kernelImage_ker` and `kernelImage_im` Round 5).
- 3 of 3 `LocalForms.lean` sorries (typeclass-projection refactor).
- 2 of 3 `Orbits.lean` sorries (`inducedOrbits`, `main`).
- All `multiplicity*` lemmas via `MultiplicityTheory`.
