# Prover Backlog

`lake build` is green (verified 2026-04-28, end of Round 6); 0 custom
axioms; **5 declaration-use `sorry` warnings** (4 + 1 additive from
Round 6's deferred `parabolic_decompose`):

- `InducedOrbitToy/Slice.lean:1078` — `parabolic_decompose` (Tier A,
  **Round 8**).
- `InducedOrbitToy/NormalForm.lean:195` — `pNormalForm_witnesses`
  (Tier S #5 + Tier A, **Round 7**).
- `InducedOrbitToy/NormalForm.lean:319` — `residual_levi_extract`
  (Tier A, **Round 7**).
- `InducedOrbitToy/NormalForm.lean:348` — `residual_levi_build`
  (Tier A, **Round 7**).
- `InducedOrbitToy/Orbits.lean:324` — `sIndependenceAndOrbitCriterion`
  (Tier A, **Round 8**).

## Tier S — plan-agent statement / structural fixes

(Tier S #1, #2, #3, #4 — all resolved in earlier rounds; see
`task_done.md`.)

### Tier S #5 — `pNormalForm_witnesses` signature change (must land in Round 7)

The current statement of `pNormalForm_witnesses` (NormalForm.lean lines
195–203) is **mathematically false as written**. The conclusion
`uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T` cannot hold for arbitrary `(C, B)`
because `uD`-conjugation only modifies the B-block (per `uD_conj_XCB`),
leaving the C-block invariant. To match `XST Sₕ T` (which has C-block
`CST Sₕ`), the conjugator must include a Levi factor `leviGL_E d`.

**Restructure (Round 7 prover delivers):**

```lean
private theorem pNormalForm_witnesses (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B)
    (_hRank :
      Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' →ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
      (d : S.E' ≃ₗ[F] S.E') (T : S.L0' →ₗ[F] S.L0),
      IsSkewT S T ∧
      uD S D ∘ₗ leviGL_E S d ∘ₗ XCB S C B
        = XST S Sₕ T ∘ₗ uD S D ∘ₗ leviGL_E S d
```

The cascading update to `pNormalForm`'s body (lines 237–301) extracts
`p := uD S D ∘ₗ leviGL_E S d` and proves
`IsParabolicElement S p` from `uD_isParabolic` ∘ `leviGL_E_isParabolic`.

See `.archon/informal/normalform_round7.md` for the full restructure
plan and proof sketches.

## Tier A — provable now with Round 6's Levi machinery in place

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` (line 195, Round 7)

Existence of `(Sₕ, D, d, T)` with the new (Tier S #5) signature.

- **Strategy** (blueprint lines 200–264): build `d : E' ≃ₗ E'` so
  `d(L0') = ker (Cbar C)` and `Cbar (C ∘ d.symm)|_{L1'}` matches a
  chosen `Sₕ : L1' ≃ Vplus`; then `D = D₀ ⊕ D₁` chosen via the
  `Vplus × ker X₀ → F` perfect pairing
  (`vplusKerPairing_isPerfPair`); then `T := projL0 ∘ B'|_{L0'}`.
- **Fallback:** if the `d`-construction is intractable in one round,
  emit a one-helper sorry isolating that piece; close everything else.
  Plan agent picks up the helper Round 8.
- **References:** `Round 7 plan` in
  `.archon/informal/normalform_round7.md`.

### `InducedOrbitToy/NormalForm.lean :: residual_levi_extract` (line 319, Round 7)

Forward direction of `pNormalForm_residual_orbit_iso`: extract
`h : L0' ≃ L0'` from a parabolic conjugator.

- **Strategy (Option B, recommended):** `p` preserves `flagEV0 = E ⊕ V0`;
  the action descends to a quotient iso `p_E' : E' ≃ E'`. Show `p_E'`
  preserves `L0'` from the conjugation `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`
  and `kernelImage_ker`. Take `h := p_E'|_{L0'}`. Verify isometry via
  the `IsOrthogonal` conjunct of `p` plus `lambdaDualE_pairing_eq`.
- **Fallback (Option A):** rely on `parabolic_decompose` (currently
  sorry'd in Slice.lean). Adds dependence on Round 8.
- **References:** `.archon/informal/normalform_round7.md` § Tier A #2.

### `InducedOrbitToy/NormalForm.lean :: residual_levi_build` (line 348, Round 7)

Backward direction of `pNormalForm_residual_orbit_iso`: build a
parabolic from an isometry.

- **Strategy:** extend `h : L0' ≃ L0'` to `d : E' ≃ E'` via
  `IsCompl L1' L0'` (`d := id ⊕ h`). Set `p := leviGL_E S d`.
  Parabolicity follows from `leviGL_E_isParabolic`. The conjugation
  `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` reduces to verifying
  `CST Sₕ ∘ d.symm = CST Sₕ` (since `d.symm` is `id` on `L1'`)
  and `lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂` (residue of
  the isometry condition).
- Refresh stale comments at lines 344, 357 (no longer accurate after
  Round 4's Tier S #3 added `L0_paired`, `L1_isotropic_L0'`, etc.).
- **References:** `.archon/informal/normalform_round7.md` § Tier A #3.

### `InducedOrbitToy/Slice.lean :: parabolic_decompose` (line 1078, Round 8)

Levi/unipotent decomposition: every `IsParabolicElement p` factors as
`p = uD D ∘ leviGL_E d ∘ leviGL_V0 g₀`.

- **Status:** carries an explicit `/-** Gap: ... -/` comment block
  outlining the 3-step construction (~85 lines).
- **Substeps:** (a) `g₀ : V0 ≃ V0` from descent of `p` to
  `flagEV0 / flagE ≃ V0`; (b) `d : E' ≃ E'` from the dual transpose
  of `p` on `flagE = E`; (c) residual `D` from
  `parametrizeX0PlusU_uniqueness` applied to `p ∘ leviGL_E d.symm ∘ leviGL_V0 g₀.symm`.
- **References:** `.archon/informal/levi.md` § 6.6 + the `Gap` comment
  preceding `parabolic_decompose` in `Slice.lean`.

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 324, Round 8)

- **Blocker:** depends on `pNormalForm_residual_orbit_iso` being fully
  sorry-free (i.e. Round 7's NormalForm work landing). The current
  statement also lacks `Nondegenerate` / `(2 : F) ≠ 0` hypotheses;
  the prover may need to add them and reduce the two-`Sₕ` case to
  single-`Sₕ` via `pNormalForm`'s existence half. (Plan agent will
  flag the statement-shape change in Round 8 PROGRESS.md.)
- **Plan:** Round 8 (after Round 7 lands).

## Completed (carried forward)

See `task_done.md` for the full list. Highlights through Round 6:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient`.
- All `X0Geometry.lean` lemmas.
- All `Slice.lean` declarations through Round 5 + the Round 6 Levi
  machinery (`lambdaDualE`, `leviGL_E`, `leviGL_V0`, `_isParabolic`,
  `_conj_XCB`, etc. — 13 of 14 new declarations sorry-free).
- 3 of 6 original `NormalForm.lean` sorries (`kernelImage_*`).
- 3 of 3 `LocalForms.lean` sorries.
- 2 of 3 `Orbits.lean` sorries.
- All `multiplicity*` lemmas via `MultiplicityTheory`.
