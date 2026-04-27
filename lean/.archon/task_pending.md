# Prover Backlog

`lake build` is green (verified 2026-04-27); 0 custom axioms; 8
declaration-use `sorry` warnings remain. Remaining sorries split into
four tiers — see `PROGRESS.md` for the full plan and round assignments.

## Tier A — provable now, no upstream changes needed

### `InducedOrbitToy/NormalForm.lean :: pNormalForm` (line 167)
- **Assigned this round** (Round 2).
- Strategy: construct `Sₕ : L1' →ₗ[F] Vplus` from `_hRank` via
  `Cbar`/`VplusEquivQuotientRange`; pick `D : E' →ₗ[F] V0` to absorb the
  `B|_{L1'}` block; set `T := projL0' (B - Cdual D ∘ C)` and verify
  `IsSkewT`; set `p := uD S D` and use `uD_conj_XCB`.
- Caveat: the `IsAdjointPair B B p p` conjunct of `IsParabolicElement p`
  is the Tier D bug. Leave a single scoped internal `sorry` for *only*
  that conjunct and document the upstream blocker — do not try to prove
  a false statement.

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_residual_orbit_iso` (line 199)
- **Assigned this round** (Round 2).
- Strategy: bidirectional iff. (→) extract Levi factor `h : L0' ≃ₗ L0'`
  from the parabolic; show `BT T₂ (h u) (h v) = BT T₁ u v` via
  `XST_apply`. (←) build `p` as `(h⁻¹)^∨ ⊕ id ⊕ h` on the block
  decomposition; reduce conjugation to diagonal blocks via `XST_apply`
  and the isometry hypothesis.
- Same caveat re `IsAdjointPair B B p p` as above.

## Tier A (deferred to next round)

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 242)
- **Not assigned this round.** Depends on `pNormalForm_residual_orbit_iso`
  landing first (this round's Tier A target).
- Body currently has 2 scoped `sorry`s (lines 260, 268) for the two iff
  directions; full plan documented in `task_results/Orbits.lean.md` from
  Round 1.
- Round 3 work.

## Tier B — needs `Basic.lean :: DualTransposeData` refactor

### `InducedOrbitToy/X0Geometry.lean :: sDual_restrict_ker_isIso` (line 206)
- **Not assigned this round.** Body has 2 scoped `sorry`s (lines 261, 264):
  `h_in_L1 : Tdual w ∈ L1` and `h_dim_L1 : finrank L1 = finrank ker S.X0`.
- Both unprovable from current `DualTransposeData`. Resolution:
  enrich `DualTransposeData` (in `Basic.lean`) with two new fields,
  `L1_le : range Tdual ≤ L1` and `finrank_L1_eq : finrank L1 = finrank (ker X0)`.
  Once those land, the existing proof skeleton in `X0Geometry.lean` closes
  with no further edits.

## Tier C — needs `Basic.lean :: SliceSetup` refactor

### `InducedOrbitToy/NormalForm.lean :: kernelImage_ker` (line 302)
### `InducedOrbitToy/NormalForm.lean :: kernelImage_im` (line 397)
- **Not assigned this round.** Both require:
  - Lagrangian condition `λ(L1, L0') = 0` exposed in `SliceSetup`,
  - `Sₕ` typed as `LinearEquiv` (not `LinearMap`).
- Plan: add `SliceSetup.lagrangian` field; tighten the theorem signatures
  to consume `LinearEquiv` (or take it as an explicit hypothesis).

## Tier D — autoformalization statement bugs

### `InducedOrbitToy/Slice.lean :: parametrizeX0PlusU_existence` (line 232)
- **Do not retry until upstream fix lands.** `Basic.lean :: UnipotentRadical`
  is too loose: it does not enforce skew-adjointness w.r.t. `S.ambientForm`.
  The autoformalized existence claim is mathematically false in this
  generality.
- Fix: tighten `UnipotentRadical` in `Basic.lean` to be the Lie subalgebra
  that *also* preserves `S.ambientForm`. Then `parametrizeX0PlusU_existence`
  becomes provable.
- Body currently has 2 scoped `sorry`s with the partial construction
  (`C := projV0 ∘ Y ∘ inE'`, `B := projE ∘ Y ∘ inE'`).

### `InducedOrbitToy/Slice.lean :: uD_isParabolic` (line 391)
- **Do not retry until upstream fix lands.** The
  `IsAdjointPair S.ambientForm S.ambientForm (uD D) (uD D)` conjunct
  asserts self-adjointness of `uD`, which is false in general. The
  blueprint asserts `uD` is an *isometry* — equivalent to
  `IsAdjointPair S.ambientForm S.ambientForm (uD D) (uD (-D))`.
- Fix (statement-level, requires plan-agent directive): change the
  autoformalized statement to use `uD (-D)` on the right of `IsAdjointPair`.
  Body has 1 scoped `sorry` for the impossible conjunct; flag-preservation
  conjuncts already proved.

## Completed (carried forward)

See `task_done.md` for the full list. Highlights:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient`.
- All 7 `X0Geometry.lean` lemmas except `sDual_restrict_ker_isIso`.
- 7 of 9 `Slice.lean` sorries (incl. `Cdual`, `uD`, `uD_conj_XCB`).
- 1 of 5 `NormalForm.lean` sorries (`kernelImage_dim`).
- 3 of 3 `LocalForms.lean` sorries (typeclass-projection refactor).
- 2 of 3 `Orbits.lean` sorries (`inducedOrbits`, `main`).
- All `multiplicity*` lemmas via `MultiplicityTheory`.
