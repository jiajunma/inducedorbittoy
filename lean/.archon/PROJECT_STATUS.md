# Project Status

## Overall Progress

- **Stage:** prover (Round 8 complete; **3** declaration-use sorries — 0 net change from Round 7).
- **Build state:** `lake build` succeeds (green, end of session 10 / Round 8).
- **Custom axiom declarations:** 0. Public-theorem axiom audit:
  - `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`, `pNormalForm_residual_orbit_iso`, `kernelImage_*`: `[propext, Classical.choice, Quot.sound]` — CLEAN.
  - `sIndependenceAndOrbitCriterion`, `main`, `pNormalForm`: depend transitively on `sorryAx` via newly-introduced private helpers (expected per Round 8 plan fallback).
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → 5 (end of session 8) → 3 (end of session 9) → **3 (end of session 10)**.
  Net session 10: **0** declaration sorries. Plan target was 3 → 0; achieved a structural reorganisation with no net closure. Each remaining sorry is now isolated to a focused private helper carrying a documented Gap.

## Round 8 work (session 10) — structural reorganisation, no net closure

### NormalForm.lean — `pNormalForm_witnesses` deferred via single isolated helper

- **Added `pNormalForm_witnesses_aux` (line 197)** — single private helper holding the residual sorry. Comprehensive Gap docstring (lines 152–196) walking through all four steps of the blueprint proof.
- **Refactored `pNormalForm_witnesses` body** (line 264) — replaced bare `sorry` with `exact pNormalForm_witnesses_aux S _hNondeg _hChar C B _hB _hRank`. The body is now sorry-free.
- **Net effect:** declaration count unchanged (1 → 1); body of `pNormalForm_witnesses` is now sorry-free.
- **Key finding:** `dim L1' = c` is needed for `Sₕ : L1' ≃ Vplus` and is **not enforceable from `SliceSetup` alone** (counterexamples: `L1' = E', L0' = 0`). Round 9 may need to add a hypothesis.

### Orbits.lean — `sIndependenceAndOrbitCriterion` body sorry-free; helper carries 2 sorries

- **Signature change:** `(Sₕ₁ Sₕ₂)` → single `(Sₕ : S.L1' ≃ₗ[F] S.Vplus)` (option (i)); added `(hNondeg, hChar)` hypotheses (option (a)). Cascaded into `main`.
- **Reverse direction (line 559) — RESOLVED, sorry-free.** Two-line proof via `pNormalForm_residual_orbit_iso` (←) + new helper `GOrbit_eq_of_isometry_conj`.
- **Forward direction (line 519) — RESOLVED in body, helper carries sorry.** Four-step plan: extract orbit witness `g`, lift via `isParabolicElement_ringInverse_of_orbit_witness`, derive conjugation via `Ring.inverse_mul_cancel`, apply `pNormalForm_residual_orbit_iso` (→).
- **New helper lemmas:** `IsOrthogonal_mul`, `IsOrthogonal_ringInverse`, `GOrbit_eq_of_isometry_conj`, `isParabolicElement_ringInverse_of_orbit_witness`. The last carries 2 scoped sorries on flag-stability conjuncts.
- **Net effect:** declaration count unchanged (1 → 1); body sorry-free; sorries pushed into focused private helper.

### Slice.lean — `parabolic_decompose` partial; mathematical statement-level gap identified

- **~460 lines of new constructive content** added to the body: `pinv` extraction, flag-preservation transfer, diagonal-block linear maps (`pE_fn`, `pV0_fn`, `pE'_fn`), bijectivity via round-trip identities, `LinearEquiv` packaging, V0-isometry, cross-pairing identity. All sorry-free.
- **Final assembly remains sorry'd at line 1572.** A direct attempt to close the goal reveals the statement is **strictly narrower than the full Levi decomposition**.
- **Mathematical observation:** A general parabolic isometry decomposes as `(uD D + B') ∘ leviGL_E d ∘ leviGL_V0 g` for some skew `B' : E' →ₗ[F] E`; the current `uD D` definition fixes `B' = 0`. The statement signature is missing a `B'` parameter.
- **Net effect:** declaration count unchanged (1 → 1); body has substantial new constructive content; statement-level gap documented in-file (lines 1088–1107).

## Solved earlier (sessions 1–9, carry-forward)

(See `proof-journal/sessions/session_9/summary.md` for the immediate-prior round and earlier sessions for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4).
- `NormalForm.lean :: kernelImage_dim`, `kernelImage_ker`, `kernelImage_im`, `isUnit_uD`, `map_uD_eq_of_le`, `pNormalForm` (sessions 3–7), `residual_levi_extract`, `residual_levi_build`, `pNormalForm_residual_orbit_iso`, `XST_apply`, `extendL0'IsoToE'` (session 9 / Round 7).
- `Basic.lean :: SliceSetup`, `UnipotentRadical` (Tier S #2, #3 — session 6).
- `Slice.lean :: parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`, `parametrizeX0PlusU_mem`, `uD_isParabolic` (sessions 5–6).
- `Slice.lean ::` Levi-action machinery (14 declarations) — closed in session 8.
- `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent`, `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`, `inducedOrbits`, `main` (sessions 3 + 6; `main` signature updated in session 10).

## Remaining sorries (3 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `NormalForm.lean` | 197 | `pNormalForm_witnesses_aux` (private helper) | A | **Single isolated sorry, four-step Gap docstring at lines 152–196.** Round 9 primary objective. ~200–300 lines estimated. Body of `pNormalForm_witnesses` (line 264) is now sorry-free; sorry isolated to this helper. **Risk:** `dim L1' = c` may need to be added as a hypothesis. |
| `Slice.lean` | 1109 | `parabolic_decompose` (partial body, statement gap) | (Round 6 deferred) | ~460 lines of new constructive content; **statement-level gap identified** (uD missing B' parameter). Round 9 should NOT attempt to close this without first deciding on the (a) generalise-uD vs (b) narrow-statement question. **Defer to polish stage.** |
| `Orbits.lean` | 438 | `isParabolicElement_ringInverse_of_orbit_witness` (private helper) | A (deferred) | 2 scoped sorries on flag-stability conjuncts (lines 453, 456). Body of `sIndependenceAndOrbitCriterion` reverse direction is sorry-free; forward direction passes through this helper. Route B (direct slice-transversality via `parametrizeX0PlusU_uniqueness`) is tractable for Round 9. |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 9 list.)

- **(NEW session 10) `noncomm_ring` for `Module.End F V` associativity.** Where commutative `ring` fails, `noncomm_ring` closes any associativity goal on module endomorphisms. Essential pattern. Future provers should prefer it over manual `mul_assoc` chains for `Ring.inverse` algebra.

- **(NEW session 10) `Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g` (units).** Derive via uniqueness from `(g * Ring.inverse p) * (p * Ring.inverse g) = 1` plus `Ring.inverse_mul_cancel` (LHS) / `Ring.mul_inverse_cancel` (RHS). Close associativity with `noncomm_ring`.

- **(NEW session 10) Orbit equality from single conjugating isometry — flag-stability NOT needed.** New `GOrbit_eq_of_isometry_conj` helper in Orbits.lean exposes only the unit + orthogonal data. Both inclusions transit through `g ↦ g * Ring.inverse p` (or dual). Reusable for any future orbit-equality argument.

- **(NEW session 10) `Ring.inverse` for orbit/conjugation reasoning.** Pattern: `Ring.inverse_mul_cancel _ hgU` (LHS), `Ring.mul_inverse_cancel _ hgU` (RHS), `IsUnit.ringInverse` (unit preservation). No division-ring needed.

- **(NEW session 10) Diagonal-block extraction from `_hpUnit.unit.inv` for parabolic isometries.** When `p` preserves a flag, build inverse maps `pE_inv`, `pV0_inv`, `pE'_inv` from `pinv := _hpUnit.unit.inv` and prove bijectivity via round-trip identities (3-step calc chains). General-purpose for any flag-preserving invertible endomorphism.

- **(NEW session 10) `LinearEquiv` via anonymous-constructor.** `{ linear_map with invFun := inv, left_inv, right_inv }` is cleaner than `LinearEquiv.ofBijective` when both `LinearMap` and explicit inverse are in scope.

- **(NEW session 10) Forward calc with reverse-direction `rw`.** When `rw [eq]` doesn't fire on a goal with the substitution on the LHS, restructure as forward calc starting from the desired identity. Concrete: `(e, 0, 0) = p (pinv (e, 0, 0)) = p (pE_inv e, 0, 0) = (pE_fn (pE_inv e), 0, 0)` works where the reverse-direction `rw [pE_inv_eq]` does not fire.

- **(NEW session 10) Statement-level gap analysis.** When a proof is repeatedly blocked at the same step despite multiple approaches, examine whether the *statement* is provable. The `parabolic_decompose` gap (`uD D` should be `uD D + B'`) is a model example. **Document the gap analysis directly in the in-file docstring** so future provers don't re-discover it.

- **(NEW session 10) Cross-file parallel dispatch with line-range partitioning.** Plan agent's careful partitioning (NormalForm 190–230, Orbits 292–630, Slice 1065–1574) enabled three concurrent provers with clean end-of-round merge. Mid-round build breakage is acceptable; end-of-round merge must be green.

(Earlier patterns from sessions 1–9 unchanged; see `proof-journal/sessions/session_9/summary.md` and PROGRESS.md "Reusable Gotchas" list for the complete carryforward.)

### Known Blockers (do not retry)

- **`parabolic_decompose` (Slice.lean line 1109) with current signature.** **Mathematical gap identified — statement is too narrow.** A general parabolic isometry has form `(uD D + B') ∘ leviGL_E d ∘ leviGL_V0 g`; current statement fixes `B' = 0`. Round 9 should NOT assign this; defer to polish stage with a refactor decision (generalise `uD` vs narrow the statement).

- **`pNormalForm_witnesses_aux` (NormalForm.lean line 197) with bare `SliceSetup` hypotheses.** `dim L1' = c` may not be derivable; Round 9 may need to add a hypothesis. Counterexamples confirm this is a real risk.

### Stale comment hygiene

- `NormalForm.lean` lines 344, 357 still contain comment refs to the now-removed `L0_isotropic` field (replaced by Lagrangian quartet in session 6). They compile cleanly (inside docstrings/comments) but should be refreshed during the next NormalForm edit pass. (Carry-forward from sessions 7–9.)

## Last Updated

2026-04-27T22:00:00Z (end of session 10 / Round 8)
