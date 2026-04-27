# Prover Backlog

`lake build` is green (verified 2026-04-28, end of Round 7); 0 custom
axioms; **3 declaration-use `sorry` warnings**:

- `InducedOrbitToy/NormalForm.lean:203` — `pNormalForm_witnesses`
  body (Tier A, **Round 8 primary**). Single isolated `sorry` at
  body-line 216; declaration line is 203. Body docstring (lines 188–202)
  outlines the four-step plan.
- `InducedOrbitToy/Slice.lean:1078` — `parabolic_decompose`
  (deferred from Round 6, optional Tier A for Round 8). 24-line
  `Gap:` comment block in-file (lines 1062–1077) describes the
  three sub-constructions.
- `InducedOrbitToy/Orbits.lean:324` — `sIndependenceAndOrbitCriterion`
  (Tier A, **Round 8 secondary**). Two scoped `sorry`s at body
  lines 358 (forward) and 376 (reverse). Now structurally
  unblocked because `pNormalForm_residual_orbit_iso` is sorry-free.

## Tier S — plan-agent statement / structural fixes

(Tier S #1 through #5 — all resolved in earlier rounds; see
`task_done.md`. Round 7 landed the Levi-factor restructure of
`pNormalForm_witnesses`.)

## Tier A — provable now (Round 8)

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` body (line 216, Round 8)

The Tier S #5 signature restructure already landed in Round 7. Only the
body remains — a single isolated `sorry`.

- **Strategy** (recommendations.md, Option A): four-step plan baked
  into the body docstring at lines 188–202.
  1. Build `(Sₕ, d)` from `_hRank : rank Cbar = c` via
     `LinearEquiv.ofBijective` on `LinearMap.codRestrict`. Lift
     L0'-iso to `d : E' ≃ E'` by `Submodule.prodEquivOfIsCompl`
     (mirrors `extendL0'IsoToE'` from Round 7).
  2. Apply `leviGL_E_conj_XCB` to rewrite the LHS into normal form.
  3. Build `D` so `X0 ∘ D = C' - CST Sₕ` lands in `range X0`.
  4. Combine via `uD_conj_XCB` + `parametrizeX0PlusU_uniqueness`
     + `uD_neg_inverse`.
- **Stop condition:** if Step 1 (the d-construction) proves
  intractable due to `Module.finrank` plumbing, the prover may
  extract Step 1 as a separate `private def` skeleton and continue
  with Steps 2–4 against an opaque `(Sₕ, d)`. The sorry localises
  to the d-construction helper.
- **Estimated effort:** ~150 lines.
- **References:** docstring at NormalForm.lean lines 175–202;
  `.archon/informal/normalform_round7.md` § Tier A #1; Round 7
  recommendations at `proof-journal/sessions/session_9/recommendations.md`.

### `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (line 324, Round 8)

Now structurally unblocked because `pNormalForm_residual_orbit_iso`
is sorry-free.

- **Reverse direction (line 376):** direct via
  `pNormalForm_residual_orbit_iso`. Apply to lift
  `_h : L0' ≃ₗ[F] L0'` to a P-element `p` with
  `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p`. Use parabolic ⊂ isometry group
  to membership-witness `p` for `GOrbit`. Mutual inclusion of
  orbits.
- **Forward direction (line 358):** From `_hg : IsometryEnd S _g`
  and conjugation equation `_hyeq`, show `_g ∈ P` (i.e.
  `IsParabolicElement S _g`). Two routes:
  - **Route A (use `parabolic_decompose`):** if the parallel
    Slice prover lands `parabolic_decompose`, simply apply it to
    `_g`. Direct.
  - **Route B (workaround, recommended for Round 8 independence):**
    direct flag-stability argument from `_hg` + conjugation.
    See session 9 recommendations.md § Option B for the sketch.
- **Hypothesis additions needed.** Both directions need
  `(Nondegenerate, (2 : F) ≠ 0, Sₕ₁ = Sₕ₂)` added to the
  `sIndependenceAndOrbitCriterion` statement. The session-9
  prover-recommendation prefers **option (b)**: strengthen
  `pNormalForm_residual_orbit_iso` to absorb them, keeping
  `sIndependenceAndOrbitCriterion`'s public statement clean.
  The Round 8 prover may pick either route; flag the choice in
  the task report.
- **Stale comments.** Lines 357 (and any `L0_isotropic` ref) are
  stale Round-4 carry-forward — refresh during the edit pass.
- **Estimated effort:** ~80 lines (forward + reverse combined).
- **References:** `proof-journal/sessions/session_9/recommendations.md`
  § Option B; `informal/orbits.md`.

### `InducedOrbitToy/Slice.lean :: parabolic_decompose` (line 1078, Round 8 optional)

Deferred from Round 6 with documented `Gap:` comment block.

- **Status:** carries an explicit `/- Gap: ... -/` comment block
  outlining the 3-step construction (~85 lines).
- **Substeps:**
  - **Step A (g₀ extraction):** action of `p` on
    `flagEV0 / flagE ≃ V0`.
  - **Step B (`(d⁻¹)^∨` extraction):** action of `p` on
    `flagE = E`.
  - **Step C (residual D):** apply
    `parametrizeX0PlusU_uniqueness` to
    `p ∘ leviGL_E d.symm ∘ leviGL_V0 g₀.symm`.
- **References:** `.archon/informal/levi.md` § 6.6; the `Gap:`
  comment immediately above `parabolic_decompose` in Slice.lean.

## Completed (carried forward)

See `task_done.md` for the full list. Highlights through Round 7:

- All 6 `Basic.lean` definitions and `c_eq_finrank_quotient`.
- All `X0Geometry.lean` lemmas.
- All `Slice.lean` Round 6 Levi machinery: 13 of 14 new
  declarations sorry-free (`lambdaDualE`, `leviGL_E`, `leviGL_V0`,
  `_isParabolic`, `_conj_XCB`, etc.) — only `parabolic_decompose`
  carries a sorry.
- 5 of 6 original `NormalForm.lean` sorries closed
  (`kernelImage_*`, `residual_levi_extract`, `residual_levi_build`)
  + Tier S #5 signature restructure landed.
- 3 of 3 `LocalForms.lean` sorries.
- 2 of 3 `Orbits.lean` sorries.
- All `multiplicity*` lemmas via `MultiplicityTheory`.
- Public consumer `pNormalForm_residual_orbit_iso` is sorry-free
  (Round 7).
