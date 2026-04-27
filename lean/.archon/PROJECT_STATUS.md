# Project Status

## Overall Progress

- **Stage:** prover (Round 6 complete; **5** declaration-use sorries — additive +1
  expected for the deferred `parabolic_decompose`).
- **Build state:** `lake build` succeeds (green, end of session 8 / Round 6).
- **Custom axiom declarations:** 0. All 14 newly-added Levi declarations in
  `Slice.lean` (`lambdaDualE`, `lambdaDualE_pairing_eq`, `lambdaDualE_id`,
  `lambdaDualE_comp`, `leviGL_E`, `leviGL_V0`, `leviGL_E_apply`,
  `leviGL_V0_apply`, `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse`,
  `leviGL_E_isParabolic`, `leviGL_V0_isParabolic`, `leviGL_E_conj_XCB`,
  `leviGL_V0_conj_XCB`) depend only on `[propext, Classical.choice, Quot.sound]`,
  audited via `/tmp/check_axioms_slice.lean` + `lake env lean`.
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → **5 (end of session 8)**.
  Net session 8: **+1** declaration sorry — additive only, the deferred
  `parabolic_decompose` per Round 6 design (PROGRESS.md lines 122–126
  permit up to one extra `sorry` for this helper). All other Round 5 sorries
  unchanged in count and location.

## Solved this session (session 8 / Round 6)

- **`Slice.lean :: lambdaDualE` infrastructure (4 declarations)** —
  `lambdaDualE`, `lambdaDualE_pairing_eq`, `lambdaDualE_id`,
  `lambdaDualE_comp`. Mirrors the existing `Cdual` construction at Slice.lean
  line 71 via `S.lambda.toPerfPair.symm` + `g.dualMap`. The `_comp` proof
  needed a `show` step to convert `(g₁ ∘ₗ g₂) e` opaque-composition form to
  nested-application `g₁ (g₂ e)` before `rw [lambdaDualE_pairing_eq]` could
  pattern-match.
- **`Slice.lean :: leviGL_E + leviGL_V0` block-diagonal embeddings (4
  declarations)** — `leviGL_E`, `leviGL_V0`, `leviGL_E_apply`,
  `leviGL_V0_apply`. Direct block-matrix definitions via
  `LinearMap.inl`/`inr`/`fst`/`snd`. `leviGL_V0` does NOT bundle the
  isometry hypothesis (avoids session-7 subtype-wrapping anti-pattern).
- **`Slice.lean :: _symm_inverse` lemmas (2 declarations)** —
  `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse`. `Prod.mk.injEq`
  component-split + `lambdaDualE_comp_symm` for E-block, `simp` for the
  rest. `d.symm.symm = d` `rfl` for `LinearEquiv` halves inverse-pair work.
- **`Slice.lean :: _isParabolic` lemmas (2 declarations)** —
  `leviGL_E_isParabolic`, `leviGL_V0_isParabolic`. 4-conjunct unfolds
  (`IsUnit ∧ Submodule.map = ∧ Submodule.map = ∧ IsOrthogonal`) via
  `Units.mkOfMulEqOne` + `le_antisymm` + `simp [SliceSetup.ambientForm,
  LinearMap.mk₂_apply]` + `lambdaDualE_pairing_eq`.
- **`Slice.lean :: _conj_XCB` lemmas (2 declarations)** —
  `leviGL_E_conj_XCB`, `leviGL_V0_conj_XCB`. Component-split via
  `Prod.mk.injEq`; E-component uses the new private helper
  `lambdaDualE_Cdual`. The V0 lemma needed an **asymmetric** `hgC` form
  (first arg CoeFun, second arg LinearMap-coerced) to match the asymmetric
  output of `Cdual_pairing` after `comp_apply` rewrites.

## Solved earlier (sessions 1–7, carry-forward)

(See `proof-journal/sessions/session_7/summary.md` and earlier sessions
for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4).
- `NormalForm.lean :: kernelImage_dim`, `kernelImage_ker`, `kernelImage_im`,
  `isUnit_uD`, `map_uD_eq_of_le`, `pNormalForm` (sessions 3–7).
- `Basic.lean :: SliceSetup`, `UnipotentRadical` (Tier S #2, #3 — session 6).
- `Slice.lean :: parametrizeX0PlusU_existence`, `parametrizeX0PlusU_mem`,
  `uD_isParabolic` (sessions 5–6).
- `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent`,
  `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`, `inducedOrbits`,
  `main` (sessions 3 + 6).

## Remaining sorries (5 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `NormalForm.lean` | 195 | `pNormalForm_witnesses` (private helper) | A | Slice Levi infra now landed. **Unblocked for Round 7.** Estimated ~50 lines (uses `leviGL_E_conj_XCB` + `uD_conj_XCB`). |
| `NormalForm.lean` | 319 | `residual_levi_extract` (private helper) | A | Slice Levi infra now landed. Choose Option B (~40 lines via `parametrizeX0PlusU_uniqueness` + `leviGL_E_isParabolic`) over Option A (close `parabolic_decompose` first, ~95 lines). **Unblocked for Round 7.** |
| `NormalForm.lean` | 348 | `residual_levi_build` (private helper) | A | Slice Levi infra now landed. Use `leviGL_E S d` directly. **Unblocked for Round 7.** Estimated ~40 lines. Refresh stale comments at lines 344, 357 (`L0_isotropic` references) as part of edit pass. |
| `Slice.lean` | 1078 | `parabolic_decompose` (deferred) | (Round 6 deferred) | Hardest piece of Round 6 (3 sub-constructions: g₀ extraction via quotient descent, (d⁻¹)^∨ from flagE action, residual D via `parametrizeX0PlusU_uniqueness`). 24-line gap explanation in-file. **Optional for Round 7** (Option A) or skip permanently if not needed downstream. |
| `Orbits.lean` | 358 + 376 | `sIndependenceAndOrbitCriterion` (2 internal scoped sorries, 1 declaration) | A (deferred) | unblocks once `pNormalForm_residual_orbit_iso` is sorry-free; also needs added hypotheses (`Nondegenerate`, `(2 : F) ≠ 0`) and `Sₕ`-equality refactor — **Round 8**. |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 7 list.)

- **(NEW session 8) `show` to expose composed-application terms before
  `rw` perfect-pairing identities.** When the goal has `(f ∘ₗ g) e` and
  `rw` of a perfect-pairing lemma fails to match, prepend `show ... f
  (g e) = ...` to surface the nested-application form. Used to fix
  `lambdaDualE_comp`.
- **(NEW session 8) Asymmetric isometry-hypothesis form for `_conj_XCB`-style
  proofs.** Match the asymmetric form `Cdual_pairing` produces — first arg
  CoeFun (`g v`), second arg LinearMap-coerced (`(g : V0 →ₗ[F] V0) (C e'')`).
  Symmetric `hgC` cannot match either form alone. The two FunLike instances
  coexist; reflexive equality doesn't help syntactic pattern-matching.
- **(NEW session 8) `d.symm.symm = d` is `rfl` for `LinearEquiv`** —
  enables `leviGL_E_symm_inverse S d.symm` for the other-direction inverse
  for free, halving inverse-pair proofs.
- **(NEW session 8) Block-matrix component-split closure pattern.**
  `refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩`
  for any `Module.End F (E × V0 × E')` identity, then close each component
  individually. Used 4× in Round 6's Levi proofs.
- **(NEW session 8) `leviGL_V0` no-bundle definition pattern.** Isometry
  hypothesis is passed at consumer sites (`leviGL_V0_isParabolic`,
  `leviGL_V0_conj_XCB`), not bundled in the def. Sidesteps session-7
  subtype-wrapping anti-pattern.
- **(NEW session 8) `lean_run_code` `#check` for known-name API
  verification** is faster than `lean_loogle` / `leansearch` when the
  informal doc names the lemma. Workflow: read `informal/levi.md` `-- Hint:`
  → `#check` → write proof. Round 6 prover did this 3× and never invoked
  the search tools — still landed 14 sorry-free declarations.
- **(NEW session 8) `#print axioms` syntax detail.** Drop the `@` prefix:
  `#print axioms lambdaDualE` works; `#print axioms @lambdaDualE` fails
  with `Unknown constant axioms`.

(Earlier patterns from sessions 1–7 unchanged; see
`proof-journal/sessions/session_7/summary.md` for the complete list.)

### Known Blockers (do not retry)

- **`parabolic_decompose`** (Slice.lean line 1078): hardest piece of
  Round 6. Three substantive sub-constructions required (a-c per
  `informal/levi.md §6.6`, ~85 lines total). Deferred; **NOT required**
  for Round 7 if the consumer takes Option B (direct
  `parametrizeX0PlusU_uniqueness` + `leviGL_E_isParabolic`). Optional for
  Round 7+.
- **Round 8 work** (`sIndependenceAndOrbitCriterion`): blocked on
  Round 7's `pNormalForm_residual_orbit_iso` plus added hypotheses
  (`Nondegenerate`, `(2 : F) ≠ 0`) and `Sₕ`-equality refactor.

### Stale comment hygiene

- `NormalForm.lean` lines 344, 357 still contain comment refs to the
  now-removed `L0_isotropic` field (replaced by Lagrangian quartet in
  session 6). They compile cleanly (inside docstrings/comments) but
  should be refreshed as part of the Round 7 `residual_levi_build` edit
  pass. (Carry-forward from session 7.)

## Last Updated

2026-04-28T00:00:00Z (end of session 8 / Round 6)
