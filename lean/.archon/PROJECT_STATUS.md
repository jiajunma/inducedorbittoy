# Project Status

## Overall Progress

- **Stage:** prover (round 4 complete; **6** declaration-use sorries remain).
- **Build state:** `lake build` succeeds (green, end of session 6 / Round 4).
- **Custom axiom declarations:** 0. All sorry-free public theorems depend
  only on `[propext, Classical.choice, Quot.sound]`. `sorryAx` appears
  only on declarations that still embed an explicit `sorry` (or
  transitively call one — currently `main` via `sIndependenceAndOrbitCriterion`).
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → **6 (end of session 6)**.
  Net session 6: **−1** declaration sorry — the Tier S #2 + #3 cascade
  closed `parametrizeX0PlusU_existence` (formerly 2 internal scoped
  sorries inside one declaration).

## Solved this session (session 6 / Round 4)

- **`Basic.lean :: SliceSetup`** — Tier S #3 structural fix landed.
  Replaced inconsistent `L0_isotropic` field with the Lagrangian quartet
  (`L0_paired`, `L1_isotropic_L0'`, `L0_isotropic_L1'`); docstring
  rewritten. Audit confirmed no code consumers (only comment refs in
  `NormalForm.lean` lines 344/357 — stale, compile cleanly).
- **`Basic.lean :: UnipotentRadical`** — Tier S #2 structural fix landed.
  Carrier predicate gains 4th conjunct `IsSkewAdjoint S.ambientForm f`;
  closure proofs (`zero_mem'`, `add_mem'`, `smul_mem'`) extended with
  `linear_combination`-based discharges of the new conjunct.
  Docstring rewritten (`𝔲 = 𝔭 ∩ 𝔤`).
- **`Slice.lean :: parametrizeX0PlusU_existence`** — both internal
  scoped sorries (formerly lines 256, 294) closed. New 4-tuple
  destructure of `_hY` exposes `hSkewY : IsSkewAdjoint S.ambientForm Y`,
  which discharges (a) the `IsSkewB B` conjunct via `hSkewY (0,0,u) (0,0,v)`
  + `linear_combination`, and (b) the E-component equality via auxiliary
  hypothesis `(Y (0,v,0)).1 = Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v` proved
  through perfect-pairing left-injectivity. File is now sorry-free.
- **`Slice.lean :: parametrizeX0PlusU_mem`** — cascade for tightened
  `UnipotentRadical`. `refine ⟨?_, ?_, ?_⟩ → refine ⟨?_, ?_, ?_, ?_⟩`;
  new IsSkewAdjoint case discharged via new helper
  `XCB_sub_X0Lift_apply` + `Cdual_pairing_eq` + ε-symmetry +
  `linear_combination`.
- **`Orbits.lean :: XCB_sub_X0Lift_mem_unipotent`** — Option A: signature
  gains `(hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S))`;
  4th conjunct discharged by passing `hskew` directly.
- **`Orbits.lean :: XST_sub_X0Lift_mem_unipotent`** — full proof rewrite
  via four new private helpers (`BST_apply`, `projL1'_add_projL0'_eq`,
  `lambda_L0_eq_lambda_L0_projL0'`, `IsSkewB_BST`) plus `Cdual_pairing_eq`
  + ε-symmetry + `linear_combination`.
- **`Orbits.lean :: XST_mem_O0PlusU` / `inducedOrbits` / `main`** — call
  sites updated to thread `hNondeg : S.formV0.Nondegenerate` and
  `hT : S.IsSkewT T` through the new signatures. Renamed previously-unused
  `_hNondeg`, `_hT` to bare `hNondeg`, `hT`.

## Solved earlier (sessions 1–5, carry-forward)

(See `proof-journal/sessions/session_5/summary.md` and earlier sessions
for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4).
- `NormalForm.lean :: kernelImage_dim`, `isUnit_uD`, `map_uD_eq_of_le`
  (sessions 3–4).
- `NormalForm.lean :: pNormalForm` (session 5 — IsOrthogonal conjunct
  closed via Tier S #1).
- `Orbits.lean :: inducedOrbits`, `main` (session 3 + Round 4 cascade).
- 7 of 9 sorries in `Slice.lean` closed in sessions 3–5;
  `parametrizeX0PlusU_existence` closed this round.
- `uD_isParabolic` (session 5 — Tier S #1 IsAdjointPair conjunct).

## Remaining sorries (6 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `NormalForm.lean` | 210 | `pNormalForm_witnesses` (private helper) | A | needs Levi-action machinery added to `Slice.lean` (additive, ≈60–100 lines) — Round 6 |
| `NormalForm.lean` | 330 | `residual_levi_extract` (private helper) | A | needs Levi machinery + Levi-decomposition lemma `parabolic_decompose` — Round 6 |
| `NormalForm.lean` | 363 | `residual_levi_build` (private helper) | A | Tier S #3 dependency now satisfied; remaining blocker is Levi machinery — Round 6 |
| `NormalForm.lean` | 537 + 543 | `kernelImage_ker` (2 internal scoped sorries, 1 declaration) | C | Tier S #3 dependency now satisfied; remaining blocker is Tier S #4 (Sₕ retyped as `LinearEquiv`) — **Round 5 next** |
| `NormalForm.lean` | 595 | `kernelImage_im` | C | Tier S #3 dependency now satisfied; same Tier S #4 blocker — **Round 5 next** |
| `Orbits.lean` | 358 + 376 | `sIndependenceAndOrbitCriterion` (2 internal scoped sorries, 1 declaration) | A (deferred) | unblocks once `pNormalForm_residual_orbit_iso` is sorry-free; also needs added hypotheses (`Nondegenerate`, `(2 : F) ≠ 0`) and `Sₕ`-equality refactor — Round 7 |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 5 list.)

- **(NEW session 6) `linear_combination` over generic `Field F`.** Never
  use `linarith` outside ordered fields; use `linear_combination h₁ + h₂`
  (or coefficients) for linear-equality goals. Pattern reappeared in
  3 distinct sub-proofs this round (Basic `add_mem'`, Slice `IsSkewB` /
  E-component, Orbits `XST_sub_X0Lift_mem_unipotent`).
- **(NEW session 6) Vector equality via perfect-pairing left-injectivity.**
  Reduce `(Y v).1 = Cdual C v` to a per-test-vector scalar identity via
  `S.paired.isPerfect.1`, then close with `linear_combination` over a
  skew-adjointness instantiation. Generalises to any "skew-adjointness
  forces a block to equal a `Cdual`" argument.
- **(NEW session 6) Cross-isotropy collapse via Lagrangian decomposition.**
  For `x : S.L0`, `λ(↑x, v) = λ(↑x, ↑(projL0' v))` via
  `projL1'_add_projL0'_eq` + `S.L0_isotropic_L1'`. Symmetric for L1.
  Likely directly reusable in `kernelImage_*` (Round 5).
- **(NEW session 6) Position-targeted rewriting with `conv_lhs`.** Bare
  `rw [← lemma]` rewrites every occurrence; use `conv_lhs => rw [...]`
  or `nth_rewrite` to scope.
- **(NEW session 6) `LinearMap.add_apply` cannot fire after `map_add`.**
  After `map_add` the residual `+` is in the codomain, not the domain.
  Drop redundant rewrites from `rw` chains.
- **(NEW session 6) `Submodule.IsCompl.projection_*` API.**
  `Submodule.IsCompl.projection_add_projection_eq_self` +
  `Submodule.IsCompl.projection_apply` is the right Mathlib API for
  `L₁ ⊕ L₀ = E` decompositions; the legacy `linearProjOfIsCompl_add_…`
  does not exist (leansearch false positive).
- **(NEW session 6) Audit-before-structural-edit.** `grep -rn '<field>'`
  before removing or renaming a structure field; comment-only refs are
  safe to ignore (refresh later); code refs force escalation.
- **(NEW session 6) ε-symmetry + ε² = 1 cancellation skeleton.**
  ```lean
  have hε := S.epsSymm
  have hε2 : S.eps * S.eps = 1 := by rcases S.epsValid with h | h <;> simp [h]
  linear_combination ... + (...) * hε2
  ```
  Used twice this round (Slice `parametrizeX0PlusU_mem`, Orbits
  `XST_sub_X0Lift_mem_unipotent`).

(Earlier patterns from sessions 1–5 unchanged; see
`proof-journal/sessions/session_5/summary.md` for the complete list.)

### Known Blockers (do not retry)

- **Round 5 work** (Sₕ : `LinearEquiv`, plus `kernelImage_ker`/`_im`):
  do not retry until Round 5 is dispatched. Tier S #3 dependency now
  satisfied as of this round.
- **Round 6 work** (Levi machinery, plus `pNormalForm_witnesses` /
  `residual_levi_extract` / `residual_levi_build`): blocked on Levi-action
  infrastructure (~60–100 lines additive in `Slice.lean`). Do not retry
  until Round 6.
- **Round 7 work** (`sIndependenceAndOrbitCriterion`): blocked on
  Round 6's `pNormalForm_residual_orbit_iso` plus added hypotheses.

### Stale comment hygiene

- `NormalForm.lean` lines 344, 357 contain comment refs to the now-removed
  `L0_isotropic` field. They compile cleanly (inside docstrings/comments)
  but should be refreshed when Round 5 touches the file.

## Last Updated

2026-04-27T17:46:22Z (end of session 6 / Round 4)
