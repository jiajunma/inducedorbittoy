# Project Status

## Overall Progress

- **Stage:** prover (Round 7 complete; **3** declaration-use sorries — −2 net from Round 6).
- **Build state:** `lake build` succeeds (green, end of session 9 / Round 7).
- **Custom axiom declarations:** 0. The two newly-closed Round 7 helpers
  (`residual_levi_extract`, `residual_levi_build`) plus the public consumer
  `pNormalForm_residual_orbit_iso` depend only on
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx` (the deferred
  `pNormalForm_witnesses` body still uses `sorry` so `pNormalForm` transitively
  depends on `sorryAx` — expected per Round 7 plan).
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → 5 (end of session 8) → **3 (end of session 9)**.
  Net session 9: **−2** declaration sorries. Plan target was 5 → 2 (close all 3 NormalForm sorries); achieved 2 of 3 with `pNormalForm_witnesses` body deferred to Round 8 as documented in the body docstring.

## Solved this session (session 9 / Round 7)

- **`NormalForm.lean :: residual_levi_extract` (line 440)** — `~250` lines closed sorry-free. Forward extraction of the L0' isometry `h` from a parabolic conjugator. Four-step skeleton: (A) Step A preserves L0' via V0-component analysis + `Sₕ.injective`; (B) Step B defines `qFun = codRestrict L0' (projE'_V ∘ p ∘ inE' ∘ L0'.subtype)`; (C) Step C shows injectivity via `flagEV0` preservation by `p` and `p⁻¹`; (D) Step D verifies isometry via `IsOrthogonal p` + `XST_apply` substitution + `Cdual_pairing_eq`.

- **`NormalForm.lean :: residual_levi_build` (line 847)** — closed sorry-free. Constructs the Levi factor `d := extendL0'IsoToE' S h` extending `h : L0' ≃ L0'` by id on L1'; takes `p := leviGL_E S d`; verifies the conjugation via `leviGL_E_conj_XCB` reduced to two component identities (`CST Sₕ ∘ d.symm = CST Sₕ` and `lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂`).

- **`NormalForm.lean :: pNormalForm_residual_orbit_iso` (line 990)** — public theorem **now sorry-free** (Sₕ as LinearEquiv enables direct passage to `residual_levi_extract` / `residual_levi_build`). `#print axioms` clean.

- **Tier S #5 signature restructure (`pNormalForm_witnesses` line 203)** — replaced mathematically-false `uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T` with corrected Levi-factor form `∃ Sₕ D d T, ... uD D ∘ leviGL_E d ∘ XCB C B = XST Sₕ T ∘ uD D ∘ leviGL_E d`. `Sₕ` strengthened from `LinearMap` to `LinearEquiv`. Cascaded through `pNormalForm`, `pNormalForm_residual_orbit_iso`, `residual_levi_*` helpers.

- **`NormalForm.lean :: pNormalForm` (line 248)** — body refactored to consume the new `pNormalForm_witnesses` signature (extract parabolic `p := uD D ∘ leviGL_E d`). Body sorry-free; depends on `pNormalForm_witnesses` so transitively `sorryAx`.

- **`NormalForm.lean :: XST_apply` (private helper, line 329)** — added because `residual_levi_extract` needs explicit unfolding `XST S Sₕ T (e, v, e') = (Cdual S (CST S Sₕ) v + (T (projL0' S e') : S.E), S.X0 v + (Sₕ (projL1' S e') : S.V0), 0)`. **Sorry-free.**

- **`NormalForm.lean :: extendL0'IsoToE'` (private noncomputable def) + 3 helper lemmas** (`extendL0'IsoToE'_symm_apply`, `projL1'_extendL0'IsoToE'_symm`, `projL0'_extendL0'IsoToE'_symm`). Block-extension via `Submodule.prodEquivOfIsCompl` + `LinearEquiv.prodCongr`. **All sorry-free.**

## Solved earlier (sessions 1–8, carry-forward)

(See `proof-journal/sessions/session_8/summary.md` and earlier sessions for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4).
- `NormalForm.lean :: kernelImage_dim`, `kernelImage_ker`, `kernelImage_im`, `isUnit_uD`, `map_uD_eq_of_le`, `pNormalForm` (sessions 3–7; `pNormalForm` now refactored in session 9).
- `Basic.lean :: SliceSetup`, `UnipotentRadical` (Tier S #2, #3 — session 6).
- `Slice.lean :: parametrizeX0PlusU_existence`, `parametrizeX0PlusU_mem`, `uD_isParabolic` (sessions 5–6).
- `Slice.lean ::` Levi-action machinery (14 declarations: `lambdaDualE`, `lambdaDualE_pairing_eq`, `lambdaDualE_id`, `lambdaDualE_comp`, `leviGL_E`, `leviGL_V0`, `leviGL_E_apply`, `leviGL_V0_apply`, `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse`, `leviGL_E_isParabolic`, `leviGL_V0_isParabolic`, `leviGL_E_conj_XCB`, `leviGL_V0_conj_XCB`) — closed in session 8.
- `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent`, `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`, `inducedOrbits`, `main` (sessions 3 + 6).

## Remaining sorries (3 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `NormalForm.lean` | 216 | `pNormalForm_witnesses` (private helper) | A | **Single isolated sorry, body docstring outlines four-step plan.** Round 8 primary objective. ~150 lines estimated. The Tier S #5 signature restructure has already landed; only the body remains. Consumers `residual_levi_extract`, `residual_levi_build`, `pNormalForm_residual_orbit_iso` are all sorry-free. |
| `Slice.lean` | 1089 | `parabolic_decompose` (deferred Round 6) | (Round 6 deferred) | Three sub-constructions per `informal/levi.md §6.6` (~85 lines). 24-line `Gap:` comment block in-file. **Optional** for Round 8 — not needed by Round 7 work (Option B sidesteps it); only relevant if Orbits.lean forward direction needs it. |
| `Orbits.lean` | 358 + 376 | `sIndependenceAndOrbitCriterion` (2 internal scoped sorries, 1 declaration) | A (deferred) | **Now structurally unblocked** — `pNormalForm_residual_orbit_iso` is sorry-free. Forward direction (358) needs parabolic-decomposition step (depends on `parabolic_decompose` OR a workaround). Reverse direction (376) is direct via `pNormalForm_residual_orbit_iso`. Both directions need missing hypotheses (`Nondegenerate`, `(2 : F) ≠ 0`, `Sₕ`-equality) added to the theorem statement, OR strengthening `pNormalForm_residual_orbit_iso` to absorb them. |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 8 list.)

- **(NEW session 9) `prodEquivOfIsCompl` symm via `Submodule.toLinearMap_prodEquivOfIsCompl_symm`.** The symm coerces to `(linearProjOfIsCompl p q h).prod (linearProjOfIsCompl q p _)`, i.e., `prodEq.symm e' = (projL1' e', projL0' e')` for our `IsCompl L1' L0'`. Bypasses unfolding through `LinearEquiv.trans`. Used in `extendL0'IsoToE'` Round 7.

- **(NEW session 9) `set ... with hdef` for opaque shorthands, BUT NOT for sums you'll later `LinearMap.add_apply`-rewrite.** Identifies a specific failure mode: `set lhs_E := Cdual ... + T₂ ...` opaquefies the sum, breaking subsequent `rw [add_apply]`. Use `set` for opaque applications like `set p_uv := p (0, 0, v)`, never for sums.

- **(NEW session 9) `congr 1` does NOT split through outer `LinearMap.comp`.** For `XCB(A, B) = XCB(A', B') ∘ leviGL_E d`-style equations where the outer is `LinearMap.comp`, `congr 1` doesn't yield 2 component goals. Better: prove `A = A'` and `B = B'` as separate `have`s and chain `rw [hA, hB]`.

- **(NEW session 9) Linearity in 1st arg of `S.paired.pairing`: `map_add` first, then `add_apply`.** The pattern `pairing (a + b) c = pairing a c + pairing b c` reduces via `LinearMap.map_add` (LHS first arg) followed by `LinearMap.add_apply` (resulting `(f + g) c`); reversed order fails.

- **(NEW session 9) `(qFun l : L0').val = qFunRaw l` is *definitionally* equal** when `qFun = LinearMap.codRestrict L0' qFunRaw _`. Use `(qFun l : E') = 0 → qFunRaw l = 0` via `exact h_val` (no `simpa`).

- **(NEW session 9) Trailing `rfl` after `simp only [..., map_zero]` is "No goals" lint.** `simp only` with `map_zero` already closes `f 0 = 0`. Drop it.

- **(NEW session 9) LinearEquiv at definition; pass directly at use site.** When a private theorem strengthens `Sₕ` from LinearMap to LinearEquiv, the consumer call site that expects LinearMap should pass `Sₕ` directly (Lean auto-coerces via LinearEquiv.toLinearMap-via-CoeFun). Explicit coercion at the call site fails type-check.

- **(NEW session 9) `S.V` ≡ `S.paired.E'` abbrev boundary requires explicit type ascription in helper defs.** When defining helpers like `extendL0'IsoToE' S h : E' ≃ E'`, every `↑d.symm e'` application needs `(d.symm : S.paired.E' →ₗ[F] S.paired.E')` to bridge the abbrev.

- **(NEW session 9) `XST_apply` private helper near top of consuming section.** When a proof needs explicit unfolding of a multi-let block-matrix def, write a `private theorem _apply` early in the section. Saves ~10 lines per consumer.

(Earlier patterns from sessions 1–8 unchanged; see `proof-journal/sessions/session_8/summary.md` for the complete carryforward list including the Round 6 Levi-machinery patterns.)

### Known Blockers (do not retry)

- **None.** All three remaining sorries are now structurally unblocked:
  - `pNormalForm_witnesses` has the Levi machinery in scope (Round 6) and the consumer-correctness proof in scope (Round 7's `residual_levi_*` are sorry-free).
  - `sIndependenceAndOrbitCriterion` has `pNormalForm_residual_orbit_iso` sorry-free in scope.
  - `parabolic_decompose` has all the sub-pieces (`leviGL_*`, `parametrizeX0PlusU_existence`) sorry-free in scope.

### Stale comment hygiene

- `NormalForm.lean` lines 344, 357 still contain comment refs to the now-removed `L0_isotropic` field (replaced by Lagrangian quartet in session 6). They compile cleanly (inside docstrings/comments) but should be refreshed during the Round 8 `pNormalForm_witnesses` edit pass. (Carry-forward from sessions 7-8.)

## Last Updated

2026-04-28T20:50:00Z (end of session 9 / Round 7)
