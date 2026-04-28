# Project Status

## Overall Progress

- **Stage:** prover (Round 10 complete; **3** declaration-use sorries; **build GREEN** after Round-9 regression repaired).
- **Build state:** `lake build` succeeds (8033 jobs, 0 errors, end of session 12 / Round 10).
- **Custom axiom declarations:** 0. Public-theorem axiom audit:
  - `pNormalForm_residual_orbit_iso`, `kernelImage_ker`, `kernelImage_im`, `kernelImage_dim`, `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`, `multiplicityEvenSymmCase`: `[propext, Classical.choice, Quot.sound]` — CLEAN.
  - `pNormalForm` — depends transitively on `sorryAx` via the **lone Step 3 sorry inside `pNormalForm_witnesses_aux`** (NormalForm.lean line 570).
  - `sIndependenceAndOrbitCriterion`, `main` — depend transitively on `sorryAx` via `isParabolicElement_ringInverse_of_orbit_witness` (Orbits.lean lines 588, 649).
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → 5 (end of session 8) → 3 (end of session 9) → 3 (end of session 10) → 3 declaration warnings + build RED (end of session 11) → **3 declaration warnings + build GREEN (end of session 12)**.
  Net session 12: **0 declaration sorries closed, internal sorry tokens 7 → 4 (4 closures), build RED → GREEN**. Plan target was 3 → 1 or 2; achieved a structural recovery + closure of NormalForm Steps 0.75 (R9 build break), Step 1 (the d-construction), and Step 2 (the D-lift). Step 3 is the single remaining sorry standing between the project and an axiom-clean `pNormalForm`.

## Round 10 work (session 12) — build recovered, NormalForm Steps 1+2 closed, Orbits restructured

### NormalForm.lean — `pNormalForm_witnesses_aux` 4 of 5 internal sorries closed

- **Step 0.75 (R9 build break repaired):** Two bugs fixed.
  1. `IsCompl` orientation swap — flipped membership pair order to match `hK'_compl : IsCompl (ker Cbar) K'`.
  2. `linarith [hsum]` over a non-ordered `Field F` — replaced with a direct `← map_add` derivation: `Cbar k + Cbar n = Cbar z` via `congrArg`, plus `Cbar k = 0` to conclude `Cbar n = Cbar z`.
- **Step 1 (closed, ~85 lines):** Built `d : E' ≃ E'` aligning `Cbar ∘ d.symm` with `Sₕ`. Construction:
  - `cbarK' : K' ≃ V0/range X0` via `LinearEquiv.ofBijective`.
  - `f : L1' ≃ K' := Sₕ ≪≫ₗ VplusEquivQuotientRange ≪≫ₗ cbarK'.symm`.
  - `dsymm := prodEq_L.symm ≪≫ₗ f.prodCongr gL0 ≪≫ₗ prodEq_K`; `d := dsymm.symm`.
  - Pointwise alignment proven via `Submodule.prodEquivOfIsCompl_symm_apply_{left,right}` (with named args `(p := L1') (q := L0')`).
- **Step 2 (closed, ~115 lines):** Built `D : E' →ₗ V0` lifting `(C ∘ d.symm - CST Sₕ)` through `X0`. Construction:
  - Step 2a: `(C ∘ d.symm - CST Sₕ) e0 ∈ range X0` via `Submodule.ker_mkQ` + decomposition `e0 = a' + b'`. `rfl`-level helper used to bypass a `LinearMap.comp_apply` rewrite failure on the LinearEquiv-coerced composition `(C ∘ₗ ↑d.symm)`.
  - Step 2b: lift via `Submodule.exists_isCompl (ker X0)` + `LinearEquiv.ofInjective` + `LinearMap.codRestrict`.
- **Step 3 (UNCLOSED):** Single focused sorry remains at line 570. Estimated 120–150 lines. See `proof-journal/sessions/session_12/recommendations.md`.

### Orbits.lean — `isParabolicElement_ringInverse_of_orbit_witness` signature tightened, case-split landed

- **Tier S #7 option (a) signature change:** `_hT₁ : IsSkewT T₁` → `hT₁ : T₁ ∈ S.Tset_circ`. Cascaded to call site in `sIndependenceAndOrbitCriterion`.
- **Body restructure with `by_cases h_easy : ¬ (eps = 1 ∧ Odd (finrank L0'))`:**
  - Easy branch (ε=-1 OR ε=+1+even): `MaximalRank T_i = dim L0'` ⇒ rank-nullity gives `ker T_i = ⊥` ⇒ `ker_XST_eq_flagE_of_injective` closes the kernel-equality conjunct **sorry-free**.
  - Hard branch (ε=+1+odd): kernel equality fails (`dim ker T = 1`); single focused sorry at line 588.
- **flagEV0 conjunct:** still requires `parabolic_decompose` infrastructure; sorry retained at line 649.
- **Net effect:** internal sorry token count 2 → 2 (positions 588, 649 are now case-split-isolated; bundled-conjunction sorry from R9 line 563 is gone).

### Slice.lean — `parabolic_decompose` ✅ NO WORK (Tier S #6 deferred)

Verify-only per PROGRESS.md Round 10 directive. File unchanged. Single sorry at 1572.

### Basic.lean, LocalForms.lean, X0Geometry.lean — ✅ NO WORK

All three correctly verified isolation, wrote brief "no work" reports, made no edits.

## Solved earlier (sessions 1–11, carry-forward)

(See `proof-journal/sessions/session_11/summary.md` for the immediate-prior round and earlier sessions for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4).
- `NormalForm.lean :: kernelImage_dim`, `kernelImage_ker`, `kernelImage_im`, `isUnit_uD`, `map_uD_eq_of_le`, `pNormalForm` (sessions 3–7), `residual_levi_extract`, `residual_levi_build`, `pNormalForm_residual_orbit_iso`, `XST_apply`, `extendL0'IsoToE'` (session 9 / Round 7).
- `Basic.lean :: SliceSetup`, `UnipotentRadical` (Tier S #2, #3 — session 6).
- `Slice.lean :: parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`, `parametrizeX0PlusU_mem`, `uD_isParabolic` (sessions 5–6).
- `Slice.lean ::` Levi-action machinery (14 declarations) — closed in session 8.
- `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent`, `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`, `inducedOrbits`, `main` (sessions 3 + 6; `main` signature updated in session 10).
- **NEW session 12:** NormalForm Step 0.75 (build break repair), Step 1 (d-construction, ~85 lines), Step 2 (D-lift, ~115 lines).

## Remaining sorries (3 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `NormalForm.lean` | 197 | `pNormalForm_witnesses_aux` (private helper) | A | **Single isolated sorry at line 570 (Step 3).** Round 11 primary objective. Estimated 120–150 lines. Once closed, `pNormalForm` becomes axiom-clean. Steps 0–2 sorry-free at end of session 12. |
| `Slice.lean` | 1109 | `parabolic_decompose` (sorry at 1572) | (Round 6 deferred) | Statement-level mathematical gap (Tier S #6); current `uD D` should be `uD D + B'`. Round 11 directive: verify-only, defer to polish. |
| `Orbits.lean` | 524 | `isParabolicElement_ringInverse_of_orbit_witness` (private helper) | A (deferred) | 2 sorries (588, 649) on the documented Tier S #6/#7 deferred cases (ε=+1+odd kernel + flagEV0 stability). Body now case-split; easy 2/3 of cases close sorry-free via `ker_XST_eq_flagE_of_injective`. Both surviving sorries genuinely require Bruhat decomposition; defer to polish. |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 11 list.)

- **(NEW session 12) Named args for `Submodule.prodEquivOfIsCompl_symm_apply_{left,right}`.** The `p, q : Submodule R E` are explicit (from `variable (p q : ...)`), so pass them via `(p := ...) (q := ...)`. Positional invocation fails type-inference. Mandatory pattern for any `prodEquivOfIsCompl`-based proof.

- **(NEW session 12) `rfl`-level definitional unfold for LinearEquiv-coerced compositions.** When `LinearMap.comp_apply` rewrite fails on `(C ∘ₗ ↑d.symm) x`, introduce a helper via `rfl` (e.g., `mkQ ((C ∘ₗ d.symm) a') = Cbar S C (d.symm a') := rfl`) using the definitional structure (`Cbar S C v = mkQ (C v)`). Reusable any time `↑f` is the `LinearEquiv → LinearMap` coercion.

- **(NEW session 12) `map_add` + `congrArg` for vector identities over generic `Field F`.** Don't use `linarith`/`linear_combination` for module-element identities (`Field F` has no order; module is not a `CommSemiring`). Pattern: from `k + n = z`, derive `Cbar k + Cbar n = Cbar z` via `← map_add`, then use known nullity (`Cbar k = 0`) to extract `Cbar n = Cbar z`. Generalises to any homomorphism with a known annihilator.

- **(NEW session 12) `LinearEquiv.ofInjective_symm_apply` for sectioning a partial injection.** When you need a section of `f : M →ₗ N` defined on `range f`, use `LinearEquiv.ofInjective f h : M ≃ₗ range f`, then `phi.symm` gives the section. The simp lemma `LinearEquiv.ofInjective_symm_apply` gives `f (phi.symm y) = (y : N)`. Used in NormalForm Step 2b for the lift through `X0`.

- **(NEW session 12) `Submodule.ker_mkQ` for membership-via-quotient.** `(M.mkQ).ker = M`. Pattern: to show `x ∈ M`, prove `M.mkQ x = 0`, then `rw [Submodule.ker_mkQ]` on the membership. Used in NormalForm Step 2a.

- **(NEW session 12) `Tset_circ` membership unlocks rank-based reasoning.** When a helper needs both skewness AND rank info, accept `T ∈ Tset_circ` instead of `IsSkewT T`. Reusable across any future helper that does case-by-rank. Used in Orbits R10 signature tightening.

- **(NEW session 12) `by_cases` on `eps × parity` for slice-form arguments.** `by_cases h_easy : ¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))` cleanly separates kernel-of-XST cases. Easy 2/3 close via `ker_XST_eq_flagE_of_injective`; ε=+1+odd needs Bruhat (deferred Tier S #6/#7).

- **(NEW session 12) Axiom-clean public theorems via private-helper isolation.** The `pNormalForm_witnesses_aux` private-helper pattern (introduced session 10) successfully isolates `sorryAx` to a single private helper. End of R10: `pNormalForm_residual_orbit_iso`, `kernelImage_*` are axiom-clean; only `pNormalForm` retains transitive `sorryAx` via the lone Step 3 sorry. This validates the structural reorganisation strategy.

(Earlier patterns from sessions 1–11 unchanged; see `proof-journal/sessions/session_11/summary.md` and PROGRESS.md "Reusable Gotchas" for the complete carryforward.)

### Known Blockers (do not retry)

- **`parabolic_decompose` (Slice.lean line 1109) with current signature.** **Mathematical gap identified — statement is too narrow** (Tier S #6). A general parabolic isometry has form `(uD D + B') ∘ leviGL_E d ∘ leviGL_V0 g`; current statement fixes `B' = 0`. Round 11 directive: verify-only, defer to polish stage with a refactor decision (generalise `uD` vs narrow the statement).

- **`isParabolicElement_ringInverse_of_orbit_witness` Orbits line 588 (ε=+1+odd kernel) + line 649 (flagEV0).** Both genuinely require Bruhat-decomposition / `parabolic_decompose` infrastructure (Tier S #6/#7). Closing them without first resolving Tier S #6 is not feasible. Round 11 directive: verify-only, defer to polish.

### Stale comment hygiene

- `NormalForm.lean` lines 344, 357 still contain comment refs to the now-removed `L0_isotropic` field (replaced by Lagrangian quartet in session 6). They compile cleanly (inside docstrings/comments) but should be refreshed during the next NormalForm edit pass — Round 11's Step 3 work is the natural opportunity.

### Process anti-patterns to address

- **LSP MCP avoidance (2 rounds in a row).** Rounds 9, 10 used 0 `lean_diagnostic_messages`, 0 `lean_leansearch`, 0 `lean_loogle` calls. Manual `Bash grep -rn` against the local mathlib mirror substituted for `lean_loogle`. The harness should escalate this to an explicit pre-flight directive in PROGRESS.md / `.archon/USER_HINTS.md` for Round 11.

## Last Updated

2026-04-28T00:30:00Z (end of session 12 / Round 10 — review agent journal pass)
