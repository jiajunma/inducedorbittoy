# Round 11 Recommendations (for plan agent)

## Top priority — close Step 3 of `pNormalForm_witnesses_aux` (NormalForm.lean line 570)

This is the **single remaining sorry** standing between the project and an axiom-clean `pNormalForm`. After Round 10's recovery, the situation is:

- `pNormalForm` has transitive `sorryAx` only via Step 3.
- `pNormalForm_residual_orbit_iso`, `kernelImage_*` are CLEAN (`[propext, Classical.choice, Quot.sound]`).
- All of Steps 0, 0.5, 0.75, 1, 2 are sorry-free in `pNormalForm_witnesses_aux`.
- Step 3 is the existential `∃ T : L0' →ₗ L0, IsSkewT T ∧ uD D ∘ leviGL_E d ∘ XCB C B = XST Sₕ T ∘ uD D ∘ leviGL_E d`.

### Recommended approach

**Refactor Step 2 to expose the freedom in `D|_{L1'}`**: instead of constructing one specific `D₀` via `LinearEquiv.ofInjective`, observe that the lift is unique only up to `D ↦ D + ψ` where `ψ : E' →ₗ ker X0`. Pick `ψ|_{L1'}` via `vplusKerPairing_isPerfPair` so that on `L1'`, the corrected operator
```
B'' = lambdaDualE d.symm ∘ B ∘ d.symm
      + (Cdual D ∘ C - Cdual C ∘ D - Cdual D ∘ X0 ∘ D) ∘ d.symm
```
satisfies `B''(L1') = 0` (i.e., the L0-component of `B''` vanishes on `L1'`).

**Then:** `B''(L0') ⊂ L0` follows from the original skewness of `B` (`_hB`) propagating through Levi+unipotent transformations. Define `T u := codRestrict L0 (B'' (u : E')) <proof>` for `u : L0'`. Skewness of `T` (i.e., `S.IsSkewT T`) propagates from `_hB`.

**Final equation:** `uD D ∘ leviGL_E d ∘ XCB C B = XST Sₕ T ∘ uD D ∘ leviGL_E d` follows by chaining `leviGL_E_conj_XCB d`, `uD_conj_XCB D`, and the reduction `(C ∘ d.symm - X0 ∘ D) = CST Sₕ` (Step 2 design with the corrected `D`), then the `B'' = BST T` reduction.

**Estimated effort:** 120–150 lines. Likely splits naturally into two private helpers:
- `_step3_T_construction` — builds `T` and `B''` and proves `B''(L1') = 0` + `B''(L0') ⊂ L0`.
- `_step3_skewness_and_equation` — verifies `IsSkewT T` and the conjugation equation.

### Reusable infrastructure already available

- `Slice.lean` Levi machinery: `lambdaDualE`, `lambdaDualE_pairing_eq`, `leviGL_E`, `leviGL_E_apply`, `leviGL_E_isParabolic`, `leviGL_E_conj_XCB`, `leviGL_E_symm_inverse`. All sorry-free.
- `Slice.lean` unipotent half: `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`, `uD`, `uD_apply`, `uD_neg_inverse`, `uD_conj_XCB`, `uD_isParabolic`. All sorry-free.
- `X0Geometry.lean :: vplusKerPairing_isPerfPair` — the perfect pairing needed to enforce `B''(L1') = 0` via dual evaluation.
- `NormalForm.lean :: kernelImage_ker`, `kernelImage_im`, `kernelImage_dim`, `XST_apply`, `extendL0'IsoToE'` — Round 7 helpers, all sorry-free.

### Single-objective dispatch

**RECOMMEND single-prover dispatch on NormalForm.lean only.** The Round 10 dual dispatch worked, but Step 3 is large (120–150 lines) and benefits from undivided attention. Orbits and Slice should be NO-WORK (verify-only) for Round 11.

### Diagnostic discipline (CRITICAL)

The Round 10 prover used 0 `lean_diagnostic_messages`, 0 `lean_leansearch`, 0 `lean_loogle` calls — same anti-pattern as Round 9. **Round 11 plan agent should issue an explicit hint** (in PROGRESS.md or `.archon/USER_HINTS.md`) directing the prover to use:
- `lean_diagnostic_messages` after every batch of edits (not just `lake env lean` via Bash).
- `lean_loogle` for mathlib lemma searches (faster than `grep -rn` against `.lake/packages/mathlib`).
- `lean_goal` to inspect the current proof state at the sorry position before attempting tactics.
- `lean_multi_attempt` to test candidate tactic combinations without editing the file.

If Round 10 needed 8 attempts to close Steps 1+2, Round 11 will likely need 15–20 attempts on Step 3; the speedup from MCP-based diagnostics is significant.

## Secondary — DO NOT ASSIGN

### `Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness` — both sorries deferred

The Round 10 case-split landed cleanly. The two surviving sorries (line 588 ε=+1+odd kernel, line 649 flagEV0 stability) **both genuinely require Bruhat-decomposition / `parabolic_decompose` infrastructure** (Tier S #6/#7). Closing them without first resolving Tier S #6 is not feasible.

**Round 11 directive:** verify-only, no work. Defer to polish stage.

### `Slice.lean :: parabolic_decompose` — Tier S #6, deferred

Statement-level mathematical gap (current `uD D` should be `uD D + B'`). PROGRESS.md Round 10 directive (DO NOT ATTEMPT) carries forward to Round 11. Defer to polish.

## Promotion criteria for `prover` → `polish`

Round 11 should promote the project to `polish` stage **if and only if**:
1. `pNormalForm_witnesses_aux` Step 3 closes (sorry token at line 570 removed).
2. `lake build` GREEN (preserved from Round 10).
3. `#print axioms pNormalForm` returns `[propext, Classical.choice, Quot.sound]` (CLEAN — no `sorryAx`).

If Step 3 closes, the project state at end of Round 11 will be:
- 2 declaration warnings (`Slice.lean :: parabolic_decompose` + `Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness`).
- 3 internal sorry tokens (Slice 1572, Orbits 588 + 649).
- All public theorems CLEAN: `pNormalForm`, `pNormalForm_residual_orbit_iso`, `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`, `multiplicityEvenSymmCase`, `kernelImage_*`.
- `sIndependenceAndOrbitCriterion`, `main` retain transitive `sorryAx` via the documented Tier S #6/#7 deferrals.

This is the natural cut-point for the prover stage. The polish stage handles Tier S #6 (parabolic_decompose statement refactor) and Tier S #7 (Orbits ε=+1+odd case via Bruhat decomposition) under a different methodology.

## Reusable proof patterns to carry forward (Round 10 → Round 11)

1. **Named args for `Submodule.prodEquivOfIsCompl_symm_apply_{left,right}`.** `(p := L1') (q := L0')` is mandatory; positional arg passing fails type-inference.

2. **`rfl`-level definitional unfold for LinearEquiv-coerced compositions.** When `LinearMap.comp_apply` rewrite fails on `(C ∘ₗ ↑d.symm) x`, introduce a helper via `rfl` (e.g., `mkQ ((C ∘ₗ d.symm) a') = Cbar S C (d.symm a') := rfl`) using the definitional structure (`Cbar S C v = mkQ (C v)`).

3. **`map_add` + `congrArg` for vector identities over generic Field F.** Don't use `linarith`/`linear_combination` for module-element identities. Pattern: from `k + n = z`, derive `Cbar k + Cbar n = Cbar z` via `← map_add`, then use known nullity (`Cbar k = 0`) to extract `Cbar n = Cbar z`.

4. **`IsCompl` orientation = obtain-site orientation.** `Submodule.exists_isCompl K` returns `IsCompl K K'` (kernel first). Membership pairs in `Submodule.mem_inf` / `Submodule.mem_sup` must follow the same orientation; flip with `.symm` if the call site demands the other direction.

5. **`Tset_circ` membership unlocks rank-based reasoning.** When a helper needs both skewness AND rank info, replace `IsSkewT T` with `T ∈ Tset_circ`. Reusable across any future helper that does case-by-rank.

6. **`by_cases h_easy : ¬ (eps = 1 ∧ Odd l)` for slice-form arguments.** Cleanly separates the kernel-of-XST cases. Easy 2/3 close via `ker_XST_eq_flagE_of_injective`; ε=+1+odd needs Bruhat (deferred).

## Stale comment hygiene (carry-forward from Round 9)

`NormalForm.lean` lines 344, 357 still contain comment refs to the now-removed `L0_isotropic` field (replaced by Lagrangian quartet in session 6). They compile cleanly inside docstrings/comments but should be refreshed during the next NormalForm edit pass. **Round 11's Step 3 work should opportunistically refresh these.**

## Process recommendations for plan agent

1. **Single-objective Round 11.** NormalForm Step 3 only. Orbits + Slice = verify-only.
2. **Issue explicit MCP-discipline hint.** Add to `.archon/USER_HINTS.md` or PROGRESS.md the Round 11 directive: "USE lean_diagnostic_messages, lean_loogle, lean_goal, lean_multi_attempt — DO NOT use Bash `lake env lean` as the sole verification path." This is the third round in a row where the prover has avoided LSP MCP tools; an explicit hint is warranted.
3. **End-of-round axiom audit.** After Round 11 lands, the plan agent should run `#print axioms pNormalForm` to confirm CLEAN before promoting to polish.
