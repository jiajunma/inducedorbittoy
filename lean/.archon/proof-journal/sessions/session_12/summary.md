# Session 12 — Prover Round 10 (parallel two-file dispatch on NormalForm + Orbits)

## Metadata

- **Session:** 12 (stage `prover`, Round 10 — parallel two-file dispatch on `NormalForm.lean` + `Orbits.lean`).
- **Sorry count (declaration-use warnings) before round:** 3 declaration warnings + **build RED**
  - `NormalForm.lean`: 1 declaration warning (`pNormalForm_witnesses_aux` line 197) carrying 5 internal sorries (309, 310, 322, 339, 356) + 5 active build errors at 289, 302–305.
  - `Slice.lean`: 1 (`parabolic_decompose` line 1109).
  - `Orbits.lean`: 1 (`isParabolicElement_ringInverse_of_orbit_witness` line 524) with 2 internal sorries (563, 624).
- **Sorry count (declaration-use warnings) after round:** **3 declaration warnings + build GREEN**
  - `NormalForm.lean`: 1 (`pNormalForm_witnesses_aux` line 197) carrying **only 1 internal sorry at line 570 (Step 3)**.
  - `Slice.lean`: 1 (`parabolic_decompose` line 1109 — unchanged).
  - `Orbits.lean`: 1 (`isParabolicElement_ringInverse_of_orbit_witness` line 524) with **2 internal sorries (588, 649)** but case-split refactored.
- **Net change:** **+0 declaration warnings, build RECOVERED (RED → GREEN), internal sorry tokens 7 → 4.** Plan target was 3 → 1 or 2; achieved a structural recovery of the build plus closure of 4 of 5 NormalForm internal sorries (Steps 0.75, 1, 2 closed). Orbits restructured with a clean case split but no sorry tokens removed. Slice deferred per directive.
- **Custom axioms introduced:** 0. Public-theorem axiom audit:
  - `pNormalForm_residual_orbit_iso`, `kernelImage_ker`, `kernelImage_im`, `kernelImage_dim` — `[propext, Classical.choice, Quot.sound]` (CLEAN).
  - `pNormalForm` — transitive `sorryAx` via the lone Step 3 sorry inside `pNormalForm_witnesses_aux` (line 570).
- **Build status:** **`lake build` GREEN** at end of round (8033 jobs, 0 errors, 1 declaration-use warning per sorry-bearing helper, 1 pre-existing `unused variable hlambda` lint at `X0Geometry.lean:221`).
- **Pre-processed log:** 81 events total (1 summary line + 80 events), **12 edits across 2 files** (`NormalForm.lean` and `Orbits.lean`), 0 explicit `lean_goal` checks, 0 `diagnostic_checks` via the LSP MCP (the prover continued to run `lake env lean` as a `Bash` build instead — same anti-pattern as Round 9), 0 `lean_build` calls, 0 `lemma_searches` via `lean_leansearch`/`lean_loogle` (5 manual `grep -rn` searches against `mathlib/...` for `quotientEquivOfIsCompl_*`, `LinearEquiv.ofInjective`, `def ofInjective`).

## Process observation

Plan agent dispatched **two parallel objectives** (Round 10) targeting `NormalForm.lean :: pNormalForm_witnesses_aux` and `Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness`. Both files were edited concurrently by separate provers; non-objective files (`Basic`, `LocalForms`, `Slice`, `X0Geometry`) correctly verified isolation and wrote brief "no work" reports.

**Major recovery vs. Round 9:** the NormalForm prover **fixed the build** (5 errors → 0), **closed the prior Round 9 carry-forward bugs** (variable swap + `linarith`-over-modules), **closed Steps 1 and 2 of the four-step plan** (with substantial new constructive content: ~85 lines for the `d`-construction, ~115 lines for the `D`-lift), and **iterated diagnostically** through three failed `Submodule.prodEquivOfIsCompl_symm_apply_*` rewrite attempts to a clean named-arg invocation. End-of-round axiom audit confirms `pNormalForm_residual_orbit_iso`, `kernelImage_*` are CLEAN; only `pNormalForm` retains transitive `sorryAx` via the lone Step 3 sorry.

**Ongoing diagnostic discipline gap:** the Round 10 NormalForm prover used 0 `lean_diagnostic_messages` MCP calls and 0 `lean_leansearch`/`lean_loogle` calls. All 5 mathlib lemma searches (`quotientEquivOfIsCompl_*`, `LinearEquiv.ofInjective_*`) were done via `Bash grep -rn` against the local mathlib mirror. **This anti-pattern is now consistent across Rounds 9 and 10**; the harness should consider escalating to a hard pre-flight check.

## Target — `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses_aux` ✅ NEAR-COMPLETE (4 of 5 internal sorries closed)

### Step 0 (sorry-free, inherited from Round 9)
`Sₕ : L1' ≃ Vplus` via `LinearEquiv.ofFinrankEq`. No edits.

### Step 0.5 (sorry-free, inherited from Round 9)
Dimension chain: `h_Cbar_surj`, `h_dim_ker_Cbar`, `h_dim_L0'`, `h_dim_match`. No edits.

### Step 0.75 (closed Round 10) — fix R9 build break

**Bug 1: `IsCompl` orientation swap.** Round 9 had:
```lean
have hbot : (x : E') ∈ (K' ⊓ LinearMap.ker (Cbar S C) : Submodule F E') :=
  ⟨hx_in_K', hx_in_ker⟩
rw [hK'_compl.disjoint.eq_bot] at hbot   -- ❌ pattern is `(ker Cbar) ⊓ K'`
```
The R10 fix flipped the order of the membership pair to match `hK'_compl : IsCompl (LinearMap.ker (Cbar S C)) K'`:
```lean
have hbot : (x : E') ∈ (LinearMap.ker (Cbar S C) ⊓ K' : Submodule F E') :=
  ⟨hx_in_ker, hx_in_K'⟩
rw [hK'_compl.disjoint.eq_bot] at hbot   -- ✓ matches now
```

**Bug 2: `linarith` over a non-ordered field.** Round 9 had:
```lean
have hk_eq : k = z - n := by linarith [hsum]   -- ❌ Field F has no order
```
The R10 fix replaced the indirect `n = z - k` derivation with a direct `map_add`-style argument:
```lean
have hcbarsum : Cbar S C k + Cbar S C n = Cbar S C z := by
  rw [← map_add]; exact congrArg _ hsum
rw [hCbar_k, zero_add] at hcbarsum
rw [hcbarsum, hz]
```
**Build verification:** `lake env lean InducedOrbitToy/NormalForm.lean` → only the `pNormalForm_witnesses_aux` declaration-use warning at 197 remained.

### Step 1 (closed Round 10) — build `d : E' ≃ E'`

**Construction (~85 lines):**
1. `cbarK' : K' ≃ V0/range X0` via `LinearEquiv.ofBijective CbarK'_lin ⟨hCbarK'_inj, hCbarK'_surj⟩`.
2. `f : L1' ≃ K' := Sₕ ≪≫ₗ VplusEquivQuotientRange S.toX0Setup ≪≫ₗ cbarK'.symm`.
3. `prodEq_L : (L1' × L0') ≃ E'` via `Submodule.prodEquivOfIsCompl S.L1' S.L0' S.isComplL'`.
4. `prodEq_K : (K' × ker(Cbar)) ≃ E'` via `prodEquivOfIsCompl K' (ker Cbar) hK'_compl.symm`.
5. `dsymm := prodEq_L.symm ≪≫ₗ f.prodCongr gL0 ≪≫ₗ prodEq_K`; `d := dsymm.symm`.

**Pointwise alignment:**
- `dsymm (a' : L1' ↪ E') = (f a' : K' ↪ E')` — via `prodEquivOfIsCompl_symm_apply_left`.
- `dsymm (b' : L0' ↪ E') = (gL0 b' : ker Cbar ↪ E')` — via `prodEquivOfIsCompl_symm_apply_right`.

**`hd_L1'`:**
- `Cbar((f a' : K') : E') = CbarK'_lin (f a') = cbarK' (f a')`.
- `cbarK' (f a') = cbarK' (cbarK'.symm (VplusEquivQuotientRange (Sₕ a'))) = VplusEquivQuotientRange (Sₕ a')`.
- `VplusEquivQuotientRange v = mkQ ((v : Vplus) : V0)` via `Submodule.quotientEquivOfIsCompl_symm_apply`.

**`hd_L0'`:** `Cbar((gL0 b' : ker Cbar) : E') = 0` direct from `(gL0 b').2 : (gL0 b' : V0) ∈ ker Cbar`.

**Diagnostic iteration (3 failed attempts captured in raw log):**

Attempt 1 (raw log line 32 / ts 23:48:45) used unnamed-arg invocation:
```lean
rw [Submodule.prodEquivOfIsCompl_symm_apply_left S.isComplL' a']
```
**Error:** `Tactic rewrite failed: Did not find an occurrence of the pattern (Submodule.prodEquivOfIsCompl ?m ?m ?h).symm ↑?x in the target expression`. The rewrite couldn't unify because `prodEquivOfIsCompl` was applied to `_compl.symm` underneath multiple `≪≫ₗ` layers.

Attempt 2 (raw log line 34 / ts 23:49:23) tried `show`-based normalisation. **Same error pattern.**

Attempt 3 (raw log line 36 / ts 23:50:22) introduced an explicit intermediate:
```lean
have h1 : (Submodule.prodEquivOfIsCompl S.L1' S.L0' S.isComplL').symm
    ((a' : S.L1') : S.paired.E') = (a', 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left S.isComplL' a'
```
**Error:** `Type mismatch: Submodule.prodEquivOfIsCompl_symm_apply_left ?m ?m has type ∀ (h : IsCompl ?m ?m) (x : ↥?m), …` — the `p, q` arguments are explicit and not inferred from `IsCompl`.

Attempt 4 (raw log line 38 / ts 23:51:27, **success**) used named-arg invocation:
```lean
have h1 : (Submodule.prodEquivOfIsCompl S.L1' S.L0' S.isComplL').symm
    ((a' : S.L1') : S.paired.E') = (a', 0) :=
  Submodule.prodEquivOfIsCompl_symm_apply_left (p := S.L1') (q := S.L0')
    S.isComplL' a'
```
**Verification:** `lake env lean` → only the line-197 declaration warning. Step 1 closed.

**Mathlib lemmas used:**
- `LinearEquiv.ofBijective`, `LinearEquiv.prodCongr`
- `Submodule.prodEquivOfIsCompl`, `Submodule.prodEquivOfIsCompl_symm_apply_{left,right}` (with named args)
- `Submodule.quotientEquivOfIsCompl_symm_apply`
- `LinearEquiv.apply_symm_apply`, `LinearEquiv.trans_apply`, `ZeroMemClass.coe_zero`

### Step 2 (closed Round 10) — build `D : E' →ₗ V0` lifting `(C ∘ d.symm - CST Sₕ)` through `X0`

**Step 2a — `(C ∘ d.symm - CST Sₕ) e0 ∈ range X0`:**
Reduce to `mkQ-zero` via `Submodule.ker_mkQ`. Decompose `e0 = (a' : E') + (b' : E')` via `Submodule.IsCompl.projection_add_projection_eq_self S.isComplL'`.

- On `a' ∈ L1'`: `mkQ(C(d.symm a')) = Cbar S C (d.symm a') = mkQ(Sₕ a' : V0)` (by `hd_L1'`), and `CST Sₕ (a' : E') = (Sₕ a' : V0)` (computed via `projL1' (a' : E') = a'` and `linearProjOfIsCompl_apply_left S.isComplL'`). Difference under `mkQ` is zero.
- On `b' ∈ L0'`: `mkQ(C(d.symm b')) = Cbar S C (d.symm b') = 0` (by `hd_L0'`), and `CST Sₕ (b' : E') = 0` (via `projL1' (b' : E') = 0`).

**Step 2b — lift through X0:**
1. `obtain ⟨K_X, hK_X_compl⟩ := Submodule.exists_isCompl (LinearMap.ker S.X0)`.
2. `X0_K_X := S.X0 ∘ₗ K_X.subtype : K_X →ₗ V0`, injective via `K_X ⊓ ker X0 = ⊥`.
3. `range X0_K_X = range X0` proven via decomposition of any `v` as `n + k` with `n ∈ ker X0`, `k ∈ K_X`, then `X0 v = X0 k` since `X0 n = 0`.
4. `phi : K_X ≃ range X0_K_X := LinearEquiv.ofInjective X0_K_X hX0_K_X_inj`.
5. `diff_cod : E' →ₗ range X0_K_X` via `LinearMap.codRestrict` using `(C ∘ d.symm - CST Sₕ) e0 ∈ range X0_K_X`.
6. `D := K_X.subtype ∘ₗ phi.symm ∘ₗ diff_cod`.

**Verification `X0 ∘ D = diff`:**
- `X0 (K_X.subtype k) = X0_K_X k` (by `rfl`).
- `X0_K_X (phi.symm y) = (y : V0)` via `LinearEquiv.ofInjective_symm_apply`.
- `(diff_cod e0 : V0) = diff e0` (by `rfl` from `codRestrict`).

**Diagnostic iteration (1 failed attempt):**

Raw log line 50 (ts 23:56:58) attempted:
```lean
have h_a' : ... = 0 := by
  rw [LinearMap.sub_apply, map_sub]
  ...
  rw [LinearMap.comp_apply]   -- ❌ failed to fire
  ...
```
**Error:** `Tactic rewrite failed: Did not find an occurrence of the pattern (?f ∘ₛₗ ?g) ?x in the target expression (S.Cbar C) (↑d.symm ↑((projL1' S) e0)) = …`. The reason: `(C ∘ₗ ↑d.symm)` is presented with `↑d.symm` as the LinearEquiv-coercion (semilinear `∘ₛₗ`), not as a pure `∘ₗ` composition with two `LinearMap`s — so `LinearMap.comp_apply` doesn't match.

Workaround (raw log line 51 / ts 23:58:16, **success**) introduced a `rfl`-level helper:
```lean
have h_left : (LinearMap.range S.X0).mkQ ((C ∘ₗ d.symm) (a' : E'))
    = Cbar S C (d.symm (a' : E')) := rfl
```
This works because `Cbar S C v = mkQ (C v)` is definitional, so `rfl` unfolds the composition through the `↑d.symm` coercion automatically.

**Mathlib lemmas used:**
- `Submodule.ker_mkQ`, `Submodule.IsCompl.projection_add_projection_eq_self`, `Submodule.IsCompl.projection_apply`
- `Submodule.linearProjOfIsCompl_apply_{left,right}`
- `Submodule.exists_isCompl`, `LinearEquiv.ofInjective`, `LinearEquiv.ofInjective_symm_apply`
- `LinearMap.codRestrict`
- `IsCompl.disjoint.eq_bot`, `IsCompl.codisjoint.eq_top`, `Submodule.mem_sup`

### Step 3 (UNCLOSED — single focused sorry remains, line 570)

**Status:** Single focused sorry inside `pNormalForm_witnesses_aux`'s Step 3 existential.

**What's needed:**
After `leviGL_E_conj_XCB d` and `uD_conj_XCB D`, the conjugated operator becomes `XCB(CST Sₕ, B'')` where
```
B'' = lambdaDualE d.symm ∘ B ∘ d.symm
      + (Cdual D ∘ C - Cdual C ∘ D - Cdual D ∘ X0 ∘ D) ∘ d.symm
```
To match `XST(Sₕ, T) = XCB(CST Sₕ, BST T)`, need `B'' = BST T` for some skew `T : L0' →ₗ L0`. This requires:
1. `B''(L1' ↪ E') = 0` — needs careful choice of `D|_{L1'}` via `vplusKerPairing_isPerfPair`.
2. `B''(L0' ↪ E') ⊂ L0` — follows from skewness propagation through Levi+unipotent transformations.

**Estimated effort:** ~120–150 lines (likely split into a `_step3_T_construction` helper and a `_step3_skewness` helper).

**Gap-classification:** technical difficulty, not impossibility. The blueprint is clear on the construction; this is purely formalization work.

## Target — `InducedOrbitToy/Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness` 🟡 PARTIAL (signature tightened, case-split landed; sorries unchanged in count)

### Signature change (Tier S #7 option (a))

The Round 9 helper had hypotheses `_hT₁ : IsSkewT T₁` and `_hT₂ : IsSkewT T₂`. Round 10 prover tightened to:
```lean
(hT₁ : T₁ ∈ S.Tset_circ) (hT₂ : T₂ ∈ S.Tset_circ)
```
Cascaded the rename in the call site (raw log line 69 / ts 23:27:52):
```lean
isParabolicElement_ringInverse_of_orbit_witness S hNondeg hChar Sₕ
  T₁ T₂ hT₁.1 hT₂.1 g hg hyeq      -- old
  T₁ T₂ hT₁ hT₂ g hg hyeq          -- new (full Tset_circ data passed)
```

This exposes both `MaximalRank T_i` and `IsSkewT T_i` inside the helper, so the case-split branch can use the rank data to derive `ker T_i = ⊥` in the easy cases.

### Case-split body restructure

The Round 9 helper carried 2 sorries on a bundled conjunction `ker XST T₁ = flagE ∧ ker XST T₂ = flagE` (line 563) plus a flagEV0 sorry (line 624).

Round 10 restructured this as a `by_cases h_easy : ¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))`:
- **Easy branch (`h_easy = true`):** `ε = -1` OR (`ε = +1` AND even `l`). In both, `MaximalRank T_i = dim L0'`, so rank-nullity gives `ker T_i = ⊥` and `ker_XST_eq_flagE_of_injective` closes the kernel-equality conjunct **sorry-free**.
- **Hard branch (`h_easy = false`, ε=+1, l odd):** `MaximalRank T_i = dim L0' - 1`, kernel equality fails. **Single focused sorry at line 588** (was 563).
- **flagEV0 conjunct:** still requires `parabolic_decompose` infrastructure (Tier S #6); **single focused sorry at line 649** (was 624).

### Net effect on Orbits.lean

- Internal sorry token count: 2 → 2 (positions changed; `588` ε=+1-odd-case kernel + `649` flagEV0).
- Declaration-use warning count: 1 → 1 (single helper carries both sorries).
- File compiles in isolation (`lake env lean InducedOrbitToy/Orbits.lean` → single declaration warning at 524).
- **Significant qualitative improvement:** the easy 2/3 of the `eps × parity` cases now close constructively without going through the bundled-conjunction sorry; only ε=+1+odd remains. This makes the surviving sorries genuinely focused on the documented Tier S #6/#7 deferral rather than blocking the whole helper.

## Target — `InducedOrbitToy/Slice.lean :: parabolic_decompose` ✅ NO WORK (correctly deferred)

Per PROGRESS.md Round 10 directive: verify-only, no edits. Slice prover correctly followed the directive; file unchanged. Single sorry at 1572 (declaration warning at 1109).

## Targets — `Basic.lean`, `LocalForms.lean`, `X0Geometry.lean` ✅ NO WORK

All three "not assigned" provers correctly verified isolation, wrote brief "no work" reports, and made no edits. `X0Geometry.lean` retains its single pre-existing intentional `unused variable hlambda` lint at line 221 (autoformalized signature).

## Key findings / proof patterns discovered (Round 10)

1. **`Submodule.prodEquivOfIsCompl_symm_apply_{left,right}` requires named args.** The `p, q : Submodule R E` are explicit (from `variable (p q : ...)`), so pass them via `(p := ...) (q := ...)` rather than relying on inference from `IsCompl`. (Discovered after 3 failed unnamed-arg attempts in raw log lines 32, 34, 36; closed via raw log line 38.)

2. **`LinearMap.comp_apply` rewrite fails on LinearEquiv-coerced compositions.** `(C ∘ₗ ↑d.symm) x` may not match the `(?f ∘ₛₗ ?g) ?x` pattern when `↑d.symm` is the coercion `LinearEquiv → LinearMap`. Workaround: introduce a `rfl`-level helper or use `show` to convert via definitional unfolding (e.g., `Cbar S C v = mkQ (C v)`). (Discovered raw log line 50; closed line 51.)

3. **`linear_combination` over a generic `Field F` needs `CommSemiring`.** Don't use `linear_combination hsum` for vector identities like `n = z - k` from `k + n = z` over a generic field on a non-`CommSemiring`. Instead, derive consequences directly: e.g., `Cbar k + Cbar n = Cbar z` via `← map_add`. (Same caution as the Round 9 `linarith`-on-modules anti-pattern.)

4. **`LinearEquiv.ofInjective_symm_apply` for sectioning a partial injection.** When you need a section of `f : M →ₗ N` defined on `range f`, use `LinearEquiv.ofInjective f h : M ≃ₗ range f`, then `phi.symm` gives the section. The simp lemma `LinearEquiv.ofInjective_symm_apply` gives `f (phi.symm y) = (y : N)`. (Used in Step 2b for the `D := K_X.subtype ∘ₗ phi.symm ∘ₗ diff_cod` lift.)

5. **`mkQ` kernel identity.** `Submodule.ker_mkQ : (M.mkQ).ker = M`. Pattern: to show `x ∈ M`, prove `M.mkQ x = 0` and then `rw [Submodule.ker_mkQ]` on the membership. (Used in Step 2a.)

6. **`Cbar S C v = mkQ (C v)` is definitional.** The `noncomputable def Cbar (C : ...) := (range X0).mkQ ∘ₗ C` unfolds via `rfl` to the composition. Useful for bridging `mkQ ((C ∘ₗ f) x)` to `Cbar S C (f x)`. (Used as the `rfl`-level workaround in Step 2a after `LinearMap.comp_apply` failed.)

7. **`IsCompl` orientation matters at the `obtain` site.** When `Submodule.exists_isCompl K` returns `⟨K', hK'_compl⟩`, the orientation is `IsCompl K K'` (kernel first). Use `Submodule.mem_sup` accordingly, or flip with `hK'_compl.symm`. (Round 9 carry-forward bug, fixed in Round 10 Step 0.75.)

8. **`Tset_circ` data unlocks rank-based kernel reasoning.** Replacing `IsSkewT` with `T ∈ Tset_circ` exposes both skewness AND `MaximalRank` info, which is what the case split needs (`MaximalRank = dim L0' ⇒ ker T = ⊥` via rank-nullity). Reusable for any future helper that does case-by-rank.

9. **Case-split on `eps × parity` for slice-form arguments.** The `by_cases h_easy : ¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))` pattern cleanly separates the kernel-of-XST cases. The two easy cases (ε=-1 OR ε=+1+even) close via the same lemma (`ker_XST_eq_flagE_of_injective`); the ε=+1+odd case requires Bruhat-decomposition (Tier S #6/#7).

## Process anti-patterns (Round 10 lessons learned)

1. **❌ Continued LSP-MCP avoidance.** Round 10 used 0 `lean_diagnostic_messages`, 0 `lean_leansearch`, 0 `lean_loogle` calls — same anti-pattern as Round 9. Manual `grep -rn` against the local mathlib mirror (5 invocations) substituted for `lean_loogle` searches. **The LSP MCP is faster and cheaper; the harness should consider escalating this to a hard pre-flight check.**

2. **✅ Diagnostic discipline AFTER edits — recovered.** Unlike Round 9 (where the prover claimed green without re-verifying), Round 10 ran `lake env lean InducedOrbitToy/NormalForm.lean` after every single batch of edits (raw log lines 17, 21, 23, 33, 35, 37, 39, 50, 52). This is the explicit lesson learned from Round 9 finally being applied.

3. **✅ Iterative refinement on rewrite failures.** The Step 1 `prodEquivOfIsCompl_symm_apply_left` mismatch took 3 tries to close (named args eventually worked). The prover did not give up or insert sorry; they continued iterating until the rewrite fired. This is the right pattern.

## Cumulative reduction (sessions 1–12)

22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → 5 (end of session 8) → 3 (end of session 9) → 3 (end of session 10) → 3 declaration warnings + build RED (end of session 11) → **3 declaration warnings + build GREEN (end of session 12)**.

**Round 10 net: STRUCTURAL RECOVERY.** Plan target was 3 → 1 or 2; achieved 3 → 3 declaration warnings, but:
- Build recovered RED → GREEN (the Round 9 regression repaired).
- Internal sorry tokens 7 → 4 (4 closures: NormalForm Steps 0.75 fix-1, 0.75 fix-2, Step 1, Step 2).
- `pNormalForm_residual_orbit_iso`, `kernelImage_*` confirmed CLEAN axioms.
- `pNormalForm` is one Step-3 closure (estimated 120–150 lines) away from being axiom-clean.
- The Orbits helper is now case-split with the two surviving sorries clearly isolated to the documented Tier S #6/#7 deferred cases (ε=+1+odd kernel + flagEV0).

## Recommendations for next session (Round 11)

See `recommendations.md` in this folder.
