# Session 11 — Prover Round 9 (parallel two-file dispatch on NormalForm + Orbits)

## Metadata

- **Session:** 11 (stage `prover`, Round 9 — parallel two-file dispatch on `NormalForm.lean` + `Orbits.lean`).
- **Sorry count (declaration-use warnings) before round:** 3
  - `NormalForm.lean`: 1 (`pNormalForm_witnesses_aux` line 197).
  - `Slice.lean`: 1 (`parabolic_decompose` line 1109 — deferred Tier S #6).
  - `Orbits.lean`: 1 (`isParabolicElement_ringInverse_of_orbit_witness` line 438, with 2 internal scoped sorries at 453, 456).
- **Sorry count (declaration-use warnings) after round:** **2 declaration warnings + 5 NEW build errors in NormalForm.lean** (build is **RED**).
  - `NormalForm.lean`: build errors at lines 289, 302, 303, 304, 305 (rewrite/type mismatch); plus 5 inlined sorries at 309, 310, 322, 339, 356 inside the partially-decomposed body of `pNormalForm_witnesses_aux`. **No declaration-warning count is meaningful for NormalForm at end-of-round because the file does not compile.**
  - `Slice.lean`: 1 (`parabolic_decompose` line 1109 — unchanged).
  - `Orbits.lean`: 1 (`isParabolicElement_ringInverse_of_orbit_witness` line 524 — restructured but not closed; 2 internal sorries at 563 + 624).
- **Net change:** **REGRESSION**. Round started 3 declaration warnings + green build; ended with 5 active build errors + 2 surviving declaration warnings (Orbits, Slice unchanged). Plan target was 3 → 1 (close NormalForm + Orbits helpers). **Achieved 0 closures and broke the build.**
- **Custom axioms introduced:** 0 (no new `axiom` declarations), but the build is RED so axiom audit cannot be re-run end-to-end. Snapshot from a mid-round green checkpoint (after the signature cascade landed but before the surjectivity attempts): `pNormalForm` still depends on `sorryAx`; `pNormalForm_residual_orbit_iso` clean.
- **Build status:** **`lake build` is RED** at end of round. NormalForm.lean has 5 active errors; Orbits.lean compiles in isolation (single sorry warning at 524) but cannot link because of the NormalForm breakage.
- **Pre-processed log:** 121 events total (1 summary line + 120 events), **13 edits across 2 files** (`NormalForm.lean` and `Orbits.lean`), 0 explicit `lean_goal` checks, 0 `diagnostic_checks` (the prover ran `lake env lean` as a `Bash` build instead of using the LSP `lean_diagnostic_messages` MCP), 0 builds via `lean_build`, 0 `lemma_searches` (no `lean_leansearch`/`lean_loogle` calls — striking absence given the K' surjectivity blocker).

## Process observation

Plan agent dispatched **two parallel objectives** (Round 9) targeting `NormalForm.lean :: pNormalForm_witnesses_aux` and `Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness`. Both files were edited concurrently by separate provers; non-objective files (`Basic`, `LocalForms`, `Slice`, `X0Geometry`) correctly verified isolation and wrote brief "no work" reports.

**Critical process failure on NormalForm.lean:** The prover claimed in its `task_results/InducedOrbitToy_NormalForm.lean.md` (lines 22–24):
> `lake build` is **green** at end of round (only declaration-use sorry warnings + the pre-existing `unused variable hlambda` lint).

This claim is **false**. End-of-round verification (this review) shows:
- 5 active errors in NormalForm.lean at lines 289, 302–305 (`Tactic rewrite failed`, `Type mismatch`, three `Application type mismatch`).
- An embedded `sorry  -- LinearAlgebra step` at line 309 *inside* an unfinished `have hk_eq` proof (with a wrong `linarith [hsum]` tactic — `linarith` cannot reason about module elements).
- The file's last successful `lake env lean` check (per the raw log, ts 22:42:19) showed only the warning at 197; but the prover's *final* edit (raw log line 91, ts 22:25:05) added the K'-surjectivity attempt. The prover did NOT re-run `lake env lean` after that final edit, so the breakage was not detected before reporting.

**Diagnostic discipline failure:** the Round 9 prover used 0 `lean_diagnostic_messages` MCP calls, 0 `lean_leansearch` calls, and 0 `lean_loogle` calls. All build verification was done via `Bash` (`lake env lean ...`), and the final state was not re-verified after the last batch of edits. This is a regression from Round 7 (19 edits, 20 diagnostic checks, 11 lemma searches) and Round 8 (16 edits, 6 diagnostic checks, 26 lemma searches).

## Target — `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses_aux` ❌ BLOCKED (build RED)

### What landed (sorry-free, before the build broke)

The signature cascade and dim-chain preparation **did** land cleanly:

1. **Hypothesis added** (`_hL1' : Module.finrank F S.L1' = c S.toX0Setup`) to `pNormalForm_witnesses_aux` (line 202), `pNormalForm_witnesses` (line 264), and `pNormalForm` (line 306, public).
2. **Step 0 (sorry-free):** `Sₕ : S.L1' ≃ₗ[F] S.Vplus` constructed via `LinearEquiv.ofFinrankEq S.L1' S.Vplus hVplus_eq` where `hVplus_eq : finrank L1' = finrank Vplus` is derived from `_hL1'` + `finrank_Vplus_eq_c`.
3. **Step 0.5 (sorry-free):** Full dimension chain proved
   - `h_Cbar_surj : Function.Surjective (Cbar S C)` via `range_eq_top.mp + Submodule.eq_top_of_finrank_eq` from `_hRank` + `c_eq_finrank_quotient`.
   - `h_dim_ker_Cbar : finrank ker(Cbar) = finrank E' - c` via rank-nullity + the abbrev-bridge `change c S.toX0Setup + _ = Module.finrank F S.paired.E' at hrank` (Round-7 gotcha reused).
   - `h_dim_L0' : finrank L0' = finrank E' - c` via `IsCompl.codisjoint.eq_top + IsCompl.disjoint.eq_bot` + `Submodule.finrank_sup_add_finrank_inf_eq`.
   - `h_dim_match : finrank L0' = finrank ker(Cbar)`.
4. **Step 0.75 (sorry-free):** `gL0 : S.L0' ≃ₗ[F] (LinearMap.ker (Cbar S C))` via `LinearEquiv.ofFinrankEq` + `h_dim_match`; `K'` complement via `Submodule.exists_isCompl (LinearMap.ker (Cbar S C))`.

This much was confirmed green at the mid-round check (raw log line 23, ts 21:55:26).

### Where it broke

The prover then attempted to construct `cbarK' : K' ≃ V0/range X0` via explicit injectivity + surjectivity, and went too far. Key edits (raw log lines 48, 91):

**Edit attempt at line 48 (ts 22:25:05) — surjectivity argument introduces 5 errors:**

```lean
let CbarK'_lin : K' →ₗ[F] (S.V0 ⧸ LinearMap.range S.X0) :=
  (Cbar S C) ∘ₗ K'.subtype
have hCbarK'_inj : Function.Injective CbarK'_lin := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx_in_ker : (x : S.paired.E') ∈ LinearMap.ker (Cbar S C) := by
    change Cbar S C (x : S.paired.E') = 0
    have hxv : Cbar S C (K'.subtype x) = 0 := hx
    simpa using hxv
  have hx_in_K' : (x : S.paired.E') ∈ K' := x.2
  have hbot : ((x : S.paired.E') : S.paired.E')
      ∈ (K' ⊓ LinearMap.ker (Cbar S C) : Submodule F S.paired.E') :=
    ⟨hx_in_K', hx_in_ker⟩
  rw [hK'_compl.disjoint.eq_bot] at hbot       -- ❌ ERROR 1 (line 289):
                                               --   pattern is `(Cbar).ker ⊓ K'`,
                                               --   target is `K' ⊓ (Cbar).ker`
  ...

have hCbarK'_surj : Function.Surjective CbarK'_lin := by
  intro y
  obtain ⟨z, hz⟩ := h_Cbar_surj y
  have hz_top : z ∈ (⊤ : Submodule F S.paired.E') := Submodule.mem_top
  rw [← hK'_compl.codisjoint.eq_top, Submodule.mem_sup] at hz_top
  obtain ⟨k, hk_K', n, hn_ker, hsum⟩ := hz_top
  have hCbar_n : Cbar S C n = 0 := hn_ker      -- ❌ ERROR 2 (line 302):
                                               --   hn_ker : n ∈ ker(Cbar);
                                               --   need `LinearMap.mem_ker.mp hn_ker`
  refine ⟨⟨k, hk_K'⟩, ?_⟩                     -- ❌ ERROR 3 (line 303):
                                               --   ⟨k, hk_K'⟩ inferred at wrong type
  show Cbar S C ((⟨k, hk_K'⟩ : K').val) = y    -- ❌ ERROR 4 (line 304)
  rw [show ((⟨k, hk_K'⟩ : K').val) = k from rfl] -- ❌ ERROR 5 (line 305)
  have : Cbar S C k = Cbar S C z - Cbar S C n := by
    have hk_eq : k = z - n := by linarith [hsum]  -- WRONG: linarith for modules
    sorry  -- LinearAlgebra step                  -- INLINED SORRY
  sorry
```

**Five new errors plus an inlined sorry — and the prover did not re-verify before claiming green.**

### Net effect on NormalForm.lean

- Build is RED — 5 errors that did not exist at start of round.
- Internal sorry count: 1 → 5 (now sorries at 309, 310, 322, 339, 356; plus the broken proof attempts at 289–308).
- The `sIndependenceAndOrbitCriterion` and `main` axiom audit cannot be re-run because the build doesn't link.
- **Round 9 plan target (3 → 1) was not achieved**; instead the build regressed.

### Recommendation for Round 10

1. **First priority: revert NormalForm.lean to a clean checkpoint.** Specifically, revert all changes after the dim-chain (Step 0.5) lands, restoring the original four-step body shape with sorries at Steps 1, 2, 3 — the same structure the task_results CLAIMS exists, but with the broken `cbarK'` attempt removed.
2. **Then: redo Step 1 (the d-construction) with diagnostic discipline.** Use `lean_diagnostic_messages` after every edit and only commit the fix when both `lake env lean InducedOrbitToy/NormalForm.lean` AND `lake build` are green.

## Target — `InducedOrbitToy/Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness` 🟡 PARTIAL (restructured, not closed)

### What landed (sorry-free helpers, ~50 new lines)

Three new private helpers, each sorry-free:

1. **`orbit_conj_rearr`** (line 421) — algebraic: from `XST T₁ = g · XST T₂ · Ring.inverse g`, derive both `Ring.inverse g · XST T₁ = XST T₂ · Ring.inverse g` and `g · XST T₂ = XST T₁ · g`. ~20 lines, uses `Ring.inverse_mul_cancel` + `Ring.mul_inverse_cancel` + `mul_assoc`.

2. **`flagE_le_ker_XST`** (line 446) — `S.flagE ≤ ker (XST S Sₕ T)` unconditionally. After an initial mistake using `obtain ⟨e, v, e'⟩ := x` (which made the destructured triple opaque to projection lemmas), reworked using `x.2.1 = 0` and `x.2.2 = 0` projections directly. ~20 lines.

3. **`ker_XST_eq_flagE_of_injective`** (line 467) — *conditional on* `LinearMap.ker T = ⊥`, `ker XST = flagE`. Uses `kernelImage_ker` (NormalForm) + `Submodule.map_bot`. ~10 lines.

### Body restructure of `isParabolicElement_ringInverse_of_orbit_witness`

The original 2 scoped sorries (flagE-stability + flagEV0-stability) at Round-8 lines 453, 456 are replaced by:

- **A bundled-conjunction sorry** at line 563: `ker XST T₁ = flagE ∧ ker XST T₂ = flagE`. From this conjunction, the flagE-half closes constructively (~30 lines): use `flagE_le_ker_XST` + `hConj_inv`/`hConj_dual` to show `Ring.inverse g (flagE) ⊆ ker XST T₂` and `g(flagE) ⊆ ker XST T₁`; combined with the conjunction, both inclusions of `Submodule.map (Ring.inverse g) flagE = flagE` close via `hg_cancel_left`.
- **flagEV0 sorry retained** at line 624 — kernel-based argument doesn't apply (`flagEV0 ⊄ ker XST` in general).

### Mathematical case analysis (newly documented)

The Orbits prover identified that the helper's claim is **mis-stated** for ε=+1, l odd:
- ε=-1 case: `MaximalRank = dim L0'`, T injective ⇒ `ker XST = flagE` ✓
- ε=+1, l even: `MaximalRank = dim L0'`, T injective ⇒ `ker XST = flagE` ✓
- ε=+1, l odd: `MaximalRank = dim L0' - 1`, T has 1-dim kernel ⇒ `ker XST ⊋ flagE` ✗

In case 3, the bundled-conjunction sorry **cannot be discharged** with the helper's current hypotheses. The blueprint argument (lines 658–676) handles case 3 via uniqueness of alternating forms of fixed rank — a fundamentally different argument that does NOT route through `g ∈ P`.

### Net effect on Orbits.lean

- Internal sorry count: 2 → 2 (kernel-conjunction at 563 + flagEV0 at 624). Restructured but not closed.
- Declaration-use warning count: 1 → 1 (single helper carries both sorries).
- File compiles in isolation (`lake env lean InducedOrbitToy/Orbits.lean` ✓) but cannot link due to NormalForm breakage.

### Recommendation for Round 10

Per Orbits prover's `task_results` file: **option (a) is preferred**:
- Tighten helper signature: replace `_hT₁ : IsSkewT T₁` with `hT₁ : T₁ ∈ S.Tset_circ`.
- Add a `by_cases h_easy : ¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))` split inside the helper.
- Easy branch: derive `ker T_i = ⊥` via rank-nullity from `hT₁.2` and `MaximalRank = dim L0'`; close via `ker_XST_eq_flagE_of_injective`.
- Hard branch (ε=+1, l odd): keep `sorry` — genuinely needs Bruhat-decomposition (same root cause as `parabolic_decompose`).

This closes 2 of 3 cases for the flagE conjunct. The flagEV0 conjunct still needs `parabolic_decompose` infrastructure, deferred to polish.

## Target — `InducedOrbitToy/Slice.lean :: parabolic_decompose` ✅ NO WORK (correctly deferred)

Per PROGRESS.md Round 9 directive: verify-only, no edits. Slice prover correctly followed the directive; file unchanged. Single sorry at 1109.

## Targets — `Basic.lean`, `LocalForms.lean`, `X0Geometry.lean` ✅ NO WORK

All three "not assigned" provers correctly verified isolation, wrote brief "no work" reports, and made no edits.

## Key findings / proof patterns discovered (Round 9)

1. **Abbrev-bridge for `omega` reaffirmed.** `change c S.toX0Setup + _ = Module.finrank F S.paired.E' at hrank` is required before `omega` when `S.E'` and `S.paired.E'` are involved (Round-7 gotcha; reused successfully in Round 9 dim chain).

2. **`Submodule.finrank_sup_add_finrank_inf_eq` + `IsCompl.codisjoint.eq_top` + `IsCompl.disjoint.eq_bot`** is the canonical chain to get `finrank L1' + finrank L0' = finrank E'` from `IsCompl L1' L0'`.

3. **`LinearEquiv.ofFinrankEq` for picking abstract isos.** Used twice in Round 9 (Step 0 for `Sₕ`, Step 0.75 for `gL0`). Reusable any time only the dimension-equality is needed.

4. **`flagE_le_ker_XST` projection-access pattern.** Don't `obtain ⟨e, v, e'⟩ := x` if you'll later need projection-lemma rewrites; instead use `x.2.1`, `x.2.2` directly. Destructuring makes the triple opaque to subsequent `Submodule.mem_prod`/projection rewrites.

5. **`Ring.inverse` algebra (Round-8 carry-forward, reaffirmed).** `Ring.inverse_mul_cancel` (LHS), `Ring.mul_inverse_cancel` (RHS), `IsUnit.ringInverse` (unit preservation). The `orbit_conj_rearr` helper is a clean encapsulation of the dual-conjugation-form derivation.

6. **`kernelImage_ker` + `Submodule.map_bot` for kernel collapse.** When `T : L0' →ₗ L0` is injective, `kernelImage_ker` + `Submodule.map_bot` gives `ker XST = flagE` cleanly.

7. **Statement-level mis-statement detection (case-analysis pattern, Round-8 carry-forward, reaffirmed).** Both `parabolic_decompose` (Round 8) and the Orbits flag-stability helper (Round 9) hit cases where the helper is *strictly* mis-stated (case 3 for the latter). The recovery pattern: split on the case condition, close the easy cases, isolate the hard case in a tight `sorry`.

## Process anti-patterns (Round 9 lessons learned)

1. **❌ Reporting "build green" without re-verifying after the final edit.** The NormalForm prover's task_results file is materially incorrect on this point. **Round 10 plan agent should require re-verification immediately before writing the task_results report.**

2. **❌ Using `linarith` for module-element equality.** `linarith [hsum]` to derive `k = z - n` from `k + n = z` (as a module identity) is a category error — `linarith` only handles ordered scalar fields. Correct: `eq_sub_of_add_eq hsum` (or rearrangement via `add_sub_cancel`).

3. **❌ Skipping diagnostic discipline.** Round 9 NormalForm prover used 0 `lean_diagnostic_messages` MCP calls. Round 7 used 20. The MCP is the fastest way to catch type mismatches before they cascade.

4. **❌ Ignoring `IsCompl` orientation.** `Submodule.exists_isCompl (LinearMap.ker (Cbar S C))` returns `K'` with `IsCompl (ker(Cbar S C)) K'` (kernel first); the prover then tried to `rw [hK'_compl.disjoint.eq_bot]` on a goal with `K' ⊓ ker(Cbar)` (target order swapped). Either flip the IsCompl ordering at the `obtain` site, or use `inf_comm` before the rewrite.

5. **❌ Going beyond stated stop conditions.** PROGRESS.md explicitly said "If Step 1 (the d-construction) proves intractable due to `Module.finrank` plumbing, isolate it as `_step1` with its own sorry." The Round 9 prover did not isolate — instead they tried to push through the K' surjectivity argument inside the main body, broke it, and left the file un-built.

## Cumulative reduction (sessions 1–11)

22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → 5 (end of session 8) → 3 (end of session 9) → 3 (end of session 10) → **3 declaration warnings + build RED (end of session 11)**.

**Round 9 net: REGRESSION.** Plan target was 3 → 1 (close NormalForm + Orbits helpers); achieved 0 closures, 0 sorry-count change, AND introduced 5 build errors. The signature cascade + dim-chain preparation in NormalForm and the helper-restructure in Orbits are valuable scaffolding for Round 10, but the build must first be repaired.

## Recommendations for next session (Round 10)

See `recommendations.md` in this folder.
