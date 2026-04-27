# Session 6 — Prover Round 4 (Tier S #2 + #3 land; Slice cascade closes; Orbits cascade closes)

## Metadata

- **Session:** 6 (stage `prover`, Round 4 — three coupled provers).
- **Sorry count (declaration-use warnings) before round:** 7
  - `Slice.lean`: 1 (`parametrizeX0PlusU_existence` line 232 — Tier D, 2 internal scoped sorries)
  - `NormalForm.lean`: 5 (`pNormalForm_witnesses` 210, `residual_levi_extract` 330, `residual_levi_build` 363, `kernelImage_ker` 537+543 → 1 declaration with 2 internal sorries, `kernelImage_im` 595)
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` line 242 — Tier A deferred, 2 internal scoped sorries)
- **Sorry count (declaration-use warnings) after round:** **6** ✅ (−1)
  - `Slice.lean`: 0 ✅ (`parametrizeX0PlusU_existence` resolved — both internal sorries closed)
  - `NormalForm.lean`: 5 (unchanged; comment refs to removed `L0_isotropic` field at lines 344/357 are now stale but compile cleanly)
  - `Orbits.lean`: 1 (unchanged — `sIndependenceAndOrbitCriterion` lines 358 + 376; cascade lemmas updated)
- **Net change:** 7 → 6 declaration warnings (−1). Plan-agent's Round 4 target was 7 → 6, hit exactly.
- **Custom axioms introduced:** 0. `lean_verify` re-confirms `[propext, Classical.choice, Quot.sound]` for `c_eq_finrank_quotient`, `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_mem`, `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`. `main` shows `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx from the unchanged `sIndependenceAndOrbitCriterion`).
- **Build status:** `lake build` green at end of round (8033 jobs replayed/built; 6 sorry warnings + 1 pre-existing unused-variable lint at `X0Geometry.lean:221`).
- **Pre-processed log:** 136 events, 14 edits across 3 files (Basic, Slice, Orbits), 6 explicit `lean_goal` checks, 8 `lean_diagnostic_messages` checks, 13 lemma searches (mix of `lean_local_search`, `lean_loogle`, `lean_leansearch`), 1 explicit `lean_build` (the rest invoked via `Bash`).

## Process observation

Plan agent assigned **three** coupled files this round (Basic, Slice, Orbits — Tier S #2 + #3 plus their cascades). The harness still dispatched provers to all six files; non-objective provers (LocalForms, NormalForm, X0Geometry) correctly verified isolation, wrote brief "no work" reports, and made no edits.

The expected mid-round build break — Slice and Orbits fail until Basic lands its 4-conjunct UnipotentRadical and 4-field Lagrangian SliceSetup — was observed and resolved automatically when the sister provers finished. End-of-round `lake build` is green.

## Target 1 — `InducedOrbitToy/Basic.lean :: SliceSetup` + `UnipotentRadical` (Tier S #3 + #2) ✅ RESOLVED

### Tier S #3 — `SliceSetup` Lagrangian fields (line 131)

Audited `L0_isotropic` use sites first:
```bash
grep -rn "L0_isotropic" InducedOrbitToy/
```
Found only 2 *comment* references in `NormalForm.lean` (lines 344, 357) — no code uses the field. Safe to remove and replace with the Lagrangian quartet:

```lean
structure SliceSetup (F : Type*) [Field F] extends X0Setup F where
  paired : PairedSpaces F
  L1 : Submodule F paired.E
  L0 : Submodule F paired.E
  L1' : Submodule F paired.E'
  L0' : Submodule F paired.E'
  isComplL : IsCompl L1 L0
  isComplL' : IsCompl L1' L0'
  L1_paired : IsPaired paired.pairing L1 L1'
  L0_paired : IsPaired paired.pairing L0 L0'
  L1_isotropic_L0' : IsIsotropic paired.pairing L1 L0'
  L0_isotropic_L1' : IsIsotropic paired.pairing L0 L1'
```

Docstring rewritten to describe the Lagrangian decomposition.

### Tier S #2 — `UnipotentRadical` 4th conjunct (line 208)

Added `IsSkewAdjoint S.ambientForm f` as 4th conjunct of the carrier predicate. Updated docstring (`𝔲 = 𝔭 ∩ 𝔤` framing). Closure proofs:

- **`zero_mem'`** — new conjunct closed by `intro x y; simp [LinearMap.zero_apply, map_zero]`.
- **`add_mem'`** — destructured `⟨h1, h2, h3, h4⟩`/`⟨h1', h2', h3', h4'⟩` and discharged the new case via `linear_combination hf + hg`.
- **`smul_mem'`** — destructured + `linear_combination c * hf`.

#### Attempt log

| # | Attempt | Outcome |
|---|---|---|
| 1 | `linarith` for the IsSkewAdjoint sum | **Failed** — `linarith` requires an ordered field; `F` is generic `[Field F]` |
| 2 | `linear_combination hf + hg` (and `c * hf` for smul) | **Success** — canonical Mathlib idiom for linear-equality goals over rings/fields |

**Reusable insight (carry forward):** never use `linarith` on a generic `Field F` — switch to `linear_combination`. Same pattern reappeared in Slice and Orbits proofs this round.

## Target 2 — `InducedOrbitToy/Slice.lean :: parametrizeX0PlusU_existence` (Tier D) ✅ RESOLVED

Both internal scoped sorries closed; file is now sorry-free.

### `parametrizeX0PlusU_mem` (line 184) — cascade for tightened UnipotentRadical

`refine ⟨?_, ?_, ?_⟩` extended to `refine ⟨?_, ?_, ?_, ?_⟩` with new IsSkewAdjoint case:

```lean
intro x y
obtain ⟨e₁, v₁, e₁'⟩ := x
obtain ⟨e₂, v₂, e₂'⟩ := y
rw [XCB_sub_X0Lift_apply, XCB_sub_X0Lift_apply]
simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_add,
  LinearMap.add_apply, map_zero, mul_zero, add_zero, zero_add]
rw [Cdual_pairing_eq …, Cdual_pairing_eq …]
linear_combination hskewB - S.eps * hSym
  - S.formV0 (C e₁') v₂ * hε2
```

where `hskewB := _hB e₁' e₂'`, `hSym := S.epsSymm v₂ (C e₁')`, and `hε2 : S.eps * S.eps = 1` from `S.epsValid`.

### New helper `XCB_sub_X0Lift_apply`

```lean
private lemma XCB_sub_X0Lift_apply (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (e : S.paired.E) (v : S.V0) (e' : S.paired.E') :
    (XCB S C B - X0Lift S) (e, v, e')
      = (Cdual S C v + B e', C e', (0 : S.paired.E')) := by
  rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
  ext <;> simp
```

### IsSkewB scoped sorry (formerly line 256) — closed

Lifted `obtain ⟨hflagE, hflagEV0, hAll, hSkewY⟩ := _hY` (now 4-tuple after Tier S #2) to top of proof body. The IsSkewB conjunct of the destructured `_hB` discharges via `hSkewY (0,0,u) (0,0,v)`:

```lean
have h := hSkewY (0, 0, u) (0, 0, v)
simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
  LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
```

### E-component sorry (formerly line 294) — closed via auxiliary hypothesis

Strategy: prove `(Y (0, v, 0)).1 = Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v` via left-injectivity of the perfect pairing, then conclude.

```lean
have hY_v_E_eq : (Y (0, v, 0)).1 = Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v := by
  apply S.paired.isPerfect.1
  intro w
  have h := hSkewY (0, v, 0) (0, 0, w)
  simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
    LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
  rw [Cdual_pairing_eq S _hNondeg, hC_eq]
  linear_combination h
```

The original plan-agent worry about a sign discrepancy (suggesting `C := -(projV0 ∘ₗ Y ∘ₗ inE')`) did **not** materialise — the convention in the existing `Cdual_pairing_eq`/`XCB_apply` already produces the correct sign once `Cdual_pairing_eq` is applied at the test-vector level.

### Attempt log (Slice)

| # | Attempt | Outcome |
|---|---|---|
| 1 | Discharge IsSkewAdjoint case with naive `simp + ring` | Goal not closed — needed Cdual_pairing_eq + ε-symmetry |
| 2 | `simp only [..., Prod.fst_zero, Prod.snd_zero, ...]` | **Failed** — `Prod.fst_zero` / `Prod.snd_zero` don't exist; `map_zero` covers it |
| 3 | Drop the non-existent simp args; close with `linear_combination` over `hskewB`, `hSym`, `hε2` | **Success** |
| 4 | `linarith` for E-component scalar identity | **Failed** — generic Field, no ordering |
| 5 | `linear_combination h` after `Cdual_pairing_eq + hC_eq` rewrites | **Success** |
| 6 | `unused simp arg LinearMap.zero_apply` lint-as-error | Trimmed — left only the simp args that fire |

## Target 3 — `InducedOrbitToy/Orbits.lean` cascade (Tier S #2 cascade) ✅ RESOLVED

Cascade complete: `XCB_sub_X0Lift_mem_unipotent` and `XST_sub_X0Lift_mem_unipotent` now produce the 4-conjunct UnipotentRadical membership; call sites (`XST_mem_O0PlusU`, `inducedOrbits`, `main`) updated to thread `hNondeg` and `hT : IsSkewT T`.

### `XCB_sub_X0Lift_mem_unipotent` — Option A (signature change)

```lean
private lemma XCB_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  refine ⟨?_, ?_, ?_, hskew⟩
  -- 3 existing flag-stability proofs unchanged
```

### Three new private helpers

1. **`BST_apply`** (line 200, `rfl`): `BST S T u = ((T (projL0' S u) : S.L0) : S.paired.E)`.
2. **`projL1'_add_projL0'_eq`** (line 206): `↑(projL1' v) + ↑(projL0' v) = v`. Proof uses `Submodule.IsCompl.projection_add_projection_eq_self` plus `Submodule.IsCompl.projection_apply` to convert from the `IsCompl.projection` form to the `linearProjOfIsCompl`-coerced form. **Negative result documented:** `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` (returned by `leansearch`) **does not exist** in current Mathlib; use the `projection_*` variants.
3. **`lambda_L0_eq_lambda_L0_projL0'`** (line 217): for `x : S.L0`, `λ(↑x, v) = λ(↑x, ↑(projL0' v))`. Proof uses `conv_lhs => rw [← projL1'_add_projL0'_eq]` (bare `rw` rewrites every `v` including the one inside `projL0' S v` — must use `conv_lhs`). Then `S.L0_isotropic_L1'` kills the L1'-projection term. The `LinearMap.add_apply` rewrite cannot fire after `map_add` (the form becomes `(S.lambda x) y + (S.lambda x) z`, not `(?f + ?g) ?x`) — drop it from the rw chain.
4. **`IsSkewB_BST`** (line 230): `IsSkewT T → IsSkewB (BST T)`. Direct application of `lambda_L0_eq_lambda_L0_projL0'` twice plus `hT (projL0' u) (projL0' v)`.

### `XST_sub_X0Lift_mem_unipotent` — full rewrite

New signature adds `hNondeg : S.formV0.Nondegenerate` and `hT : S.IsSkewT T`. Body applies `XCB_sub_X0Lift_mem_unipotent` and discharges the IsSkewAdjoint goal via:

1. Destruct vectors, expand via `XCB_apply, X0Lift_apply, sub_apply`, then `ext <;> simp` for V0-component cancellation.
2. `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_add, ...]`.
3. `rw [Cdual_pairing_eq …, Cdual_pairing_eq …]` on the two `λ(Cdual ·, ·)` atoms.
4. `linear_combination hSkewB e₁' e₂' + (-S.eps) * hSym + (-(S.formV0 ((CST S Sₕ) e₁') v₂)) * hε2`.

Cancellation pattern (mirror of `parametrizeX0PlusU_mem`):

- `λ(Cdual C v₁, e₂') + B0(v₁, C e₂') = 0` (Cdual_pairing_eq)
- `B0(C e₁', v₂) - ε² · B0(C e₁', v₂) = 0` (ε-symmetry + ε² = 1)
- `λ(B e₁', e₂') + ε · λ(B e₂', e₁') = 0` (`IsSkewB_BST`, derived from `IsSkewT T` + `L0_isotropic_L1'` Tier S #3)

### Call-site updates

- `XST_mem_O0PlusU` (line 284) — added `hNondeg`, `hT : S.IsSkewT T` parameters; threads through to `XST_sub_X0Lift_mem_unipotent`.
- `inducedOrbits` (line 299) — renamed `_hT → hT`; added `hNondeg` parameter; passes `hT.1 : S.IsSkewT T` (extracted from `hT : T ∈ S.Tset_circ`).
- `main` (line 410) — renamed `_hNondeg → hNondeg`, `_hT → hT`; threads `hNondeg` through both calls.

### Attempt log (Orbits)

| # | Attempt | Outcome |
|---|---|---|
| 1 | `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` (per leansearch) | **Failed** — unknown constant |
| 2 | `lean_run_code` with `apply?` to find actual Mathlib name | Returns `Submodule.IsCompl.projection_add_projection_eq_self` |
| 3 | `simpa [projL1', projL0']` with naive coercion | Looping simp warning on `Submodule.IsCompl.projection_apply` |
| 4 | `rw [Submodule.IsCompl.projection_apply, …]` then `simpa` | **Success** |
| 5 | `rw [← projL1'_add_projL0'_eq]` | **Failed** — rewrites every `v`, breaking `projL0' S v` |
| 6 | `conv_lhs => rw [← h_eq]` | **Success** |
| 7 | `rw [map_add, LinearMap.add_apply, h_iso, zero_add]` | **Failed** — `LinearMap.add_apply` cannot fire after `map_add` distributes |
| 8 | `rw [map_add, h_iso, zero_add]` | **Success** |
| 9 | First IsSkewAdjoint discharge for `XST_sub_X0Lift_mem_unipotent` lacked the right `linear_combination` coefficients | Iterated to `hSkewB + (-ε)·hSym + …·hε2` |

## Key findings / patterns discovered

### `linear_combination` over generic Field
Three independent uses this round (Basic `add_mem'`, Slice `parametrizeX0PlusU_*`, Orbits `XST_sub_X0Lift_mem_unipotent` + helpers). Replaces the `linarith` reflex from session 5. Pattern: collect hypotheses `h₁, h₂, …` of the form `a₁ + a₂ + … = 0`, write the linear combination of them that algebraically equals the goal modulo `ring`, and Lean closes the rest.

### ε-symmetry + ε² = 1 cancellation
Used in both Slice's `parametrizeX0PlusU_mem` IsSkewAdjoint case and Orbits's `XST_sub_X0Lift_mem_unipotent` IsSkewAdjoint case. Same skeleton:
```lean
have hε := S.epsSymm
have hε2 : S.eps * S.eps = 1 := by rcases S.epsValid with h | h <;> simp [h]
have hSym : S.formV0 v₂ x = S.eps * S.formV0 x v₂ := hε _ _
linear_combination ... + (...) * hε2
```

### Vector equality via perfect-pairing left-injectivity
`(Y (0, v, 0)).1 = Cdual S C v` is reduced to a per-test-vector scalar identity via `S.paired.isPerfect.1`. Generalises to any "the V₀→E block of a skew-adjoint Y is a Cdual" argument. **Reusable.**

### Position-targeted rewriting with `conv_lhs`
Bare `rw [← lemma]` is unsafe when the rewrite-side term appears multiple times in the goal. Use `conv_lhs => rw [...]` (or `nth_rewrite`/`conv` blocks) to scope rewrites to the LHS only. Encountered when `projL1'_add_projL0'_eq S v` rewrote both the standalone `v` and the `v` inside `projL0' S v`.

### `LinearMap.add_apply` precedence vs `map_add`
After `map_add` (which rewrites `λ x (a + b) = λ x a + λ x b`) the resulting `+` is at the level of `F`-elements, so `LinearMap.add_apply` (which rewrites `(f + g) x = f x + g x`) does not fire. Drop redundant rewrites from `rw` chains when they fail to match.

### leansearch false positive
`Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` was returned by both `leansearch` and `loogle` searches but is not in current Mathlib. Always verify lemma names via `lean_run_code` `example`-blocks or `apply?` before relying on a search result.

## Cross-file mid-round breakage observed (and resolved)

Slice's prover finished its 4-tuple `obtain` before Basic landed → `expected 3, got 4` error. Same for Orbits's 4-conjunct `refine`. Each error was quietly resolved when the sister provers landed; final `lake build` is green. This matches the documented Round 4 parallel-safety expectation.

## Recommendations for next session

See `recommendations.md` for the prioritised next-round queue.

## Reusable patterns added to knowledge base

(Augments session-5 list. Updates flow into PROJECT_STATUS.md.)

- **`linear_combination` is the canonical tool over generic `Field F`.** Never `linarith` outside ordered fields.
- **`Submodule.IsCompl.projection_add_projection_eq_self` + `projection_apply`** is the right Mathlib API for `L₁ ⊕ L₀ = E` decompositions; the legacy `linearProjOfIsCompl_add_…` does not exist.
- **`conv_lhs`** (or `conv_rhs`) for position-targeted rewriting when the rewrite-LHS appears in multiple positions.
- **`map_add` vs `LinearMap.add_apply`** ordering in `rw` chains — after `map_add` the residual `+` is in the codomain, not the domain.
- **`hY_v_E_eq` aux-hypothesis pattern**: prove a vector equality by reducing to a per-test-vector scalar identity via the perfect-pairing's left-injectivity (`S.paired.isPerfect.1`), then close the scalar identity with `linear_combination` over a skew-adjointness instantiation.
- **Audit before structural edit**: `grep -rn '<field_name>'` before removing or renaming a structure field; comment-only references can be left, code references force escalation.
- **Mid-round build break is normal for tightly coupled Round-4-style cascades**; cross-file errors resolve when sister provers land. Provers should still write task_results and explicitly note the expected breakage.
