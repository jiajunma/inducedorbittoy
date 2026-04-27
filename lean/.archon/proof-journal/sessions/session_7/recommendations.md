# Recommendations for the Plan Agent — Round 6

## TL;DR

Round 5 closed cleanly (6 → 4 declaration warnings, exactly hit). The remaining 4 sorries are all on the **Levi-machinery dependency chain** (3 in `NormalForm.lean`) plus 1 deferred Tier A (`Orbits.lean`). Round 6 should be a **2-file dispatch**: `Slice.lean` (additive Levi machinery) + `NormalForm.lean` (consume the new Levi lemmas).

## Targets, prioritised

### 🟢 Closest to completion: 3 NormalForm.lean sorries unblocked structurally

All three (`pNormalForm_witnesses` 195, `residual_levi_extract` 319, `residual_levi_build` 348) are now blocked **only** on the Levi infrastructure — Tier S #3 + #4 (their other dependency) are now both landed.

**Recommended assignment:**
1. **`Slice.lean` prover (Round 6, half 1):** add ~60–100 additive lines for Levi-action machinery: `parabolic_decompose` lemma (decompose elements of the parabolic into Levi + unipotent factors), Levi-stable subspaces, the Levi action on `Vplus / range X0`. No structural edits to existing definitions; pure additive extension.
2. **`NormalForm.lean` prover (Round 6, half 2):** consume the new Slice lemmas to discharge the three sorries. The proof outlines are already sketched in the file's docstrings around lines 187–210, 307–330, 336–363.

**Expected sorry count after Round 6:** 4 → 1 (only `sIndependenceAndOrbitCriterion` would remain).

### 🟡 Deferred to Round 7: `sIndependenceAndOrbitCriterion`

This Tier A target needs:
- `pNormalForm_residual_orbit_iso` fully sorry-free (depends on Round 6).
- Added hypotheses `Nondegenerate` and `(2 : F) ≠ 0` likely required at the statement level (per `task_pending.md` Tier A note).
- A reduction of the two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s existence half.

**Do NOT assign in Round 6.** Plan agent should hold this until Round 6 closes.

## Approaches that showed promise this round (carry into Round 6)

### `lean_leansearch` natural-language for Mathlib-name discovery

In this session, `lean_loogle` returned `No results found` for several legitimate API queries (`Submodule.linearProjOfIsCompl_apply`, `Submodule.linear_proj_of_is_compl`, `linearProjOfIsCompl`). `lean_leansearch` with English-prose queries ("linear projection isCompl sum equals identity", "Submodule mem_sup decompose add element", "IsCompl.projection equals linearProjOfIsCompl") was the productive path — Round 6 prover should default to it.

### Bridge `IsCompl.projection_apply` ↔ `linearProjOfIsCompl`

The pattern of using `Submodule.IsCompl.projection_add_projection_eq_self` + `Submodule.IsCompl.projection_apply` to bridge between the two API surfaces was reusable this round. The Levi proof in Round 6 will likely need similar bridges for the Levi-vs-unipotent decomposition; document this as the canonical recipe.

### Inline obtain/cases on Codisjoint at Prop-conclusion sites

Trying to package "iso + property" as a `Subtype` (`{φ : … // ∀ w, …}`) inside a helper definition fails when the proof requires `cases` on `IsCompl.codisjoint` (`Exists.casesOn` Prop-eliminator restriction). The Round 6 Levi proofs may run into this if they want to factor "Levi witness + property" through a Subtype helper — inline at each Prop-conclusion call site instead.

## Approaches to avoid (carry into Round 6 prompts)

### `linarith` on generic Field `F`

Reappeared this round (edit #8 in NormalForm). `linear_combination` is the canonical replacement, but with a caveat (next item). Flag this in the Round 6 prover prompt.

### `linear_combination` on Module-element identities

NEW this round: `linear_combination` synthesises `CommSemiring`/`CommRing` on the **target type**. `S.E` is `AddCommGroup F + Module F` — not a `CommRing`. Vector identities over modules cannot be discharged with `linear_combination`; only scalar identities qualify. For module identities, drop to `rw` chains + `abel`.

This is a refinement of session 6's "linear_combination over generic Field" pattern — flag this boundary explicitly in the Round 6 prover prompt.

### Stale `leansearch` hits

`Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` is returned by `lean_leansearch` but does **not** exist in current Mathlib. Round 6 prompts should re-emphasize: always verify a search-returned name via `lean_run_code` (`#check` it) or `lean_multi_attempt` before relying on it.

### Explicit `LinearMap` coercions in `rw` arguments

Once a callee's signature switches from `LinearMap` to `LinearEquiv`, `rw [callee S _ (f : ... →ₗ ...) _]` will fail with `Application type mismatch`; Lean inserts the coercion automatically. Drop the explicit coercion. Round 6 will likely face similar coercion issues if the Levi machinery introduces new `LinearEquiv`-valued signatures.

## Stale comment hygiene

`NormalForm.lean` lines 344, 357 still reference the now-removed `L0_isotropic` field (Tier S #3, session 6). They are inside docstrings/comments and compile cleanly, but the Round 6 prover should refresh these as part of the `residual_levi_build` edit pass.

## Process observations to retain

- **Single-file Round-5 dispatch worked cleanly.** No mid-round build break (only one file edited). End-of-round build green on the first `lake build` invocation.
- **`#print axioms` verification.** Prover used `Bash` to run a one-off `/tmp/check_axioms.lean` that imported `InducedOrbitToy.NormalForm` and printed the axioms of all three target theorems. This is the right pattern when `lean_verify` is not directly available; consider promoting it into the Round 6 prover prompt as a closure check.
- **`lean_diagnostic_messages` over `lean_goal`.** This prover skipped explicit `lean_goal` checks (0 invocations) and relied on `lean_diagnostic_messages` (12 invocations) to drive iteration. Worked well for "is the file clean now?" loops. For more nuanced state inspection, the Round 6 prover should still use `lean_goal` at suspected sticking points.

## Concrete Round 6 task list (suggested)

For the plan agent to translate into PROGRESS.md objectives:

1. **`Slice.lean` (Round 6, additive)**:
   - Add `Levi` typeclass / definition factoring the parabolic into Levi + unipotent.
   - Add `parabolic_decompose : g ∈ Parabolic → ∃ ℓ ∈ Levi, ∃ u ∈ UnipotentRadical, g = ℓ * u`.
   - Add Levi-action lemmas: how Levi elements act on `Vplus / range X0`, on `L0 / L1`, on the dual pairings.
   - Estimated size: 60–100 lines additive. No structural changes to existing `SliceSetup` / `UnipotentRadical` / `parametrizeX0PlusU_*`.

2. **`NormalForm.lean` (Round 6, consume Levi machinery)**:
   - `pNormalForm_witnesses` (line 195): construct the explicit `Sₕ`, `T` witnesses using Levi action.
   - `residual_levi_extract` (line 319): extract Levi component from a parabolic element.
   - `residual_levi_build` (line 348): build a parabolic element from Levi + unipotent components. Refresh stale comments at lines 344, 357.

3. **Files NOT assigned Round 6:** `Basic.lean`, `LocalForms.lean`, `X0Geometry.lean`, `Orbits.lean`. The harness should still dispatch provers to these per protocol; provers should write "no work" reports and not edit.

4. **Round-6 success criterion:** sorry count 4 → 1. Only `sIndependenceAndOrbitCriterion` should remain.
