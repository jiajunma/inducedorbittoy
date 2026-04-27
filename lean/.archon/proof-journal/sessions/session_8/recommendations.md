# Recommendations for the Plan Agent — Round 7

## TL;DR

Round 6 closed cleanly on its primary objective: **helpers 1–7 of the Levi
machinery are sorry-free** in `Slice.lean` (14 new declarations,
`#print axioms` confirmed `[propext, Classical.choice, Quot.sound]` only).
Helper 8 (`parabolic_decompose`) was deferred to Round 7 with an explicit
`sorry` and a documented gap, per the PROGRESS.md stop condition.

The 4 → 5 declaration-warning increase is **deliberate** (additive only).
The plan agent should now dispatch **NormalForm.lean prover for Round 7**;
the Slice API is finalised. Round 7 should target sorry count **5 → 1**.

## Targets, prioritised

### 🟢 Closest to completion: 3 NormalForm.lean sorries (now structurally unblocked)

All three (`pNormalForm_witnesses` line 195, `residual_levi_extract` line 319,
`residual_levi_build` line 348) are blocked **only** on `parabolic_decompose`
choice (use it directly, or work around it). Tier S #3, #4, and Round-6
Levi infrastructure are all landed.

**Recommended Round 7 sequencing (per session-8 prover's task report):**

1. **`pNormalForm_witnesses` (NormalForm line 195)** — uses
   `leviGL_E_conj_XCB` (Slice.lean 6.5) to align `(C, B)` to a Levi-normalised
   form, then `uD_conj_XCB` to clear the residual. Estimated **~50 lines**.

2. **`residual_levi_extract` (NormalForm line 319)** — choose between:
   - **Option A:** Close `parabolic_decompose` first (additive, ~85 lines in
     `Slice.lean`), then use it directly (~10 lines in NormalForm).
     Total: **~95 lines** in 2 files.
   - **Option B (recommended by session-8 prover):** Skip
     `parabolic_decompose`; work directly via `parametrizeX0PlusU_uniqueness`
     + `leviGL_E_isParabolic` (~40 lines in NormalForm).
     Total: **~40 lines** in 1 file.

   Option B is cleaner: same prover, same file, no Slice.lean cascade
   risk. Option A is justified only if `parabolic_decompose` is itself
   needed for downstream (e.g., a future Round 8 cleanup or Tier A target).
   It currently is not.

3. **`residual_levi_build` (NormalForm line 348)** — construct
   `d : E' ≃ₗ E'` from the iso `h : L0' ≃ₗ L0'` via `IsCompl L1' L0'`,
   then `p := leviGL_E S d`. Estimated **~40 lines**.

   **Comment hygiene:** Refresh stale references to the now-removed
   `L0_isotropic` field at NormalForm.lean lines 344, 357 as part of this
   edit pass (carry-forward from session 7).

**Expected sorry count after Round 7:** 5 → 1 (under Option B) or 5 → 0
(under Option A — but only because Option A also closes
`parabolic_decompose`). Only `sIndependenceAndOrbitCriterion` (Orbits line
324, deferred to Round 8) would remain in either case.

### 🟡 Still deferred to Round 8: `sIndependenceAndOrbitCriterion`

This Tier A target needs:
- `pNormalForm_residual_orbit_iso` fully sorry-free (depends on Round 7).
- Added hypotheses `Nondegenerate` and `(2 : F) ≠ 0` likely required at the
  statement level (per `task_pending.md` Tier A note).
- A reduction of the two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s
  existence half.

**Do NOT assign in Round 7.** Hold until Round 7 closes.

## Approaches that showed promise this round (carry into Round 7)

### `lean_run_code` `#check` for known-name API verification

When the informal sketch (`informal/levi.md`) names the target Mathlib
lemma in a `-- Hint:` comment, jumping straight to `lean_run_code "import
Mathlib; #check @LinearMap.dualMap"` is faster than running a fuzzy
search. The Round 6 prover never invoked `lean_loogle` or `lean_leansearch`
(0 events) and still landed 14 sorry-free declarations. Workflow shift:
read informal doc → `lean_run_code` verify name → write proof. Round 7
should default to this when consuming the new Slice API.

### Block-matrix component-split closure pattern

`refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩` for
any `Module.End F (E × V0 × E')` identity, then close each component
individually. Used throughout Round 6's Levi proofs; Round 7 will need
similar splits for the NormalForm consumers.

### `show` to expose composed-application terms before `rw`

When `rw`-ing perfect-pairing identities through a `comp` argument and the
goal has `(f ∘ₗ g) e`, prepend `show ... f (g e) = ...` to surface the
nested-application form. Without it, `rw` cannot pattern-match the
identity. Used to fix `lambdaDualE_comp` after first attempt.

### `d.symm.symm = d` `rfl` for `LinearEquiv`

Halves the work of inverse-pair proofs: apply `leviGL_E_symm_inverse S
d.symm` directly for the other-direction inverse. Will recur in Round 7
if NormalForm constructs new `LinearEquiv` from `leviGL_E`-style blocks.

## Approaches to avoid (carry into Round 7 prompts)

### Symmetric `hgC` form for isometry hypotheses in `_conj_XCB`-style proofs

This was a 10-minute dead end this round. `Cdual_pairing` rewrites
asymmetrically produce `g v` (CoeFun) on the first arg and `(g : V0 →ₗ
V0) (C e'')` (LinearMap-coerced) on the second arg. State `hgC`
asymmetrically:

```lean
hgC : ∀ v e'', S.formV0 (g v) ((g : S.V0 →ₗ[F] S.V0) (C e'')) = S.formV0 v (C e'')
```

NOT:

```lean
hgC : ∀ v e'', S.formV0 ((g : ...) v) ((g : ...) (C e'')) = S.formV0 v (C e'')  -- WRONG: rw can't match
```

The two FunLike instances coexist; their reflexive equality doesn't help
syntactic pattern-matching. Round 7 may face the same issue if NormalForm
states isometry hypotheses for parabolic elements consumed by Slice's
`leviGL_*_isParabolic` lemmas.

### `linear_combination` on Module-element identities (carry-forward from session 7)

`linear_combination` synthesises `CommSemiring`/`CommRing` on the **target
type**. `S.E` is `AddCommGroup F + Module F` — not a `CommRing`. Vector
identities over modules cannot be discharged with `linear_combination`;
only **scalar** identities qualify. For module identities, drop to `rw`
chains + `abel`. Re-flag in Round 7's prover prompt.

### `linarith` on generic Field `F` (carry-forward from session 6)

Reappeared in session 7. `linear_combination` is the canonical replacement
(with the caveat above). Flag in Round 7 prompt.

### Stale `leansearch` hits (carry-forward)

`Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` is
returned by `lean_leansearch` but does **not** exist in current Mathlib.
Always verify a search-returned name via `lean_run_code` (`#check` it) or
`lean_multi_attempt` before relying on it.

### `#print axioms` syntax: drop the `@` prefix

Round 6 prover hit this typo: `#print axioms @lambdaDualE` fails with
`Unknown constant axioms`; correct form is `#print axioms lambdaDualE`
(no `@`). Trivial gotcha but worth flagging.

## Reusable patterns added to knowledge base (Round 6 contributions)

- **`show` to expose composed-application terms before `rw` perfect-pairing
  identities.**
- **Asymmetric isometry hypothesis form for `_conj_XCB`-style lemmas:**
  match the asymmetric form `Cdual_pairing` produces — first arg CoeFun,
  second arg LinearMap-coerced.
- **`d.symm.symm = d` `rfl` for `LinearEquiv`** halves inverse-pair proofs.
- **Block-matrix component-split closure:** `Prod.mk.injEq .. |>.mpr ⟨?_,
  Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩` for `Module.End F (E × V0 × E')`.
- **No-bundle definition pattern for `leviGL_V0`:** isometry hypothesis
  passed at consumer sites, sidestepping session-7 subtype-wrapping
  anti-pattern.
- **`#print axioms` without `@` prefix** is the correct syntax.

## Process observations to retain

- **Single-file Round-6 dispatch worked cleanly.** Only one file edited;
  no mid-round build break. End-of-round `lake build` green on first try.
  This is the second consecutive single-file round (sessions 7 and 8); the
  pattern is reliable.
- **Non-objective prover dispatch worked.** All 5 non-objective provers
  (`Basic`, `LocalForms`, `NormalForm`, `Orbits`, `X0Geometry`) verified
  isolation and wrote brief "no work" reports. The harness's tendency to
  dispatch all files is harmless under this protocol.
- **Bash-invoked `lake build` over MCP `lean_build`.** Round 6 prover used
  `Bash` for both `lake build` and `lake env lean InducedOrbitToy/Slice.lean`.
  Worked fine; faster than `mcp__lean-lsp__lean_build` for whole-project
  verification.
- **`lean_diagnostic_messages` over `lean_goal`.** Continues working well
  for "is the file clean now?" loops. Round 6 prover used 5 diagnostic
  checks and 0 explicit `lean_goal` checks.

## Concrete Round 7 task list (suggested for plan-agent translation into PROGRESS.md)

1. **`NormalForm.lean` (Round 7)** — single file, single prover:
   - `pNormalForm_witnesses` (line 195): use `leviGL_E_conj_XCB` +
     `uD_conj_XCB`. ~50 lines.
   - `residual_levi_extract` (line 319): **prefer Option B** — direct
     `parametrizeX0PlusU_uniqueness` + `leviGL_E_isParabolic`. ~40 lines.
   - `residual_levi_build` (line 348): construct `d : E' ≃ₗ E'` from `h
     : L0' ≃ₗ L0'`. ~40 lines. Refresh stale comments at lines 344, 357.

2. **(Optional) `Slice.lean` (Round 7 supplementary, if Option A is
   chosen):** close `parabolic_decompose` (~85 lines additive). Only
   needed if downstream code (Round 8 or Tier A) explicitly needs the
   structural decomposition; currently it doesn't.

3. **Files NOT assigned Round 7:** `Basic.lean`, `LocalForms.lean`,
   `Slice.lean` (if Option B), `X0Geometry.lean`, `Orbits.lean`. Standard
   "verify isolation and skip" protocol.

4. **Round 7 success criterion:** sorry count **5 → 1** (Option B) or
   **5 → 0** (Option A). Only `sIndependenceAndOrbitCriterion` should
   remain (or nothing, if Option A).

## Stale comment hygiene (carry-forward)

`NormalForm.lean` lines 344, 357 still reference the now-removed
`L0_isotropic` field. They are inside docstrings/comments and compile
cleanly, but the Round 7 prover should refresh these as part of the
`residual_levi_build` edit pass.

## Decision point for the plan agent

The choice between **Option A** (close `parabolic_decompose` first,
~95 lines across 2 files) and **Option B** (skip it, ~40 lines in 1 file)
should be made **before** PROGRESS.md is written. Recommendation:
**Option B** unless there is a downstream reason to want
`parabolic_decompose` proper (none currently identified). Option B is
strictly faster, lower risk (1 prover vs 2), and `parabolic_decompose`
can always be closed in a future cleanup round if needed.
