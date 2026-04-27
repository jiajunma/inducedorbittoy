# Session 7 — Prover Round 5 (Tier S #4 + `kernelImage_ker` / `kernelImage_im` cascade)

## Metadata

- **Session:** 7 (stage `prover`, Round 5 — single-file focused dispatch on `NormalForm.lean`).
- **Sorry count (declaration-use warnings) before round:** 6
  - `Slice.lean`: 0 (closed in session 6)
  - `NormalForm.lean`: 5 (`pNormalForm_witnesses` 195, `residual_levi_extract` 319, `residual_levi_build` 348, `kernelImage_ker` 537+543, `kernelImage_im` 595)
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` lines 358 + 376 — Tier A deferred)
- **Sorry count (declaration-use warnings) after round:** **4** ✅ (−2)
  - `NormalForm.lean`: 3 (only `pNormalForm_witnesses` 195, `residual_levi_extract` 319, `residual_levi_build` 348 — all Round 6 / Levi-blocked)
  - `Orbits.lean`: 1 (unchanged — Tier A, Round 7)
- **Net change:** 6 → 4 declaration warnings (−2). Plan-agent's Round 5 target was 6 → 4 (Tier S #4 + 2 `kernelImage_*` declarations); hit exactly.
- **Custom axioms introduced:** 0. `#print axioms` for `kernelImage_ker`, `kernelImage_im`, `kernelImage_dim` reports `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no custom axioms. Build verified by the prover via `Bash`-invoked `lake build` (8033 jobs, green).
- **Build status:** `lake build` green at end of round. Remaining warnings: 4 sorry declarations + 1 pre-existing unused-variable lint at `X0Geometry.lean:221`.
- **Pre-processed log:** 83 events (summary line + 82), 12 edits to a single file (`NormalForm.lean`), 0 `lean_goal` checks (this prover relied on `lean_diagnostic_messages` instead), 12 diagnostic checks, 0 explicit `lean_build` calls (lake invoked via `Bash`), 11 lemma searches (mix of `lean_loogle`, `lean_local_search`, `lean_leansearch`), 2 `lean_multi_attempt` invocations.

## Process observation

The plan agent assigned **one** file this round (`NormalForm.lean` — Tier S #4 retyping `Sₕ : S.L1' ≃ₗ[F] S.Vplus` plus closing the two `kernelImage_*` sorries that depended on it). The harness still dispatched provers to all six files; non-objective provers (`Basic.lean`, `LocalForms.lean`, `Slice.lean`, `Orbits.lean`, `X0Geometry.lean`) correctly verified isolation, wrote brief "no work" reports, and made no edits. The single objective prover landed all three Round 5 targets cleanly.

No mid-round build break this round (only one file edited). End-of-round `lake build` is green.

## Target — `InducedOrbitToy/NormalForm.lean :: kernelImage_ker` + `kernelImage_im` (Tier S #4 cascade) ✅ RESOLVED

### Tier S #4 — `kernelImage_ker` signature retyped

Changed `Sₕ` from `S.L1' →ₗ[F] S.Vplus` to `S.L1' ≃ₗ[F] S.Vplus`. Underscore-prefixed `_hNondeg` / `_hT` replaced with `hNondeg` / `hT` (now used). Body coerces `Sₕ` to a `LinearMap` via `(Sₕ : S.L1' →ₗ[F] S.Vplus)` at every call site.

```lean
-- Before:
theorem kernelImage_ker
    (_hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.ker (XST S Sₕ T) = kerXST_submod S Sₕ T

-- After (Round 5):
theorem kernelImage_ker
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.ker (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) =
      kerXST_submod S (Sₕ : S.L1' →ₗ[F] S.Vplus) T
```

`kernelImage_im` statement was already typed with `LinearEquiv` from session 5 — only its body changed. `kernelImage_dim`'s call site was updated to drop the explicit `LinearMap` coercion (line 783–784).

### New private helpers

| Helper | Purpose | Lines |
|---|---|---|
| `Cdual_CST_mem_L1` | For any `v : V0`, `Cdual S (CST S Sₕ) v ∈ L1`. | 472–516 |
| `kernelImage_DTD` | Packages `Cdual S (CST S Sₕ)` as a `DualTransposeData` for `sDual_restrict_ker_isIso`. | 518–544 |
| `lambda_isPerfPair_local` | Re-derives `S.lambda.IsPerfPair` from `S.paired.isPerfect`. (`Slice.lean`'s `lambda_isPerfPair` is private to that file.) | 546–562 |

### `Cdual_CST_mem_L1` outline

1. For each `l' ∈ L0'`, `λ(Cdual(CST Sₕ) v, l') = -formV0 v ((CST Sₕ) l') = 0`
   (using `Cdual_pairing_eq` + `(CST Sₕ) l' = 0` since `projL1' l' = 0`).
2. Decompose `Cdual(CST Sₕ) v = a + b` with `a ∈ L1`, `b ∈ L0` via `IsCompl L1 L0`'s codisjoint.
3. By `L1_isotropic_L0'`, `λ(a, l') = 0` for `l' ∈ L0'`. So `λ(b, l') = 0` for `l' ∈ L0'`.
4. By `L0_paired.2.1` (left injectivity of perfect pairing on `L0 × L0'`), `b = 0`.
   Hence `Cdual(CST Sₕ) v = a ∈ L1`.

### `kernelImage_ker` reverse inclusion — outline

- Existing prefix gives `hX0v_zero`, `hSh_zero`, `hv_in_kerX0`.
- New: `Sₕ.injective` + `Subtype.ext` (Vplus.subtype injectivity) push `hSh_zero` to `projL1' e' = 0`.
- New: `Cdual_CST_mem_L1` + `(T (projL0' e')).2 ∈ L0` + `IsCompl L1 L0` give `Cdual(CST Sₕ) v = 0` and `(T (projL0' e') : E) = 0`.
- New: `sDual_restrict_ker_isIso S.toX0Setup hNondeg S.lambda (lambda_isPerfPair_local S) S.L1 S.L1' hL1'_eq_c Sₕ (kernelImage_DTD …)` produces `φ : ker X0 ≃ L1`. Apply `φ` to `⟨v, hv_in_kerX0⟩`; combined with `Cdual(CST Sₕ) v = 0` and `φ.injective`, conclude `v = 0`.
- Goal `e' ∈ map L0'.subtype (ker T)`: witness is `projL0' S e'`. Use `Submodule.IsCompl.projection_add_projection_eq_self` + `Submodule.IsCompl.projection_apply` to get `(projL1' e' : E') + (projL0' e' : E') = e'`; combine with `(projL1' e' : E') = 0`.

### `kernelImage_im` — outline

**Forward (`range XST ⊆ imXST_submod`).** Direct from `XST_apply` + `Cdual_CST_mem_L1` + `Submodule.mem_sup_left/right` for the `L1 ⊕ image-T` split.

**Reverse (`imXST_submod ⊆ range XST`).** Constructive preimage:
- Decompose `a = a_L1 + a_T_e` via `Submodule.mem_sup`. Get `l : L0'` with `(T l : E) = a_T_e`.
- Decompose `b = b_V + r` via `IsCompl Vplus (range X0)`. Get `v_X0 : V0` with `X0 v_X0 = r`.
- Set `l1' := Sₕ.symm ⟨b_V, hb_V⟩` and `e' := (l1' : E') + (l : E')`.
- Build `φ : ker X0 ≃ L1` via `sDual_restrict_ker_isIso`. Set
  `target := ⟨a_L1 - Cdual(CST Sₕ) v_X0, _⟩ : L1`. Take `w_a := φ.symm target`;
  this gives `Cdual(CST Sₕ) (w_a : V0) = a_L1 - Cdual(CST Sₕ) v_X0`.
- Preimage triple: `(0, (w_a : V0) + v_X0, e')`.
- Verify components via `XST_apply` + `map_add` + the precomputed identities.
  E-component closes via an explicit `abel` step (cancelling the `Cdual(CST Sₕ) v_X0` terms).

### Attempt log (NormalForm.lean — 12 edits)

The 12 edits in `attempts_raw.jsonl` decompose into the following progression:

| # | Strategy | Outcome |
|---|---|---|
| 1 | Add `Cdual_CST_mem_L1` (initial draft) decomposing via `obtain` then `cases` on `IsCompl.codisjoint` | **Failed** — `Tactic 'cases' failed: recursor 'Exists.casesOn' can only eliminate into 'Prop'`. The `obtain` on a `Codisjoint` decomposition produced a non-`Prop` target. |
| 2 | Drop the `kerSDualEquiv` Subtype-wrapping helper that hit the same `Exists.casesOn` issue; inline the `obtain` inside each `Prop`-conclusion theorem instead | **Success** — diagnostics clean (no errors, only the pre-existing 3 sorry warnings at 195/319/348). |
| 3 | Retype `kernelImage_ker`'s `Sₕ` to `LinearEquiv` and rewrite reverse-inclusion proof with the new helpers | **Failed** at `kernelImage_dim` call site: `Application type mismatch: ↑Sₕ has type S.L1' →ₗ[F] S.Vplus but expected S.L1' ≃ₗ[F] S.Vplus in kernelImage_ker S _hNondeg ↑Sₕ` |
| 4 | Use `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` (per `lean_leansearch`) for `projL1' + projL0' = id` | **Failed** — unknown constant; lemma does not exist. |
| 5 | Try `lean_multi_attempt` to find right name → returns `Submodule.IsCompl.projection_add_projection_eq_self`; bridge to `linearProjOfIsCompl` form via `Submodule.IsCompl.projection_apply` | **Success** — clean. |
| 6 | Update `kernelImage_dim` call site: `rw [kernelImage_ker S _hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) T _hT]` | **Failed** — same type-mismatch as #3 (the explicit coercion in the rewrite confuses Lean once the signature changed). |
| 7 | Drop the `LinearMap` coercion: `rw [kernelImage_ker S _hNondeg Sₕ T _hT]` | **Success** — clean. |
| 8 | Implement `kernelImage_im` reverse inclusion with `linarith` for an `a + b - c = ?` algebraic step | **Failed** — `linarith failed to find a contradiction` (generic `Field F`, no ordering). |
| 9 | Replace `linarith` with `linear_combination -h1 + h2 + h3` | **Failed** — `failed to synthesize CommSemiring S.E` (E is not a commutative ring; `linear_combination` needs a `CommRing`/`CommSemiring`). |
| 10 | Replace `linear_combination` with explicit rewrites: `have h2 : … := by rw [h_phi_w_a]; rfl` then `rw [← h1, h2]` | **Failed** — `rfl` fails (`No goals to be solved` style mismatch — the `rw [h_phi_w_a]` already closes the goal). |
| 11 | Drop the spurious `rfl`: `have h2 : … := by rw [h_phi_w_a]` | **Success** — clean diagnostics. |
| 12 | Adjust `Sₕ` application form (`hSh_l1'`): use `((Sₕ : S.L1' →ₗ[F] S.Vplus) l1' : S.Vplus)` rather than `(Sₕ l1' : S.Vplus)`, and `simp [LinearEquiv.apply_symm_apply]` to discharge `Sₕ (Sₕ.symm _) = _`; introduce `hsuma'`, `hsumb'` aux equalities and an explicit `abel`-friendly E-component closure | **Success** — file builds clean, only the 3 unrelated sorry warnings remain. |

### Lemma searches (11 total)

Notable hits:
- `lean_leansearch "linear projection isCompl sum equals identity"` → `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` (false positive — does not exist) and `Submodule.IsCompl.projection_add_projection_eq_self` (correct).
- `lean_leansearch "linearProjOfIsCompl apply_eq_zero element of complement"` → `LinearMap.linearProjOfIsCompl_apply_right'` (used to kill `projL1'`/`projL0'` of L0'/L1' inputs).
- `lean_leansearch "Submodule mem_sup decompose add element"` → `Submodule.mem_sup` (used in the constructive preimage decomposition for `kernelImage_im`).
- `lean_leansearch "IsCompl.projection equals linearProjOfIsCompl"` → `Submodule.IsCompl.projection_apply` and `Submodule.coe_linearProjOfIsCompl_apply` (the bridge lemmas to convert between the two API forms).
- `lean_loogle "Submodule.linear_proj_of_is_compl"` and several variants returned `No results found` — `lean_leansearch`'s natural-language mode was the productive path.

## Key findings / patterns discovered

### `linear_combination` requires `CommRing`/`CommSemiring`

Discovered the hard way (edit #9): `linear_combination` does **not** work on Module elements over a non-commutative target (here, `S.E`, which is just an `AddCommGroup` + `Module F`). Even though scalar identities work fine over a `Field F`, **vector** identities must be discharged via explicit `rw` chains followed by `abel` (or `linear_combination` only on pre-extracted scalar pairs).

This is a refinement of session 6's "`linear_combination` over generic Field F" pattern — confirming the boundary: scalars yes, modules no.

### Subtype-wrapped `LinearEquiv` returners hit `Exists.casesOn` Prop-eliminator restriction

A natural design — package `kerSDualEquiv : {φ : … // ∀ w, ((φ w : S.L1) : S.E) = …}` returning a `Subtype` of a `LinearEquiv` plus a property — fails because the proof must `cases` on an `Exists`/`Codisjoint` that lives in `Prop`, but the goal type is the `Subtype` (which lives in `Type`). Inlining the `obtain` inside each `Prop`-conclusion theorem (where the goal is `Prop`) sidesteps the restriction.

**Reusable insight (carry forward):** if a helper definition involving `Codisjoint` / `IsCompl.codisjoint` decomposition fails with `Exists.casesOn can only eliminate into Prop`, inline the helper into each `Prop`-conclusion call site rather than attempting to package the iso + property as a `Subtype`.

### `let` impedes `simpa` reduction; prefer inline anonymous constructors

`let w := ⟨v, hv⟩` followed by `simpa` on a goal involving `w.val` does not always reduce. Working with the inline term `⟨v, hv_in_kerX0⟩` directly + `congrArg (fun w => (w : S.V0))` + `simpa` resolved it. (Documented as a dead-end in the prover's task_results file.)

### `LinearEquiv` coercion forms in `rw`

Once `kernelImage_ker`'s `Sₕ` was retyped to `LinearEquiv`, the `kernelImage_dim` call site failed when the `rw` argument was written `(Sₕ : S.L1' →ₗ[F] S.Vplus)` — Lean's elaboration prefers the bare `Sₕ` and inserts the coercion automatically. Drop explicit `LinearMap` coercions in `rw` argument lists when the function expects a `LinearEquiv`.

### `rfl` after `rw`-that-closes-the-goal

Edit #10's `rw [h_phi_w_a]; rfl` failed with `No goals to be solved` because `rw` already discharged the goal via the rewrite (the LHS and RHS were definitionally equal up to the rewrite). When debugging "should-be-trivial" tail tactics in proofs, drop redundant `rfl`/`exact rfl` pairs once the preceding `rw` is doing more work than expected.

### Two distinct `Sₕ` application forms in `LinearEquiv` proofs

`Sₕ l1'` (using the `CoeFun` instance for `LinearEquiv`) and `(Sₕ : S.L1' →ₗ[F] S.Vplus) l1'` (after coercing to `LinearMap`) both work but elaborate differently. For `simp [LinearEquiv.apply_symm_apply]` to fire on `Sₕ (Sₕ.symm _) = _`, the proof at hand needed the `LinearMap`-coerced form. `show` to specify the target form before `rw`/`simp`.

## Reusable patterns added to knowledge base

(Augments session 6 list; flows into PROJECT_STATUS.md.)

- **(NEW session 7) `linear_combination` is scalar-only over generic Modules.** It needs a `CommRing`/`CommSemiring` target. For vector identities over a Module, drop to explicit `rw` chains + `abel`.
- **(NEW session 7) `kerSDualEquiv` Subtype-wrapping anti-pattern.** When packaging "iso + property" via `Subtype`, an inner `obtain`/`cases` on a `Prop`-valued `Codisjoint` decomposition forces `Exists.casesOn` to eliminate into a `Type`. Solution: inline the construction at each `Prop`-conclusion call site.
- **(NEW session 7) `Submodule.IsCompl.projection_apply` + `projection_add_projection_eq_self` bridge.** Convert between the `IsCompl.projection` form (returns `S.E`) and the `linearProjOfIsCompl` form (returns the codomain `Submodule`) via `projection_apply`. Pattern is reusable for any `IsCompl L1 L0` decomposition where we must combine the two API surfaces.
- **(NEW session 7) Drop explicit `LinearMap` coercions in `rw` arguments** once a callee's signature switches from `LinearMap` to `LinearEquiv` — Lean inserts the coercion automatically and explicit annotations cause an `Application type mismatch`.
- **(NEW session 7) `lean_leansearch` natural-language > `lean_loogle` patterns** for projection and `IsCompl.projection_*` API discovery; `lean_loogle` returned `No results found` for several legitimate queries this round.

## Recommendations for next session

See `recommendations.md` for the prioritised next-round queue. Briefly: Round 6 work (`pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build`) is unblocked at the structural level (Tier S #4 done) but requires Levi-action machinery added additively to `Slice.lean` (~60–100 lines), which is the gating dependency.
