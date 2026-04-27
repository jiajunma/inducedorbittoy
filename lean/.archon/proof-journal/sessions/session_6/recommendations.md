# Round 5 Plan-Agent Recommendations (post-session-6)

## Targets to prioritise (Round 5)

Per the round plan in `PROGRESS.md`, Round 5 was scheduled to attack **Tier S #4 (`Sₕ` retyped as `LinearEquiv`) + close `kernelImage_ker`, `kernelImage_im`** in `NormalForm.lean`. Both are now unblocked because:

- Tier S #3 (Lagrangian fields `L0_paired`, `L1_isotropic_L0'`, `L0_isotropic_L1'`) landed in `Basic.lean` this round.
- The cascade through `Slice.lean` and `Orbits.lean` is closed; nothing else in Tier S #2/#3 is blocking.

### Closest to completion

| Theorem | File | Line | Status | Estimated effort |
|---|---|---|---|---|
| `kernelImage_ker` | `NormalForm.lean` | 537 + 543 (2 internal scoped sorries) | **Round 5 target** — needs Tier S #4 (Sₕ : LinearEquiv) + uses Tier S #3 fields landed this round | ~30 lines once Sₕ is retyped |
| `kernelImage_im` | `NormalForm.lean` | 595 | **Round 5 target** — needs Tier S #3 (landed) ✅; only Tier S #4 dependency remains | ~20 lines |

Both rely on the new `L1_isotropic_L0'` and `L0_isotropic_L1'` cross-isotropy fields that just landed. The proof skeleton from Orbits's `lambda_L0_eq_lambda_L0_projL0'` is directly reusable: cross-pairings vanish on the L1' (or L1) component of a Lagrangian decomposition.

### Already known-blocked (do not assign before Round 6)

| Theorem | File | Blocker |
|---|---|---|
| `pNormalForm_witnesses` | `NormalForm.lean:210` | Levi-action machinery (~60–100 lines additive in `Slice.lean`) |
| `residual_levi_extract` | `NormalForm.lean:330` | Levi machinery + `parabolic_decompose` lemma |
| `residual_levi_build` | `NormalForm.lean:363` | Levi machinery (Tier S #3 dependency now satisfied) |
| `sIndependenceAndOrbitCriterion` | `Orbits.lean:358 + 376` | `pNormalForm_residual_orbit_iso` must be sorry-free first; also missing `Nondegenerate` / `(2 : F) ≠ 0` hypotheses and `Sₕ`-equality refactor |

## Approaches that showed promise

### Plan-agent's "Option A" (signature-add-hypothesis)
For the `XCB_sub_X0Lift_mem_unipotent` cascade, Option A (add `(hskew : ...)` hypothesis to the helper) was clean and preserved the helper structure. Same idea may apply to `kernelImage_*` if it turns out we need a Lagrangian condition the caller already has — let the caller produce the hypothesis instead of the helper proving it.

### Auxiliary `_apply` helpers next to existing ones
`XCB_sub_X0Lift_apply` slotted in cleanly next to the existing `XCB_apply` / `X0Lift_apply` and was load-bearing for both the IsSkewAdjoint cascade and the E-component sorry. If `kernelImage_*` requires similar pointwise unfolding for `XST` decomposition, drop the helper next to the existing definitions.

### Cross-file proof-shape validation via `lean_run_code`
Prover validated the proof shape for `parametrizeX0PlusU_mem`'s IsSkewAdjoint case via `lean_run_code` `example`-blocks before the cross-file dependencies (Tier S #2 + #3 in `Basic.lean`) landed. Eliminated mid-round uncertainty during the parallel race. **Recommend reusing this pattern in Round 5** when `kernelImage_*` proofs depend on the Sₕ retyping and the Tier S #3 fields.

## Approaches that did NOT work

### `linarith` over generic Field
Reappeared as a dead-end three separate times this round (Basic add_mem', Slice IsSkewB, Slice E-component). **Carry forward as a hard rule:** generic `[Field F]` → never `linarith` → use `linear_combination`.

### `simp [Prod.fst_zero, Prod.snd_zero]`
These are not real Mathlib simp lemmas; `map_zero` covers the zero-projection case naturally.

### Bare `rw [← perfect_pair_decomp]`
Rewrites every occurrence of the test vector, breaking subterms that reference the same variable. Always use `conv_lhs => rw [...]` or `nth_rewrite`.

### `LinearMap.add_apply` after `map_add`
After `map_add` the addition is in the codomain and `LinearMap.add_apply` cannot fire. Drop it from such `rw` chains.

### `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self`
Returned by `leansearch` but does **not** exist in current Mathlib. The actual API is `Submodule.IsCompl.projection_add_projection_eq_self` plus `Submodule.IsCompl.projection_apply`. **Verify lemma names via `lean_run_code` examples before relying on search results.**

## Reusable proof patterns discovered this round

1. **`linear_combination` over `IsSkewAdjoint` instantiations.** Skeleton:
   ```lean
   have h := hSkewY (point1) (point2)
   simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
     LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
   -- h : scalar identity in λ, B0
   rw [Cdual_pairing_eq, …]
   linear_combination h
   ```
2. **Vector equality via perfect-pairing left-injectivity.** `S.paired.isPerfect.1` reduces a vector goal to a per-test-vector scalar identity. Apply to any "skew-adjointness forces V₀→E block to equal `Cdual` of the E'→V₀ block" argument.
3. **`conv_lhs`/`conv_rhs` for position-targeted rewrites.** Use whenever the rewrite-LHS appears in multiple positions in the goal.
4. **Cross-isotropy collapse via Lagrangian decomposition.** For `x : S.L0`, `λ(↑x, v) = λ(↑x, ↑(projL0' v))` follows from `projL1'_add_projL0'_eq` + `S.L0_isotropic_L1'`. Symmetric versions for L1, L1', L0'. Likely directly reusable in `kernelImage_*` proofs in Round 5.
5. **Audit-before-structural-edit.** `grep -rn '<field_name>'` before removing or renaming. If only comment refs found, safe to remove (refresh comments later). If code refs found, escalate.

## Documentation hygiene

`InducedOrbitToy/NormalForm.lean` lines 344, 357 — comment refs to the now-removed `L0_isotropic` field are stale. They compile cleanly (inside docstrings/comments) but should be refreshed when Round 5 touches the file (e.g., during `kernelImage_*` work).

## Suggested Round 5 specification (for plan agent)

**Files to assign:** `NormalForm.lean` only (Tier S #4 + close two `kernelImage_*` declarations).

**Likely Tier S #4 shape:** retype `Sₕ` from `S.L1' →ₗ[F] S.Vplus` to `S.L1' ≃ₗ[F] S.Vplus`. Audit existing call sites in `Slice.lean` (`parametrizeX0PlusU_mem` already takes Sₕ as a `LinearEquiv` per task_results) and `Orbits.lean` (`inducedOrbits`, `main`, `multiplicity*`) for the cascade. The cascade is likely just adding `(Sₕ : S.L1' →ₗ[F] S.Vplus)` coercions where the linear-map version was used — light editing.

**Likely `kernelImage_*` shape:** the two scoped sorries inside `kernelImage_ker` and the body of `kernelImage_im` follow from a Lagrangian-style block decomposition + the new `L1_isotropic_L0'` / `L0_isotropic_L1'` fields. Reuse Orbits's `lambda_L0_eq_lambda_L0_projL0'` + `IsSkewB_BST` patterns; if those helpers are needed in NormalForm.lean too, lift them to a shared file or restate locally.

**Round-5 sorry delta target:** 6 → 4 (close 2 declarations).

**Coupling:** moderate. Tier S #4 cascades into Slice + Orbits but the call-site updates are coercion-level only. Mid-round build break possible but small.
