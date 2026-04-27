# InducedOrbitToy/NormalForm.lean — Round 5

## Summary

All three Round 5 objectives **RESOLVED**:

1. **Tier S #4** — `kernelImage_ker` retyped: `Sₕ : S.L1' ≃ₗ[F] S.Vplus`
   (was `S.L1' →ₗ[F] S.Vplus`). Underscore-prefixed `_hNondeg`/`_hT`
   replaced with `hNondeg`/`hT` (now used).
2. **`kernelImage_ker`** sorry-free (was 2 sorries at lines 537, 543).
3. **`kernelImage_im`** sorry-free (was 1 sorry at line 595).

`kernelImage_dim` call site updated to pass `Sₕ` directly without explicit
`LinearMap` coercion.

`lake build` is green; only 4 sorry warnings remain (3 in NormalForm.lean
for Round 6's Levi machinery, 1 in Orbits.lean for Round 7).

`#print axioms` for `kernelImage_ker`, `kernelImage_im`, `kernelImage_dim`
returns only `[propext, Classical.choice, Quot.sound]` — no custom axioms
or `sorryAx`.

## New helpers added (in NormalForm.lean)

| Helper | Purpose | Lines |
|---|---|---|
| `Cdual_CST_mem_L1` | For any `v : V0`, `Cdual S (CST S Sₕ) v ∈ L1`. | 472–516 |
| `kernelImage_DTD` | Packages `Cdual S (CST S Sₕ)` as a `DualTransposeData` for `sDual_restrict_ker_isIso`. | 518–544 |
| `lambda_isPerfPair_local` | Re-derives `S.lambda.IsPerfPair` from `S.paired.isPerfect`. (`Slice.lean`'s `lambda_isPerfPair` is private to that file.) | 546–562 |

## Proof outlines

### `Cdual_CST_mem_L1`
1. For each `l' ∈ L0'`, `λ(Cdual(CST Sₕ) v, l') = -formV0 v ((CST Sₕ) l')
   = 0` (using `Cdual_pairing_eq` + `(CST Sₕ) l' = 0` since `projL1' l' = 0`).
2. Decompose `Cdual(CST Sₕ) v = a + b` with `a ∈ L1`, `b ∈ L0` via
   `IsCompl L1 L0`'s `codisjoint`.
3. By `L1_isotropic_L0'`, `λ(a, l') = 0` for `l' ∈ L0'`. So
   `λ(b, l') = 0` for `l' ∈ L0'`.
4. By `L0_paired.2.1` (left injectivity of perfect pairing on `L0 × L0'`),
   `b = 0`. Hence `Cdual(CST Sₕ) v = a ∈ L1`.

### `kernelImage_ker` (reverse inclusion)
- The existing prefix gives `hX0v_zero`, `hSh_zero`, `hv_in_kerX0`.
- New: `Sₕ.injective` + `Subtype.ext` (Vplus.subtype injectivity) push
  `hSh_zero` to `projL1' e' = 0`.
- New: `Cdual_CST_mem_L1` + `(T (projL0' e')).2 ∈ L0` + `IsCompl L1 L0`
  give `Cdual(CST Sₕ) v = 0` and `(T (projL0' e') : E) = 0`.
- New: `sDual_restrict_ker_isIso S.toX0Setup hNondeg S.lambda
  (lambda_isPerfPair_local S) S.L1 S.L1' hL1'_eq_c Sₕ
  (kernelImage_DTD ...)` produces `φ : ker X0 ≃ L1`. Apply `φ` to
  `⟨v, hv_in_kerX0⟩`; combined with `Cdual(CST Sₕ) v = 0` and
  `φ.injective`, conclude `v = 0`.
- Goal `e' ∈ map L0'.subtype (ker T)`: witness is `projL0' S e'`. Use
  `Submodule.IsCompl.projection_add_projection_eq_self` +
  `Submodule.IsCompl.projection_apply` to get
  `(projL1' e' : E') + (projL0' e' : E') = e'`, then
  `(projL1' e' : E') = 0` from `projL1' e' = 0` to conclude
  `(projL0' e' : E') = e'`.

### `kernelImage_im`
**Forward (`range XST ⊆ imXST_submod`):** Direct from `XST_apply` +
`Cdual_CST_mem_L1` + `Submodule.mem_sup_left/right` for the L1 ⊕ image-T
split.

**Reverse (`imXST_submod ⊆ range XST`):** Constructive preimage:
- Decompose `a = a_L1 + a_T_e` via `Submodule.mem_sup`. Get `l : L0'`
  with `(T l : E) = a_T_e`.
- Decompose `b = b_V + r` via `IsCompl Vplus (range X0)`. Get
  `v_X0 : V0` with `X0 v_X0 = r`.
- Set `l1' := Sₕ.symm ⟨b_V, hb_V⟩` and `e' := (l1' : E') + (l : E')`.
- Build `φ : ker X0 ≃ L1` via `sDual_restrict_ker_isIso`. Set
  `target := ⟨a_L1 - Cdual(CST Sₕ) v_X0, _⟩ : L1`. Take
  `w_a := φ.symm target`; this gives
  `Cdual(CST Sₕ) (w_a : V0) = a_L1 - Cdual(CST Sₕ) v_X0`.
- Preimage triple: `(0, (w_a : V0) + v_X0, e')`.
- Verify components via `XST_apply` + `map_add` + the precomputed
  identities. The E-component closes via an explicit `abel` step
  (cancelling the `Cdual(CST Sₕ) v_X0` terms).

## `kernelImage_dim` call-site update

Line 783–784 (was 611):
```lean
-- Before:
rw [kernelImage_ker S _hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) T _hT]
-- After (Tier S #4):
rw [kernelImage_ker S _hNondeg Sₕ T _hT]
```

## Mathlib lemmas used

- `Submodule.linearProjOfIsCompl_apply_left/_right/_right'` — kill
  `projL1'`/`projL0'` of L0'/L1' inputs.
- `Submodule.IsCompl.projection_add_projection_eq_self` and
  `Submodule.IsCompl.projection_apply` — bridge between
  `IsCompl.projection` and `linearProjOfIsCompl` for the
  `projL1' e' + projL0' e' = e'` identity.
- `Submodule.mem_sup`, `Submodule.mem_sup_left`, `Submodule.mem_sup_right`
  — element decomposition along `IsCompl`.
- `Submodule.mem_map`, `LinearMap.mem_range` — unpack `map L0.subtype
  (range T)`.
- `LinearEquiv.finrank_eq` (`Sₕ.finrank_eq`) and `finrank_Vplus_eq_c`
  to derive `finrank L1' = c S`.
- `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`,
  `Subspace.dual_finrank_eq`, `LinearMap.IsPerfPair.mk` — replicating
  `lambda_isPerfPair`.
- `LinearEquiv.apply_symm_apply` — for `Sₕ (Sₕ.symm _) = _`.

## Failed approaches / dead-ends

- `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self`
  (the name leansearch initially returned) **does not exist**. The
  correct name is `Submodule.IsCompl.projection_add_projection_eq_self`.
- `linarith` does not work over generic `Field F` (needs
  `LinearOrderedField`); fail-fast lesson reinforced — use
  `linear_combination`/`abel` for module identities.
- `linear_combination` does not work directly on Module elements
  (needs `CommSemiring/CommRing`). For E/V0 component identities,
  prefer explicit rewrites + `abel` (already a known gotcha in
  `PROGRESS.md`).
- A `kerSDualEquiv` helper that returned a `Subtype` wrapping the iso
  + property fails because `Exists.casesOn` cannot eliminate into
  non-`Prop` types without `Classical.choice`. Inlining the
  `obtain` inside each `Prop`-conclusion theorem avoids this issue.
- The "let w := ⟨v, hv⟩" bind impedes `simpa` from reducing
  `w.val` to `v`. Working with the inline term `⟨v, hv_in_kerX0⟩`
  + `congrArg (fun w => (w : S.V0))` + `simpa` resolves it.

## Verification

`lake env lean InducedOrbitToy/NormalForm.lean` produces only the 3
expected sorry warnings (lines 195, 319, 348 — Round 6 work):

```
warning: InducedOrbitToy/NormalForm.lean:195:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:319:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:348:16: declaration uses `sorry`
```

`lake build` green at end of round (no errors, only the above 3
NormalForm sorries + 1 Orbits sorry + 1 pre-existing
`unused variable hlambda` lint).

`#print axioms` confirms no new axioms introduced:
- `kernelImage_ker`: `[propext, Classical.choice, Quot.sound]`
- `kernelImage_im`: `[propext, Classical.choice, Quot.sound]`
- `kernelImage_dim`: `[propext, Classical.choice, Quot.sound]`

## Statements changed

Only `kernelImage_ker`'s signature changed (Tier S #4):

```
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

`kernelImage_im` statement unchanged (already used `LinearEquiv` from
Round 4). `kernelImage_dim` statement unchanged.

`pNormalForm`, `pNormalForm_witnesses`, `residual_levi_extract`,
`residual_levi_build`, `pNormalForm_residual_orbit_iso`,
`IsParabolicElement` signatures and proof structures are **unchanged**
— only `kernelImage_*` and the `kernelImage_dim` call site were touched.

## Notes for the plan agent

- Comments at lines 344, 357 (in `residual_levi_build`) still reference
  the old `L0_isotropic` field. They are stale but do not break
  anything; refresh them when Round 6 work touches that proof.
- The `lambda_isPerfPair_local` helper is a near-duplicate of the
  private `lambda_isPerfPair` in `Slice.lean`. If a future refactor
  promotes the Slice version to public, remove the local copy.
