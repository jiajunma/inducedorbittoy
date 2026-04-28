# InducedOrbitToy/NormalForm.lean (Round 10)

## Summary

**Build status: GREEN** (`lake build` succeeds; `lake env lean InducedOrbitToy/NormalForm.lean` compiles).

**Sorry delta in `pNormalForm_witnesses_aux`:** 5 → 1 (closed Step 0.75 build break + Step 1 + Step 2; Step 3 remains).

**Public-theorem axiom audit:**
- `pNormalForm_residual_orbit_iso`, `kernelImage_ker`, `kernelImage_im`, `kernelImage_dim` —
  `[propext, Classical.choice, Quot.sound]` (clean).
- `pNormalForm` — transitive `sorryAx` (via the lone Step 3 sorry inside `pNormalForm_witnesses_aux`).

No new `axiom` declarations introduced.

---

## `pNormalForm_witnesses_aux` (line 197) — five sub-goals

### Step 0 (sorry-free, inherited from R9)
`Sₕ : L1' ≃ Vplus` via `LinearEquiv.ofFinrankEq`.

### Step 0.5 (sorry-free, inherited from R9)
Dimension chain: `h_Cbar_surj`, `h_dim_ker_Cbar`, `h_dim_L0'`, `h_dim_match`.

### Step 0.75 — build-break fixed (closed)
**Bug 1: variable swap.** R9 had
```lean
obtain ⟨k, hk_K', n, hn_ker, hsum⟩ := hz_top
```
but `hK'_compl : IsCompl (LinearMap.ker (Cbar S C)) K'`, so `Submodule.mem_sup` on
`(ker Cbar) ⊔ K'` yields `k ∈ ker(Cbar)`, `n ∈ K'`. The names were reversed.

**Fix:** Swapped to
```lean
obtain ⟨k, hk_ker, n, hn_K', hsum⟩ := hz_top
have hCbar_k : Cbar S C k = 0 := hk_ker
refine ⟨⟨n, hn_K'⟩, ?_⟩
```
and rewrote the `hbot` membership to use `(ker Cbar) ⊓ K'` matching `hK'_compl.disjoint.eq_bot`.

**Bug 2: `linarith` over a non-ordered field.** R9 had
```lean
have hk_eq : k = z - n := by linarith [hsum]
```
which fails on a generic `Field F` (no order).

**Fix:** Replaced the indirect `n = z - k` derivation with a direct `map_add`-style argument:
```lean
have hcbarsum : Cbar S C k + Cbar S C n = Cbar S C z := by
  rw [← map_add]; exact congrArg _ hsum
rw [hCbar_k, zero_add] at hcbarsum
rw [hcbarsum, hz]
```

### Step 1 (closed Round 10) — build `d : E' ≃ E'`
~85 lines.

**Key construction:**
1. `cbarK' : K' ≃ V0/range X0` via `LinearEquiv.ofBijective CbarK'_lin ⟨hCbarK'_inj, hCbarK'_surj⟩`.
2. `f : L1' ≃ K' := Sₕ ≪≫ₗ VplusEquivQuotientRange S.toX0Setup ≪≫ₗ cbarK'.symm`.
3. `prodEq_L : (L1' × L0') ≃ E'` via `Submodule.prodEquivOfIsCompl S.L1' S.L0' S.isComplL'`.
4. `prodEq_K : (K' × ker(Cbar)) ≃ E'` via `prodEquivOfIsCompl K' (ker Cbar) hK'_compl.symm`.
5. `dsymm := prodEq_L.symm ≪≫ₗ f.prodCongr gL0 ≪≫ₗ prodEq_K`.
6. `d := dsymm.symm`.

**Pointwise alignment:**
- `dsymm (a' : L1' ↪ E') = (f a' : K' ↪ E')` — via `prodEquivOfIsCompl_symm_apply_left`.
- `dsymm (b' : L0' ↪ E') = (gL0 b' : ker Cbar ↪ E')` — via `prodEquivOfIsCompl_symm_apply_right`.

**`hd_L1'`:**
- `Cbar((f a' : K') : E') = CbarK'_lin (f a') = cbarK' (f a')`.
- `cbarK' (f a') = cbarK' (cbarK'.symm (VplusEquivQuotientRange (Sₕ a'))) = VplusEquivQuotientRange (Sₕ a')`.
- `VplusEquivQuotientRange v = mkQ ((v : Vplus) : V0)` via `Submodule.quotientEquivOfIsCompl_symm_apply`.

**`hd_L0'`:**
- `Cbar((gL0 b' : ker Cbar) : E') = 0` — direct from `(gL0 b').2 : (gL0 b' : V0) ∈ ker Cbar`.

**Mathlib lemmas used:**
- `LinearEquiv.ofBijective`
- `LinearEquiv.prodCongr`
- `Submodule.prodEquivOfIsCompl`, `Submodule.prodEquivOfIsCompl_symm_apply_{left,right}`
- `Submodule.quotientEquivOfIsCompl_symm_apply`
- `LinearEquiv.apply_symm_apply`, `LinearEquiv.trans_apply`
- `ZeroMemClass.coe_zero`

**Gotcha:** `Submodule.prodEquivOfIsCompl_symm_apply_{left,right}` has `p, q : Submodule R E` as
*explicit* variables. Passing `S.isComplL'` first as the only arg fails to elaborate;
must use `(p := S.L1') (q := S.L0')` named args.

### Step 2 (closed Round 10) — build `D : E' →ₗ V0` lifting `(C ∘ d.symm - CST Sₕ)` through `X0`
~115 lines.

**Step 2a — `(C ∘ d.symm - CST Sₕ) e0 ∈ range X0`:**
Reduce to `mkQ-zero` via `Submodule.ker_mkQ`.  Decompose `e0 = (a' : E') + (b' : E')` via
`Submodule.IsCompl.projection_add_projection_eq_self S.isComplL'`.

- On `a' ∈ L1'`: `mkQ(C(d.symm a')) = Cbar S C (d.symm a') = mkQ(Sₕ a' : V0)` (by `hd_L1'`),
  and `CST Sₕ (a' : E') = (Sₕ a' : V0)` (computed via `projL1' (a' : E') = a'` and
  `linearProjOfIsCompl_apply_left S.isComplL'`). Difference under `mkQ` is zero.
- On `b' ∈ L0'`: `mkQ(C(d.symm b')) = Cbar S C (d.symm b') = 0` (by `hd_L0'`),
  and `CST Sₕ (b' : E') = 0` (via `projL1' (b' : E') = 0`).

**Step 2b — lift through X0:**
1. `obtain ⟨K_X, hK_X_compl⟩ := Submodule.exists_isCompl (LinearMap.ker S.X0)`.
2. `X0_K_X := S.X0 ∘ₗ K_X.subtype : K_X →ₗ V0`, injective via `K_X ⊓ ker X0 = ⊥`.
3. `range X0_K_X = range X0` proven via decomposition of any `v` as `n + k` with
   `n ∈ ker X0`, `k ∈ K_X`, then `X0 v = X0 k` since `X0 n = 0`.
4. `phi : K_X ≃ range X0_K_X := LinearEquiv.ofInjective X0_K_X hX0_K_X_inj`.
5. `diff_cod : E' →ₗ range X0_K_X` via `LinearMap.codRestrict` using
   `(C ∘ d.symm - CST Sₕ) e0 ∈ range X0_K_X` (from `h_diff_mem_range` and `h_range_eq`).
6. `D := K_X.subtype ∘ₗ phi.symm ∘ₗ diff_cod`.

**Verification `X0 ∘ D = diff`:**
- `X0 (K_X.subtype k) = X0_K_X k` (by `rfl`).
- `X0_K_X (phi.symm y) = (y : V0)` via `LinearEquiv.ofInjective_symm_apply`.
- `(diff_cod e0 : V0) = diff e0` (by `rfl` from `codRestrict`).

**Mathlib lemmas used:**
- `Submodule.ker_mkQ` (`(M.mkQ).ker = M`)
- `Submodule.IsCompl.projection_add_projection_eq_self`, `Submodule.IsCompl.projection_apply`
- `Submodule.linearProjOfIsCompl_apply_{left,right}`
- `Submodule.exists_isCompl`
- `LinearEquiv.ofInjective`, `LinearEquiv.ofInjective_symm_apply`
- `LinearMap.codRestrict`
- `IsCompl.disjoint.eq_bot`, `IsCompl.codisjoint.eq_top`, `Submodule.mem_sup`

**Gotcha:** the `LinearMap.comp_apply` rewrite on `(C ∘ₗ d.symm.toLinearMap)` failed to
match because the term is presented as `(C ∘ₗ ↑d.symm)` (with `↑d.symm` the LinearEquiv
coercion, semilinear `∘ₛₗ`). Worked around by introducing a `rfl`-level helper:
```lean
have h_left : mkQ ((C ∘ₗ d.symm) (a' : E'))
    = Cbar S C (d.symm (a' : E')) := rfl
```
(definitional unfolding of `Cbar S C v = mkQ (C v)`).

### Step 3 (UNCLOSED — focused sorry remains, line 570)

**Status:** Single focused sorry inside `pNormalForm_witnesses_aux`'s Step 3 existential.

**What's needed:**
After `leviGL_E_conj_XCB d` and combining with `uD_conj_XCB D`, the conjugated operator
becomes `XCB(CST Sₕ, B'')` where
```
B'' = lambdaDualE d.symm ∘ B ∘ d.symm
      + (Cdual D ∘ C - Cdual C ∘ D - Cdual D ∘ X0 ∘ D) ∘ d.symm
```
(after the `C' - X0 ∘ D = CST Sₕ` simplification from Step 2 design).

To match `XST(Sₕ, T) = XCB(CST Sₕ, BST T)`, need `B'' = BST T` for some skew `T : L0' →ₗ L0`.
This requires:
1. `B''(L1' ↪ E') = 0` — needs careful choice of `D|_{L1'}` via `vplusKerPairing_isPerfPair`.
2. `B''(L0' ↪ E') ⊂ L0` — follows from skewness propagation through Levi+unipotent transformations.

Both ingredients are doable but require:
- A more careful Step 2: instead of any lift D, use the freedom `D ↦ D + ψ` (where
  `ψ : E' →ₗ ker X0`) to enforce the L1'-vanishing on the corrected `B''`.
- A skewness-propagation lemma chaining `_hB`'s skewness through `lambdaDualE d.symm` and
  the `Cdual`-correction terms.

**Estimated effort:** ~120 lines (likely split into a `_step3_T_construction` helper and a
`_step3_skewness` helper).

**Gap-classification:** technical difficulty, not impossibility. The blueprint is clear
on the construction; this is purely formalization work.

---

## Public-theorem closure status

| Theorem | Round 10 axioms |
|---|---|
| `pNormalForm` | `[propext, sorryAx, Classical.choice, Quot.sound]` (transitive sorryAx via Step 3) |
| `pNormalForm_residual_orbit_iso` | `[propext, Classical.choice, Quot.sound]` (CLEAN) |
| `kernelImage_ker` | `[propext, Classical.choice, Quot.sound]` (CLEAN) |
| `kernelImage_im` | `[propext, Classical.choice, Quot.sound]` (CLEAN) |
| `kernelImage_dim` | `[propext, Classical.choice, Quot.sound]` (CLEAN) |

If Round 11 closes Step 3 (the lone remaining sorry in `pNormalForm_witnesses_aux`),
`pNormalForm` becomes axiom-clean.

---

## Reusable gotchas (carry forward)

1. **`Submodule.prodEquivOfIsCompl_symm_apply_{left,right}` requires named args.**
   The `p, q : Submodule R E` are explicit (from `variable (p q : ...)`), so pass them
   via `(p := ...) (q := ...)` rather than relying on inference from `IsCompl`.

2. **`LinearMap.comp_apply` rewrite fails on LinearEquiv-coerced compositions.**
   `(C ∘ₗ ↑d.symm) x` may not match the `(?f ∘ₛₗ ?g) ?x` pattern when `↑d.symm` is the
   coercion `LinearEquiv → LinearMap`. Workaround: introduce a `rfl`-level helper or
   use `show` to convert via definitional unfolding (e.g., `Cbar S C v = mkQ (C v)`).

3. **`linear_combination` over a generic `Field F` needs `CommSemiring`.**
   Don't use `linear_combination hsum` for vector identities like `n = z - k` from
   `k + n = z` over a generic field on a non-`CommSemiring`. Instead, derive consequences
   directly: e.g., `Cbar k + Cbar n = Cbar z` via `← map_add`.

4. **`LinearEquiv.ofInjective_symm_apply` for sectioning a partial injection.**
   When you need a section of `f : M →ₗ N` defined on `range f`, use
   `LinearEquiv.ofInjective f h : M ≃ₗ range f`, then `phi.symm` gives the section.
   The simp lemma `LinearEquiv.ofInjective_symm_apply` gives `f (phi.symm y) = (y : N)`.

5. **`mkQ` kernel identity.** `Submodule.ker_mkQ : (M.mkQ).ker = M`. Pattern: to show
   `x ∈ M`, prove `M.mkQ x = 0` and then `rw [Submodule.ker_mkQ]` on the membership.

6. **`Cbar S C v = mkQ (C v)` is definitional.**
   The `noncomputable def Cbar (C : ...) := (range X0).mkQ ∘ₗ C` unfolds via `rfl` to the
   composition. Useful for bridging `mkQ ((C ∘ₗ f) x)` to `Cbar S C (f x)`.

---

## Confirmation

- `lake env lean InducedOrbitToy/NormalForm.lean`: compiles (single sorry warning at line 197 from `pNormalForm_witnesses_aux`).
- `lake build`: GREEN (8033 jobs, 0 errors).
- `#print axioms pNormalForm`: `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx from Step 3 only).
- `#print axioms pNormalForm_residual_orbit_iso`: `[propext, Classical.choice, Quot.sound]` (CLEAN).
- `#print axioms kernelImage_ker`, `kernelImage_im`, `kernelImage_dim`: all `[propext, Classical.choice, Quot.sound]` (CLEAN).
- No new `axiom` declarations introduced.

---

## Next steps for Round 11

1. **Close Step 3 of `pNormalForm_witnesses_aux`.**
   - Refactor Step 2 to expose the freedom in `D|_{L1'}` (lift via `D := D₀ + ψ`
     where `ψ : E' →ₗ ker X0` is to-be-chosen).
   - Choose `ψ|_{L1'}` via `vplusKerPairing_isPerfPair` so that `B''(L1') = 0`.
   - Prove `B''(L0') ⊂ L0` via skewness propagation.
   - Define `T u := codRestrict L0 (B'' (u : E')) ...`.
   - Verify the conjugation equation via the chain
     `leviGL_E_conj_XCB → uD_conj_XCB → parametrizeX0PlusU_uniqueness`.
   - Estimated effort: ~150 lines.

2. **Once Step 3 closes:** `pNormalForm` is axiom-clean. Together with the Orbits Tier S #7
   helper (case 3 + flagEV0 deferred to polish), the prover stage advances to polish.
