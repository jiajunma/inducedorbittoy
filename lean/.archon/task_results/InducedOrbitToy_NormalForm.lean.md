# InducedOrbitToy/NormalForm.lean

## Summary

The file compiles cleanly (`lake env lean InducedOrbitToy/NormalForm.lean`
exits 0). Four `sorry` placeholders remain at:

* line 167  — `pNormalForm`
* line 199  — `pNormalForm_residual_orbit_iso`
* line 302  — `kernelImage_ker`
* line 397  — `kernelImage_im`

`#print axioms` for every public theorem reports only the standard
`propext / sorryAx / Classical.choice / Quot.sound`.  No custom `axiom`
was introduced.

`kernelImage_dim` is now **fully proved** (modulo the upstream sorry in
`kernelImage_ker`).

`lake build` is *not* green — but the only failure is in
`InducedOrbitToy/LocalForms.lean` (universe-level mismatch in the
`ClassifyBilinearForms` / `localFormClasses` definition; line 130 / 133),
which is **pre-existing** and unrelated to this file.  This prover did
not edit any other file.

## Helper definitions/lemmas added (all `private`)

* `XST_apply` — explicit Prod-formula for `XST S Sₕ T (e, v, e')`.
* `kerXST_submod_le_ker` — fully proves the easy direction
  `kerXST_submod ⊆ ker (XST S Sₕ T)`.
* `submoduleProdEquiv` — generic `↥(p.prod q) ≃ₗ[F] (↥p × ↥q)`.
* `finrank_submodule_prod` — `dim ↥(p.prod q) = dim p + dim q` via the
  preceding equiv.

## Per-theorem status

### `kernelImage_dim` (line 343) — RESOLVED

**Approach:** Reduce to `kernelImage_ker`, then compute
`finrank kerXST_submod`.

```
rw [kernelImage_ker S _hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) T _hT]
unfold kerXST_submod
rw [finrank_submodule_prod, finrank_submodule_prod]
rw [finrank_top, finrank_bot]
rw [Submodule.finrank_map_subtype_eq]
change Module.finrank F S.paired.E + _ = Module.finrank F S.paired.E + _
have hrank := LinearMap.finrank_range_add_finrank_ker T
omega
```

**Key Mathlib lemmas used:** `finrank_top`, `finrank_bot`,
`Submodule.finrank_map_subtype_eq`,
`LinearMap.finrank_range_add_finrank_ker`, `Module.finrank_prod`
(via `submoduleProdEquiv`).

**Caveat:** `omega` was confused by `S.E` vs `S.paired.E` (definitionally
equal but printed differently); `change … S.paired.E … = … S.paired.E …`
was the fix.

### `kernelImage_ker` (line 302) — PARTIAL (forward direction proved)

Forward direction `kerXST_submod ⊆ ker XST` is fully closed by
`kerXST_submod_le_ker`.

For the **reverse** `ker XST ⊆ kerXST_submod` direction, we now record:

* `hx1 : Cdual S (CST S Sₕ) v + (T (projL0' S e') : S.E) = 0`,
* `hx2 : S.X0 v + (Sₕ (projL1' S e') : S.V0) = 0`,
* `hX0v_zero : S.X0 v = 0`  (so `v ∈ ker X0`),
* `hSh_zero : (Sₕ (projL1' S e') : S.V0) = 0`.

Two final scoped `sorry`s remain inside `kernelImage_ker`:

1. `v ∈ ⊥` — needs `v = 0`, which requires `Cdual (CST Sₕ) v ∈ S.L1`
   (Lagrangian condition `λ(L1, L0') = 0`) plus `Sₕ` injective on
   `Vplus`, plus `Cdual restricted to ker X0` injective into `L1`
   (this last is `sDual_restrict_ker_isIso`, currently sorry'd in
   `X0Geometry.lean`).
2. `e' ∈ map L0'.subtype (ker T)` — needs the same Sₕ injectivity to get
   `projL1' e' = 0`, then `Cdual (CST Sₕ) v ∈ L1` to split the first
   equation via `IsCompl L1 L0`.

**Fundamental obstacle:** The current `SliceSetup` does *not* assume
`λ(L1, L0') = 0`.  Concretely, take `F = ℚ`, `E = E' = F²`, identity
pairing, `L1 = span (1,0)`, `L0 = span (0,1)`, `L1' = span (1,1)`,
`L0' = span (1,0)`: all `SliceSetup` axioms are satisfied, yet
`λ(L1, L0') = ab ≠ 0` for generic `(a,0) ∈ L1`, `(b,0) ∈ L0'`.  Without
this Lagrangian condition, `Cdual (CST Sₕ)` need not land in `L1`, and
the kernel formula `kerXST_submod = ⊤ × ⊥ × map L0'.subtype (ker T)` is
strictly *smaller* than the actual kernel.

**Recommendation for plan agent:** Either

* Strengthen `SliceSetup` to include `IsIsotropic λ S.L1 S.L0'`
  (or add it as an explicit hypothesis on `kernelImage_ker`,
  `kernelImage_im`, `kernelImage_dim`), **or**
* Restrict the kernel/image theorems to take `Sₕ : S.L1' ≃ₗ S.Vplus`
  consistently and add the Lagrangian condition as an explicit
  hypothesis.

### `kernelImage_im` (line 397) — UNRESOLVED, plan-comment included

Both directions of the equality require the Lagrangian condition
`λ(L1, L0') = 0` to land `Cdual (CST Sₕ) v` inside `L1`:

* **`imXST_submod ⊆ range XST`** is constructive but uses
  `sDual_restrict_ker_isIso` (sorry'd in `X0Geometry.lean`) plus a `k`
  correction in `ker X0` whose existence requires
  `a₁ - Cdual (CST Sₕ) w ∈ L1`, i.e. the Lagrangian condition.
* **`range XST ⊆ imXST_submod`** requires `Cdual (CST Sₕ) v ∈ L1`
  for any `v ∈ V0`.

The body is a single `sorry` with the detailed plan in the docstring.

### `pNormalForm` (line 167) — UNRESOLVED, blueprint plan included

The body remains `sorry`.  The blueprint outline is now in the docstring:

1. Use `_hRank` to pick a Levi-decomposed `Sₕ : L1' ≃ Vplus` and adjust
   `C` so `C|_{L1'} = Sₕ`, `C|_{L0'} = 0`.
2. Conjugate by some `u_D ∈ P` (`Slice.lean :: uD`) to absorb the
   `B|_{L1'}` block.
3. Verify the residual `T : L0' →ₗ L0` is skew, using `_hB` and
   `uD_conj_XCB`.

**Blocker:** Steps 2 and 3 rely on `uD`, `uD_conj_XCB`,
`parametrizeX0PlusU_*` from `Slice.lean`, all currently `sorry`.  The
formal proof can only proceed once `Slice.lean` is filled.

### `pNormalForm_residual_orbit_iso` (line 199) — UNRESOLVED, blueprint plan included

The body remains `sorry`.  The blueprint outline (now in the docstring):

* (→) Given `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` with `p` parabolic, the
  Levi-action descent gives `h : L_0' ≃ₗ L_0'` with
  `T₂ = (h⁻¹)^∨ T₁ h`, hence `BT T₁ ↦ BT T₂`.
* (←) Given an `h`-isometry of `BT T₁ ↦ BT T₂`, build `p` acting as
  `(h⁻¹)^∨ ⊕ id ⊕ h` on the block decomposition.

**Blocker:** Same as `pNormalForm` — relies on the unipotent-conjugation
machinery in `Slice.lean`.

## Compilation log

```
$ lake env lean InducedOrbitToy/NormalForm.lean
InducedOrbitToy/NormalForm.lean:167:8: warning: declaration uses `sorry`
InducedOrbitToy/NormalForm.lean:199:8: warning: declaration uses `sorry`
InducedOrbitToy/NormalForm.lean:302:8: warning: declaration uses `sorry`
InducedOrbitToy/NormalForm.lean:397:8: warning: declaration uses `sorry`
EXIT 0
```

## Axiom audit

```
'InducedOrbitToy.SliceSetup.kernelImage_dim'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'InducedOrbitToy.SliceSetup.kernelImage_ker'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'InducedOrbitToy.SliceSetup.kernelImage_im'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'InducedOrbitToy.SliceSetup.pNormalForm'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'InducedOrbitToy.SliceSetup.pNormalForm_residual_orbit_iso'
  depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

No custom `axiom` declarations were introduced.

## Pre-existing build issue (not caused by this prover)

`lake build` fails in `InducedOrbitToy/LocalForms.lean:130` and
`:133` with a universe-level mismatch:

```
Application type mismatch: ... S has type SliceSetup.{u_1, u_2, u_3, u_4} F
but is expected to have type SliceSetup.{u_1, u_5, u_6, u_7} F
```

This is in code I did not author or edit and is independent of any
change made here.  The plan agent should route this to whoever owns
`LocalForms.lean`.

## Recommended next steps

1. **Plan agent:** decide whether to strengthen `SliceSetup` with
   `IsIsotropic λ S.L1 S.L0'`, or to add this Lagrangian condition as an
   explicit hypothesis on `kernelImage_ker / _im / _dim`.  Without it,
   the kernel/image equalities cannot be proved as currently stated.
2. **Slice.lean prover:** finish `Cdual`, `Cdual_pairing_eq`,
   `parametrizeX0PlusU_*`, `uD`, `uD_*` so that `pNormalForm` and
   `pNormalForm_residual_orbit_iso` have the upstream lemmas they need.
3. **X0Geometry.lean prover:** finish `sDual_restrict_ker_isIso`, which
   `kernelImage_im`'s constructive direction depends on.
4. **LocalForms.lean owner:** repair the universe annotation on
   `ClassifyBilinearForms` (`@[classes]` resolver issue) so that
   `lake build` is green again.
