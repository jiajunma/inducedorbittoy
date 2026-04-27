# InducedOrbitToy/Orbits.lean — Round 4 (Tier S #2 cascade)

## Summary

Round 4 cascade for the tightened (4-conjunct) `UnipotentRadical` from
`Basic.lean`: updated `XCB_sub_X0Lift_mem_unipotent` and
`XST_sub_X0Lift_mem_unipotent` to produce/consume the new
`IsSkewAdjoint S.ambientForm` conjunct, threaded `hNondeg` through
`XST_mem_O0PlusU`, `inducedOrbits`, and `main`, and added three new
private helpers (`BST_apply`, `projL1'_add_projL0'_eq`,
`lambda_L0_eq_lambda_L0_projL0'`, `IsSkewB_BST`).

**Result:** Orbits.lean compiles in isolation. The only remaining
declaration-use `sorry` warning is line 324 (`sIndependenceAndOrbitCriterion`,
Tier A deferred to Round 7) — same as start of round.
`lake build` is green at end of round.
`#print axioms inducedOrbits` / `multiplicityNonDeg` / `multiplicityOddCase`
shows only `[propext, Classical.choice, Quot.sound]`. `main` shows
`[propext, sorryAx, Classical.choice, Quot.sound]` because of the
transitive call to `sIndependenceAndOrbitCriterion`.

## Changes

### `XCB_sub_X0Lift_mem_unipotent` (line 168) — RESOLVED (signature change)

**Approach (Option A, per plan-agent):** added explicit hypothesis
`(hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S))`. The 3
existing flag-stability conjuncts are unchanged; the 4th conjunct is
discharged by passing `hskew` directly into the `refine` block.

```lean
private lemma XCB_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  refine ⟨?_, ?_, ?_, hskew⟩
  -- 3 existing proofs unchanged
```

### `BST_apply` (line 200) — NEW (definitional helper)

Pointwise unfolding of `BST S T u`:
`BST S T u = ((T (projL0' S u) : S.L0) : S.paired.E)`. Closes by `rfl`
(since `BST = L0.subtype ∘ T ∘ projL0'`).

### `projL1'_add_projL0'_eq` (line 206) — NEW (decomposition lemma)

`↑(projL1' v) + ↑(projL0' v) = v` (subtype-coerced). Proved via
`Submodule.IsCompl.projection_add_projection_eq_self` plus
`Submodule.IsCompl.projection_apply` to convert from the `IsCompl.projection`
form to the `linearProjOfIsCompl`-coerced form.

**Key Mathlib lemma:**
`Submodule.IsCompl.projection_add_projection_eq_self`. (The
`Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` returned by
`leansearch` is **not** in current Mathlib — only `projection_add_projection_eq_self`
exists. Recorded as a search-result false positive for future provers.)

### `lambda_L0_eq_lambda_L0_projL0'` (line 217) — NEW (cross-isotropy
collapse)

For `x : S.L0` and `v : S.E'`:
`λ(↑x, v) = λ(↑x, ↑(projL0' v))`. Proved by rewriting the LHS via
`projL1'_add_projL0'_eq`, distributing over `+`, and using
`S.L0_isotropic_L1'` to kill the `L1'`-projection term.

**Key trick:** had to use `conv_lhs => rw [← h_eq]` (not bare `rw`) to
prevent the rewrite from also touching the `(projL0' S v)` subterm on the
RHS — bare `rw [← h_eq]` rewrites every occurrence of `v`, breaking
the `projL0'` argument.

### `IsSkewB_BST` (line 230) — NEW (skewness lift)

`IsSkewT T → IsSkewB (BST T)`. Direct application of
`lambda_L0_eq_lambda_L0_projL0'` twice (once per side of the `IsSkewB`
identity), reducing the goal to `IsSkewT T (projL0' u) (projL0' v)`.

### `XST_sub_X0Lift_mem_unipotent` (line 244) — RESOLVED (signature
change + new proof body)

**New signature:**
```lean
private lemma XST_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) {T : S.L0' →ₗ[F] S.L0} (hT : S.IsSkewT T) :
    XST S Sₕ T - X0Lift S ∈ UnipotentRadical S
```

(Added `hNondeg` for `Cdual_pairing_eq`; `hT : IsSkewT T` is now
required because the tightened `UnipotentRadical` membership
encodes form-preservation.)

**Proof structure:**

1. Apply `XCB_sub_X0Lift_mem_unipotent` to reduce to proving
   `IsSkewAdjoint S.ambientForm (XCB S (CST Sₕ) (BST T) - X0Lift S)`.
2. Compute `(XCB - X0Lift)(e, v, e') = (Cdual S (CST Sₕ) v + (BST T) e',
   (CST Sₕ) e', 0)` via `XCB_apply, X0Lift_apply, sub_apply` plus
   `ext <;> simp` to handle the V0-component cancellation.
3. Expand `S.ambientForm` via `mk₂_apply`.
4. Apply `Cdual_pairing_eq` twice to convert the `λ(Cdual ·, ·)` atoms
   to `-B0(·, ·)`.
5. Close via `linear_combination`:
   ```
   hSkewB e₁' e₂' + (-S.eps) * hSym
     + (-(S.formV0 ((CST S Sₕ) e₁') v₂)) * hε2
   ```
   where `hSkewB := IsSkewB_BST S hT`,
   `hSym := S.epsSymm v₂ ((CST S Sₕ) e₁')`, and
   `hε2 : S.eps * S.eps = 1` from `S.epsValid`.

**Mathematical insight:** the 6 atoms after Cdual_pairing_eq cancel as

- `λ(Cdual C v₁, e₂') + B0(v₁, C e₂') = 0` (via Cdual_pairing_eq directly)
- `B0(v₁, C e₂')` cancels with the matching term from the other side
- `B0(C e₁', v₂) - ε² · B0(C e₁', v₂) = 0` (via ε-symmetry + ε² = 1)
- `λ(B e₁', e₂') + ε · λ(B e₂', e₁') = 0` (this is `IsSkewB B`,
  derived from `IsSkewT T` + `L0_isotropic_L1'` via `IsSkewB_BST`)

### `XST_mem_O0PlusU` (line 284) — signature update

Added `hNondeg` and `hT : S.IsSkewT T` as new explicit parameters.
Body unchanged except for threading the new args to
`XST_sub_X0Lift_mem_unipotent`.

### `inducedOrbits` (line 299) — signature update

Renamed `_hT` to `hT` (now explicit, not unused). Added new explicit
`(hNondeg : S.formV0.Nondegenerate)` parameter. Body now passes
`hT.1 : S.IsSkewT T` (extracted from `hT : T ∈ S.Tset_circ`) to
`XST_mem_O0PlusU`.

### `main` (line 410) — signature unchanged, body update

Renamed `_hNondeg` to `hNondeg` (now used). Body now passes `hNondeg`
to both `XST_sub_X0Lift_mem_unipotent` and `inducedOrbits`. The first
conjunct's intro variable renamed from `_hT` to `hT` (now used).

## Acceptance criteria check

- `XCB_sub_X0Lift_mem_unipotent` and `XST_sub_X0Lift_mem_unipotent`
  produce proofs of the *tightened* (4-conjunct) `UnipotentRadical`
  membership. ✅
- All call sites of `XST_sub_X0Lift_mem_unipotent` updated. ✅
- `lake env lean InducedOrbitToy/Orbits.lean` has only the line 324
  `sIndependenceAndOrbitCriterion` `sorry` warning — same as start of
  round. ✅
- `lake build` green at end of round. ✅
- No new `axiom` declarations. ✅
- `inducedOrbits`, `main`, `multiplicityNonDeg`, `multiplicityOddCase`,
  `embO0`, `O0`, `IndPG`, `O0PlusU`, `GOrbit`, `MultiplicityTheory`
  signatures preserved (only the `_hNondeg → hNondeg` rename + body
  threading change for `inducedOrbits` and `main`). ✅

## Mathlib lemmas used (new this round)

- `Submodule.IsCompl.projection_add_projection_eq_self` — for the
  `L1' ⊕ L0' = E'` decomposition.
- `Submodule.IsCompl.projection_apply` — to convert
  `IsCompl.projection` to the `linearProjOfIsCompl`-subtype-coerced form.

## Negative search results

- `Submodule.linearProjOfIsCompl_add_linearProjOfIsCompl_eq_self` is
  reported by `leansearch` but **does not exist** in current Mathlib.
  Use `Submodule.IsCompl.projection_add_projection_eq_self` plus
  `projection_apply` instead.
- `LinearMap.add_apply` cannot be applied after `map_add` has already
  distributed `λ` over `+` — the resulting expression has the form
  `(S.lambda x) y + (S.lambda x) z`, not `(?f + ?g) ?x`. Drop
  `LinearMap.add_apply` from such `rw` chains.
- Bare `rw [← projL1'_add_projL0'_eq S v]` rewrites every `v` in the
  goal — use `conv_lhs => rw [...]` or position-targeted rewriting to
  avoid touching `v` inside `projL0' S v`.

## Compilation confirmation

- `lake env lean InducedOrbitToy/Orbits.lean` → only line-324 sorry
  warning (Tier A deferred to Round 7).
- `lake build` → green (8033 jobs).
- `#print axioms inducedOrbits` → `[propext, Classical.choice,
  Quot.sound]`.
- `#print axioms multiplicityNonDeg` → `[propext, Classical.choice,
  Quot.sound]`.
- `#print axioms main` → `[propext, sorryAx, Classical.choice,
  Quot.sound]` (sorryAx from `sIndependenceAndOrbitCriterion`).

## Next steps (Round 7)

`sIndependenceAndOrbitCriterion` (line 324) is the last remaining
sorry-bearing theorem in this file. Round 7's work:

1. Add `(hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)`
   hypotheses to the signature.
2. Forward direction: extract `g ∈ G` from orbit equality; show `g ∈ P`
   via slice stability (uses `XST_sub_X0Lift_mem_unipotent` Round 4
   work + parabolic decomposition Round 6 work); apply
   `pNormalForm_residual_orbit_iso`.
3. Reverse direction: lift the bilinear isometry `h : L0' ≃ L0'` to a
   `P`-element via `pNormalForm_residual_orbit_iso` (Round 6); deduce
   orbit equality.

Both directions depend on `pNormalForm_residual_orbit_iso` being
sorry-free, which itself depends on `pNormalForm_witnesses`,
`residual_levi_extract`, `residual_levi_build` (Round 6 work).
