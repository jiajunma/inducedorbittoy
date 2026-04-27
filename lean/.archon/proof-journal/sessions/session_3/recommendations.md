# Recommendations for Session 4

## Snapshot

- **Build state:** `lake build` is green; 8 declaration-use `sorry` warnings remain.
- **Custom axioms:** 0. All public theorems depend on `[propext, Classical.choice, Quot.sound]` only.
- **Net session-3 progress:** 22 → 8 declaration-use sorries (≈63% reduction).

## Priority queue for next plan iteration

### Tier A — Highest priority (provable now, no upstream changes needed)

These targets are still open *not* because of upstream issues but because they
involve long but standard proofs that can be discharged in the next prover round:

1. **`InducedOrbitToy/NormalForm.lean :: pNormalForm`** (line 167)
   - Strategy: from `_hRank : rank Cbar = c`, construct `Sₕ : L1' →ₗ Vplus` as
     a `LinearMap.linearEquivOfInjective`-style map (use the rank hypothesis
     to confirm injectivity + dim-match). Then call
     `Slice.uD_conj_XCB` (already proven this session) to put `XCB S C B`
     into `XST S Sₕ T` form. Extract `T` from the residual data.
   - Estimated effort: 1 prover round, 30–50 lines.

2. **`InducedOrbitToy/NormalForm.lean :: pNormalForm_residual_orbit_iso`** (line 199)
   - Strategy:
     - **(→)** Given parabolic `p` with `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`,
       extract action on the `L_0 ⊕ L_0'` block to get a Levi factor;
       its action on `BT T₁` is a bilinear isometry to `BT T₂`.
     - **(←)** Given `q : BT T₁ ≃ᵇ BT T₂`, lift `q` to a parabolic `p`
       via the block-matrix structure on `V`.
   - Both directions reuse `Slice.uD_conj_XCB`.
   - Estimated effort: 1 prover round, 80–120 lines.

3. **`InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion`** (line 242, 2 internal sorries)
   - **Unblocked** by `pNormalForm_residual_orbit_iso` above. Both iff
     directions reduce to that lemma plus a unipotent-radical absorption.
   - Estimated effort: 30 lines once `pNormalForm_residual_orbit_iso` lands.

**Plan agent suggestion:** assign Tier A items 1 and 2 to two parallel
provers, then a follow-up round picks up item 3.

### Tier B — Provable after a small upstream refactor

4. **`InducedOrbitToy/X0Geometry.lean :: sDual_restrict_ker_isIso`** (line 206, 2 scoped sorries)
   - Blocker: `Basic.lean :: DualTransposeData` does not expose
     (a) the `L1` subspace such that `range(Tdual) ⊆ L1`, and
     (b) the dimension equation `finrank L1 = finrank ker S.X0`.
   - Refactor: enrich `DualTransposeData` with two new fields. Roughly:
     ```lean
     structure DualTransposeData ... where
       Tdual : Vplus →ₗ[F] V0
       pairing_eq : ∀ ..., lambda (Tdual w) v = -formV0 w v
       L1_le : LinearMap.range Tdual ≤ L1     -- NEW
       finrank_L1_eq : Module.finrank F L1 = Module.finrank F (ker X0)  -- NEW
     ```
   - Estimated effort: 5 lines in `Basic.lean` + 2-line proof discharge in
     `X0Geometry.lean` (the rest of the proof skeleton is already in place).

### Tier C — Blocked on upstream data refactor (Plan: do NOT reassign yet)

5. **`InducedOrbitToy/NormalForm.lean :: kernelImage_ker`** (line 302)
6. **`InducedOrbitToy/NormalForm.lean :: kernelImage_im`** (line 397)
   - Blocker: both formulas require `Sₕ` to be a bijection (LinearEquiv) onto
     `Vplus`, **and** a Lagrangian condition `λ(L1, L0') = 0`. Neither is
     part of the current `SliceSetup` data.
   - Refactor: revisit `Slice.lean :: SliceSetup` to add:
     ```lean
     structure SliceSetup ... where
       ...
       lagrangian : ∀ x ∈ L1, ∀ y ∈ L0', lambda x y = 0  -- NEW
     ```
     and tighten `kernelImage_ker` / `kernelImage_im` to take `Sₕ` as
     `LinearEquiv` not `LinearMap` (the underlying API at the call sites
     already uses `LinearEquiv`, so this is mostly cosmetic).

### Tier D — Permanently blocked (statement-level autoformalization bugs)

7. **`InducedOrbitToy/Slice.lean :: parametrizeX0PlusU_existence`** (line 232)
   - The autoformalized statement is **mathematically false**: `UnipotentRadical`
     in `Basic.lean` is the loose flag-preserving Lie algebra without
     skew-adjointness w.r.t. `S.ambientForm`. An arbitrary flag-preserving
     `Y` decomposes as a triple of free linear maps with no skew constraint.
   - Fix: tighten `Basic.lean :: UnipotentRadical` to be the Lie subalgebra
     that *also* preserves `S.ambientForm`. Then this becomes provable.

8. **`InducedOrbitToy/Slice.lean :: uD_isParabolic`** (line 391)
   - Statement bug: the `LinearMap.IsAdjointPair B B (uD D) (uD D)` conjunct
     says `uD` is *self-adjoint* w.r.t. the ambient form. The blueprint says
     `uD` is an *isometry* (i.e., `(uD D, uD (-D))` is an adjoint pair).
   - Fix: change the autoformalized statement to
     `LinearMap.IsAdjointPair B B (uD D) (uD (-D))`. Then provable from
     `uD_neg_inverse` + a one-line block-matrix calculation.

**Plan agent: do NOT assign Tier D until the above autoformalization fixes
land in `Basic.lean`/`Slice.lean`.**

## Reusable proof patterns discovered

1. **Polymorphic typeclasses over multi-universe structures:** declare with
   explicit universe parameters (`class C.{u, v, w, x}`) so that internal
   fields' uses of the structure type unify cleanly. `Type*` placeholders
   inside class fields *do not* unify across uses.

2. **`change` for omega across abbrevs:** `omega`/`linarith` cannot see
   through `abbrev`s like `S.E := S.paired.E`. Insert a manual `change`
   at the abbrev boundary before invoking `omega`.

3. **Block-matrix pointwise lemmas:** for endomorphisms on `V = E × V₀ × E'`
   defined via `LinearMap.fst/snd/inl/inr` compositions, the pattern
   `XCB_apply ... := rfl` fails (too many `let`-bindings). Instead, write
   the fully unfolded RHS in a `show` clause before the `rfl`:
   ```lean
   show ((LinearMap.inl ...) ∘ₗ ... + ...) (e, v, e') = (..., ..., 0); rfl
   ```

4. **Dual transpose via `LinearMap.toPerfPair`:** the right Mathlib
   construction for "transpose of `C : E' →ₗ V0` along the perfect pairing
   `λ : E ↔ E'`" is
   ```lean
   noncomputable def Cdual S C : V0 →ₗ E :=
     S.lambda.toPerfPair.symm.toLinearMap.comp (-(C.dualMap.comp S.formV0))
   ```
   Pairing equation `λ (Cdual C v) e' = -formV0 v (C e')` follows from
   `LinearMap.apply_symm_toPerfPair_self`.

5. **`(2 : F)⁻¹ + (2 : F)⁻¹ = 1`:** `field_simp` leaves a residual
   `1 + 1 = 2` that must be closed manually. Use
   ```lean
   have hhalf : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by
     rw [← two_mul, mul_inv_cancel₀ hChar]
   ```

6. **`Submodule.prod p q ≃ₗ ↥p × ↥q`:** not in Mathlib. Helper written this
   session (in `NormalForm.lean :: submoduleProdEquiv`) is reusable; worth
   upstreaming.

7. **`Ring.inverse` for endomorphism orbit predicates:** `Ring.inverse g`
   on `Module.End F V` returns the genuine inverse for `IsUnit g` and `0`
   otherwise, dodging the need for a division-ring structure on `End`.

## Suggested round structure for next session

- **Round 1 (parallel):** assign Tier A items 1 and 2 (`pNormalForm` and
  `pNormalForm_residual_orbit_iso`) to two provers. Both files already
  compile, so risk of breakage is low.
- **Round 2 (cleanup):** Tier A item 3 (`sIndependenceAndOrbitCriterion`),
  plus Tier B item 4 if `Basic.lean :: DualTransposeData` is also
  refactored as part of the same round.
- **Defer:** Tier C and Tier D items until the upstream `Basic.lean` /
  `Slice.lean` data fixes are scoped and assigned.
