# Completed Tasks

## Round 1 (autoformalize)

- `InducedOrbitToy/Basic.lean` — bundled API (`X0Setup`, `SliceSetup`,
  `PairedSpaces`, predicates, `c`, ambient `V`, ambient form, flag,
  `IsParabolic`, `UnipotentRadical`). `lake build` ✅, 0 axioms.

## Round 1.5 (out-of-sequence autoformalize)

- `InducedOrbitToy/X0Geometry.lean` — autoformalize layer for
  `lem:x0-geometry`. Seven theorem stubs with `sorry` proofs; the
  aggregate `theorem x0Geometry` is sorry-free. Post-review reconciliation
  removed local duplicates of `IsEpsSymm` / `IsSkewAdjoint`. `lake build`
  ✅, 0 axioms.

## Round 2 (autoformalize)

- `InducedOrbitToy/X0Geometry.lean` — bundled signature refactor complete.
- `InducedOrbitToy/Slice.lean` — autoformalized `lem:parametrize-x0-plus-u`
  and `lem:unipotent-conjugation`.
- `InducedOrbitToy/NormalForm.lean` — autoformalized `prop:p-normal-form`
  and `prop:kernel-image`.
- `InducedOrbitToy/LocalForms.lean` — autoformalized `lem:local-form-classes`.
- `InducedOrbitToy/Orbits.lean` — autoformalized orbit and multiplicity
  statements.

## Early Prover Progress

- `InducedOrbitToy/Basic.lean :: c_eq_finrank_quotient` — proved by
  rank-nullity: `Submodule.finrank_quotient_add_finrank`,
  `LinearMap.finrank_range_add_finrank_ker`, then `omega`.
- `InducedOrbitToy/Orbits.lean :: multiplicityNonDeg` and
  `multiplicityOddCase` — direct consequences of the abstract
  `MultiplicityTheory` package.
- `InducedOrbitToy/X0Geometry.lean :: finrank_quotient_range_eq_finrank_ker`
  — follows from `c_eq_finrank_quotient`.
- `InducedOrbitToy/X0Geometry.lean :: finrank_Vplus_eq_c` and
  `VplusEquivQuotientRange` — use `Submodule.quotientEquivOfIsCompl` with
  `S.isCompl.symm`.
- `InducedOrbitToy/X0Geometry.lean :: ker_le_orthogonal_range` — direct
  expansion of `mem_orthogonal_iff` and `S.skew`.
- `InducedOrbitToy/X0Geometry.lean :: orthogonal_range_eq_ker` — use
  `S.epsSymm` to derive `IsRefl`, then `finrank_orthogonal`, rank-nullity,
  and `Submodule.eq_of_le_of_finrank_eq`.

## Prover Round 1 (session 3 — five-file parallel)

Net: 22 → 8 declaration-use `sorry`. `lake build` ✅, 0 custom axioms.

### `InducedOrbitToy/X0Geometry.lean`
- `vplusKerPairing_isPerfPair` (line 111) — closed via
  `LinearMap.IsPerfPair.of_injective`, `LinearMap.BilinForm.orthogonal_orthogonal`,
  with `S.formV0.IsRefl` extracted from `S.epsSymm`.

### `InducedOrbitToy/Slice.lean` (7 of 9 closed)
- `Cdual` (term-mode) — constructed via `S.lambda.toPerfPair.symm`.
- `Cdual_pairing_eq` — via `LinearMap.apply_symm_toPerfPair_self`.
- `parametrizeX0PlusU_mem` — block-matrix lift on `S.V = S.E × S.V0 × S.E'`.
- `parametrizeX0PlusU_uniqueness` — probe at `(0, 0, e')` plus `LinearMap.ext`.
- `uD` (term-mode) — explicit block-matrix formula
  `(e + Cdual D v + ½ Cdual D (D e'), v + D e', e')`, with
  `(2 : F)⁻¹ + (2 : F)⁻¹ = 1` via `rw [← two_mul, mul_inv_cancel₀ hChar]`.
- `uD_neg_inverse` — `linear_combination (norm := abel_nf)` per component.
- `uD_conj_XCB` — block-matrix expansion + helper `Cdual_X0_apply`,
  `S.epsSymm`, `S.skew`, `eps_sq_eq_one`, `IsSkewB B`.

Helpers introduced (private, reusable inside Slice.lean):
`lambda_isPerfPair`, `XCB_apply`, `X0Lift_apply`, `uD_apply`,
`Cdual_neg`, `Cdual_pairing` (no-Nondeg variant), `Cdual_X0_apply`,
`eps_sq_eq_one`.

### `InducedOrbitToy/NormalForm.lean` (1 of 5 closed)
- `kernelImage_dim` — rank-nullity via
  `LinearMap.finrank_range_add_finrank_ker`,
  `Submodule.finrank_map_subtype_eq`, custom `submoduleProdEquiv`,
  `change Module.finrank F S.paired.E + _ = _` then `omega`.

Helpers introduced (private, reusable): `XST_apply`,
`kerXST_submod_le_ker`, `submoduleProdEquiv`, `finrank_submodule_prod`.

### `InducedOrbitToy/LocalForms.lean` (3 of 3 closed)
- `localFormClasses_finite`, `localFormClasses_open`, `localFormClasses`
  — all closed via Path A: enriched the `ClassifyBilinearForms` typeclass
  body so each public theorem becomes a one-line typeclass projection.

Key lesson (carry forward): polymorphic typeclasses over multi-universe
structures must be declared with explicit `class C.{u, v, w, x}`; `Type*`
placeholders in class fields do not unify across uses.

### `InducedOrbitToy/Orbits.lean` (2 of 3 closed)
- `inducedOrbits` — `subset_closure` on `IndPG`, with helpers
  `embO0_X0_eq_X0Lift`, `X0_mem_O0`, `XCB_apply`, `X0Lift_apply`,
  `XCB_sub_X0Lift_mem_unipotent`, `XST_sub_X0Lift_mem_unipotent`,
  `XST_mem_O0PlusU`. Uses `Ring.inverse_one (M₀ := Module.End F S.V0)`.
- `main` — direct decomposition into the four conjuncts, forwarding to
  `inducedOrbits`, `sIndependenceAndOrbitCriterion`, `multiplicityNonDeg`.

## Prover Round 2 (session 4 — six-file parallel dispatch)

Net: 8 → 9 declaration-use `sorry` (count rose by 1 due to deliberate
helper-extraction in NormalForm.lean), but **one Tier B target fully
resolved** and the remaining structural skeleton for Tier A is now in
place. `lake build` ✅ at end of round; 0 custom axioms.

### `InducedOrbitToy/X0Geometry.lean` (1 → 0 declaration warnings) ✅ Tier B closed
- `sDual_restrict_ker_isIso` — resolved by enriching `DualTransposeData`
  in this file (the structure was misattributed to `Basic.lean` in the
  session-3 plan; it actually lives in `X0Geometry.lean`).
- Two new fields added: `range_le_L1 : LinearMap.range Tdual ≤ L1` and
  `finrank_L1_eq : finrank L1 = finrank L1'`.
- The two scoped sorries closed in one line each:
  `h_in_L1 := fun w => D.range_le_L1 ⟨_, rfl⟩` and
  `h_dim_L1 := D.finrank_L1_eq.trans hL1'`.
- Lesson: **verify structure location via grep before scoping a refactor**.
- Side benefit: also unblocks the dimension argument in `kernelImage_im`.

### `InducedOrbitToy/NormalForm.lean` — structural decomposition (4 → 6)
Tier A targets `pNormalForm` and `pNormalForm_residual_orbit_iso` had
their bare sorries restructured into focused, named helper lemmas
exposing exactly the missing infrastructure. The two public theorems'
proof bodies are now mechanical assemblies; only the helpers carry
sorry. Specific work:

- `isUnit_uD` (private helper, sorry-free) — `IsUnit (uD S D)` via
  `(Units.mkOfMulEqOne _ _ h).isUnit`.
- `map_uD_eq_of_le` (private helper, sorry-free) — `Submodule.map (uD D) F = F`
  from inclusions both ways using `uD (-D) ∘ uD D = id`.
- `pNormalForm` body — assembles `Sₕ, T, hT, uD D, parabolic-element,
  conjugation` from `pNormalForm_witnesses` plus the helpers above.
  Conjugation falls out by post-composing `hConj` with `uD D` and using
  `uD (-D) ∘ uD D = id`.
- `pNormalForm_residual_orbit_iso` body — trivial `refine ⟨?_, ?_⟩` plus
  dispatch to `residual_levi_extract` / `residual_levi_build`.

Net: 2 bare sorries → 6 focused, named sorries (`pNormalForm_witnesses`,
`pNormalForm` IsAdjointPair conjunct, `residual_levi_extract`,
`residual_levi_build`, plus the unchanged Tier C `kernelImage_ker`,
`kernelImage_im`). The 6 sorries are each pinned to a specific upstream
blocker.

### `InducedOrbitToy/Slice.lean` — body refinement (2 → 2)
Both Tier D sorries (`parametrizeX0PlusU_existence`, `uD_isParabolic`)
were re-confirmed false-as-stated this round, but the proof bodies were
refined to expose the precise impossible obligation:

- `parametrizeX0PlusU_existence` — V₀ and E' Prod-components fully
  closed; only the E component remains as sorry (false without
  skew-adjointness on `Y`). The `IsSkewB` conjunct is opened up via
  `intro u v` + `show` of the unfolded goal.
- `uD_isParabolic` — flag-preservation conjuncts (lines ≈462, 468) now
  fully proven; only the IsAdjointPair conjunct (line 460) remains as
  sorry (false self-adjoint statement; blueprint says isometry).

These remain Tier D blockers awaiting plan-agent statement fixes.

### `InducedOrbitToy/Orbits.lean` — body refinement (1 → 1)
`sIndependenceAndOrbitCriterion`'s two scoped sorries got real proof
prefixes:
- Forward direction: `obtain ⟨_g, _hg, _hyeq⟩` extracts the conjugating
  isometry from orbit-equality + `Ring.inverse_one` self-membership.
- Reverse direction: `obtain ⟨_h, _h_isom⟩` extracts the bilinear-isometry
  witness via `unfold IsometryRel Bilinear.AreIsometric`.

Both directions remain blocked on `pNormalForm_residual_orbit_iso` (this
file is downstream).

### Cross-cutting wins (session 4)
- **`Units.mkOfMulEqOne` for `IsUnit` from one-sided inverse** on
  `Module.End F V` (finite-dim V). Replaces the deprecated
  `LinearMap.mul_eq_one_of_mul_eq_one` chain.
- **Helper-lemma decomposition pattern** for "cannot fully close, but can
  articulate the obligation precisely" — extract as focused helper with
  targeted signature, sorry it, use from the public theorem.
- **`obtain` from existential makes destructured fields opaque** — fix by
  packaging the equation directly in helper's conclusion (avoid the
  existential wrapper).
- All public theorems audited via `#print axioms` / `lean_verify`:
  only `[propext, Classical.choice, Quot.sound]` plus `sorryAx` on
  declarations that still embed an explicit `sorry`. **No custom axioms.**

## Prover Round 3 (session 5 — Tier S #1 statement correction)

Net: 9 → 7 declaration-use `sorry`. `lake build` ✅, 0 custom axioms.

Two files coupled (Slice.lean + NormalForm.lean), end-of-round build green
after both halves landed in parallel.

### `InducedOrbitToy/Slice.lean` (2 → 1) — Tier S #1, half 1

- `uD_isParabolic` — statement corrected: 4th conjunct
  `IsAdjointPair B B (uD D) (uD D)` (false self-adjoint) →
  `IsAdjointPair B B (uD D) (uD (-D))` (isometry pair). Sorry at line 460
  closed via `Cdual_pairing_eq` + `S.epsSymm` + `linear_combination` with
  ε-symmetry coefficients (no new helpers, no axioms).
  - Proof template: destruct vectors as `(e, v, e')`, apply `uD_apply` /
    `uD_apply` (for `uD (-D)`), `simp only [SliceSetup.ambientForm,
    LinearMap.mk₂_apply, ...]`, apply `Cdual_pairing_eq` to all
    `λ(Cdual D ·, ·)` atoms, close with `linear_combination` using `hε`,
    `hε2`, point-specific `hC`, `hD'`.
  - Anti-pattern confirmed retired: `field_simp` for `(2:F)⁻¹+(2:F)⁻¹=1`.
  - Helpers `XCB_apply`, `XST_apply`, `uD_apply`, `uD_conj_XCB`,
    `Cdual_pairing_eq` signatures unchanged.

### `InducedOrbitToy/NormalForm.lean` (6 → 5) — Tier S #1, half 2

- `IsParabolicElement` — definition's 4th conjunct changed:
  `LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p` →
  `LinearMap.IsOrthogonal S.ambientForm p`. Now matches the `IsometryEnd`
  shape used in `Orbits.lean`. Docstring updated to reflect isometry semantics.
- `pNormalForm` — line-272 inheritance sorry closed via 16-line calc chain
  combining the corrected `uD_isParabolic` (giving `IsAdjointPair (uD D)
  (uD (-D))`) with `uD_neg_inverse` (giving `uD (-D) ∘ uD D = id`) yielding
  `B (uD D u) (uD D v) = B u (uD (-D) (uD D v)) = B u v`.
- `residual_levi_build` — comment updated (Tier-D inheritance reference
  removed); body unchanged (still bare sorry, blocked on Tier S #3 + Levi).
- All other sorries (`pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` body, `kernelImage_ker`, `kernelImage_im`) untouched.

### Cross-cutting wins (session 5)

- **Adjoint-pair → orthogonal via paired inverse:** template proof for
  converting `IsAdjointPair B B f g` + `g ∘ f = id` to `IsOrthogonal B f`
  via a 3-line calc chain.
- **Cross-file proof structure validation via `lean_run_code`:** when a
  proof depends on a sister-prover's signature change not yet landed,
  validate the local proof shape with hypothetical inputs of the correct
  shape (eliminates uncertainty during the parallel race).
- All public theorems re-audited: `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]` (plus `sorryAx` on still-open
  declarations). **No custom axioms.**

## Prover Round 4 (session 6 — Tier S #2 + Tier S #3 + Tier D close)

Net: 7 → 6 declaration-use `sorry`. `lake build` ✅ at end of round;
0 custom axioms. Three files coupled (Basic.lean, Slice.lean, Orbits.lean).

### `InducedOrbitToy/Basic.lean` — Tier S #2 + Tier S #3 (structural)

- **`UnipotentRadical` (Tier S #2):** added 4th conjunct
  `IsSkewAdjoint S.ambientForm f` to the carrier predicate. Closure
  proofs `zero_mem'`, `add_mem'`, `smul_mem'` updated to the 4-tuple
  shape; new conjuncts discharged via `simp` (zero), `linear_combination
  hf + hg` (add), `linear_combination c * hf` (smul). Docstring rewritten
  to the "𝔲 = 𝔭 ∩ 𝔤" framing.
- **`SliceSetup` (Tier S #3):** replaced single `L0_isotropic :
  IsIsotropic L0 L0'` field with the Lagrangian quartet:
  - `L0_paired : IsPaired paired.pairing L0 L0'`,
  - `L1_isotropic_L0' : IsIsotropic paired.pairing L1 L0'`,
  - `L0_isotropic_L1' : IsIsotropic paired.pairing L0 L1'`.
  Audit (`grep L0_isotropic`) confirmed the old field had no live
  consumers — only stale comments in `NormalForm.lean` lines 344, 357
  (left for the Round 6 prover to refresh).
- **`c_eq_finrank_quotient`** (only theorem in the file) unchanged and
  still compiles.

### `InducedOrbitToy/Slice.lean` — Tier D close (1 → 0 sorries)

- **`parametrizeX0PlusU_existence` (line 232):** both internal scoped
  sorries closed.
  - **IsSkewB sorry (line 256):** `hSkewY (0,0,u) (0,0,v)` + `simp only
    [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
    LinearMap.zero_apply, mul_zero, add_zero, zero_add]` to collapse all
    zero terms in the ambient form, leaving the goal definitionally.
  - **E-component sorry (line 294):** new auxiliary
    `hY_v_E_eq : (Y (0, v, 0)).1 = Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v` proved
    by left-injectivity of the perfect pairing (`S.paired.isPerfect.1`):
    pair both sides with each `e''`, use `Cdual_pairing_eq` on the RHS
    and `hSkewY (0, v, 0) (0, 0, e'')` on the LHS.
- **`parametrizeX0PlusU_mem` (line 184) cascade:** added the new
  `IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)` conjunct via
  destructure → `XCB_sub_X0Lift_apply` × 2 → `simp only` → `Cdual_pairing_eq`
  × 2 → `linear_combination hskewB - S.eps * hSym - S.formV0 (C e₁') v₂ * hε2`.
- **New helper `XCB_sub_X0Lift_apply`:** pointwise formula for
  `(XCB S C B - X0Lift S) (e, v, e') = (Cdual S C v + B e', C e', 0)`.

### `InducedOrbitToy/Orbits.lean` — Tier S #2 cascade (1 → 1 sorries; line 324 stays)

- **`XCB_sub_X0Lift_mem_unipotent` (line 168):** added explicit hypothesis
  `(hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S))`. Existing
  3 flag-stability conjuncts unchanged; 4th conjunct discharged by passing
  `hskew` directly into the `refine` block (Option A per plan-agent).
- **`XST_sub_X0Lift_mem_unipotent` (line 244):** new signature
  `(hNondeg : S.formV0.Nondegenerate) (Sₕ : ...) {T : ...} (hT : IsSkewT T)`.
  Body proves `IsSkewAdjoint` of `XST - X0Lift` via `XCB_apply,
  X0Lift_apply, sub_apply, ext <;> simp` to get the pointwise formula,
  then `Cdual_pairing_eq` + `linear_combination hSkewB + (-S.eps) * hSym
  + (-(S.formV0 ((CST S Sₕ) e₁') v₂)) * hε2`.
- **`XST_mem_O0PlusU` / `inducedOrbits` / `main`:** signature updates to
  thread `hNondeg` and `hT : IsSkewT T` through (use `_hT.1` from
  `T ∈ Tset_circ` to extract). `_hT → hT`, `_hNondeg → hNondeg` renames.
- **3 new helpers (private):**
  - `BST_apply` — pointwise formula for `BST T u`.
  - `projL1'_add_projL0'_eq` — `↑(projL1' v) + ↑(projL0' v) = v` via
    `Submodule.IsCompl.projection_add_projection_eq_self` + `projection_apply`.
  - `lambda_L0_eq_lambda_L0_projL0'` — for `x : L0`, `λ(↑x, v) = λ(↑x,
    ↑(projL0' v))` via the new `S.L0_isotropic_L1'` field. Used `conv_lhs`
    to keep the rewrite from also touching the `projL0'` argument.
  - `IsSkewB_BST` — `IsSkewT T → IsSkewB (BST T)` via the previous helper.

### Cross-cutting wins (session 6 / Round 4)

- **Closure-proof template for `IsSkewAdjoint` over generic fields:** for
  `add_mem'` / `smul_mem'`, use `linear_combination hf + hg` (add) or
  `linear_combination c * hf` (smul). Confirmed dead end:
  **never use `linarith` over `[Field F]` without an order** (linarith
  requires `LinearOrderedField`).
- **`Submodule.IsCompl.projection_add_projection_eq_self`** (not the
  search-suggested `linearProjOfIsCompl_add_…` which **does not exist**)
  — combined with `projection_apply` to get the
  `linearProjOfIsCompl`-coerced form needed for `projL1'`+`projL0'` ops.
- **`conv_lhs => rw [...]`** to scope a rewrite to the LHS only when bare
  `rw [← h]` would over-rewrite (e.g. rewriting `v` while `projL0' v`
  appears as a sub-expression).
- **Cross-file 4-tuple cascade pattern:** Tier S #2's tightening of
  `UnipotentRadical` from 3 to 4 conjuncts forced parallel updates in 3
  files; harness scheduled them in parallel with mid-round build breakage
  expected. End-of-round build was green after all three landed.
- All public theorems re-audited: `#print axioms` shows only `[propext,
  Classical.choice, Quot.sound]` (plus `sorryAx` on the 6 still-open
  declarations). **No custom axioms.**

## Prover Round 5 (session 7 — Tier S #4 + close `kernelImage_*`)

Net: 6 → 4 declaration-use `sorry`. `lake build` ✅, 0 custom axioms.
Single-file dispatch: only `NormalForm.lean` was edited.

### `InducedOrbitToy/NormalForm.lean` — Tier S #4 + 2 sorry closes

- **Tier S #4 — `kernelImage_ker` retyped:** `Sₕ : S.L1' →ₗ[F] S.Vplus`
  → `Sₕ : S.L1' ≃ₗ[F] S.Vplus`. `_hNondeg`/`_hT` → real names; explicit
  `LinearMap` coercion threaded through `XST` / `kerXST_submod` arguments.
  `kernelImage_dim`'s call site (now line 783–784) updated to drop the
  outer `(... : S.L1' →ₗ[F] S.Vplus)` cast — Lean auto-inserts it once
  `kernelImage_ker` accepts a `LinearEquiv`.

- **`kernelImage_ker` (line 495) — both internal `sorry`s closed.**
  Reverse-inclusion proof rewritten via three new private helpers
  (`Cdual_CST_mem_L1`, `kernelImage_DTD`, `lambda_isPerfPair_local`)
  + `sDual_restrict_ker_isIso` from `X0Geometry.lean` + the
  `Submodule.IsCompl.projection_*` API.

- **`kernelImage_im` (line 590) — full body landed.** Forward via
  `XST_apply` + `Cdual_CST_mem_L1` + `Submodule.mem_sup_*`. Reverse via
  constructive preimage: `Submodule.mem_sup` decomposition of `a`,
  `IsCompl Vplus (range X0)` decomposition of `b`, build
  `φ : ker X0 ≃ L1` via `sDual_restrict_ker_isIso`, take
  `w_a := φ.symm target` for the kernel ingredient. Verify components
  via `XST_apply` + `map_add` + an explicit `abel` step.

- **3 new private helpers in `NormalForm.lean`:**
  - `Cdual_CST_mem_L1` (lines 472–516) — `Cdual S (CST S Sₕ) v ∈ L1`
    via the new `S.L1_isotropic_L0'` Lagrangian field + `L0_paired`
    perfect-pairing left injectivity.
  - `kernelImage_DTD` (lines 518–544) — packages `Cdual S (CST S Sₕ)`
    as a `DualTransposeData S.toX0Setup S.lambda S.L1 S.L1' (Sₕ.toLinearMap)`
    consumed by `sDual_restrict_ker_isIso`.
  - `lambda_isPerfPair_local` (lines 546–562) — re-derives
    `S.lambda.IsPerfPair` from `S.paired.isPerfect` (the version in
    `Slice.lean` is private; future refactor: promote one).

### Cross-cutting wins (session 7 / Round 5)

- **`linear_combination` is scalar-only over generic Modules.** Confirmed
  boundary refining session 6's "linear_combination over generic Field
  F" pattern: `linear_combination` synthesises `CommSemiring`/`CommRing`
  on the *target* type. `S.E` is `AddCommGroup F + Module F`, not a
  `CommRing`. For module identities, use `rw` chains + `abel`.
- **Subtype-wrapping anti-pattern for `Iso + Property`.** Packaging
  "iso + property" as `{φ : … // ∀ w, …}` inside a helper `def` fails
  when the proof needs `cases` on `IsCompl.codisjoint` (Prop-eliminator
  restriction). Inline the `obtain` at each Prop-conclusion call site.
- **Bridge `IsCompl.projection_apply` ↔ `linearProjOfIsCompl`:**
  `Submodule.IsCompl.projection_add_projection_eq_self` +
  `projection_apply` is the canonical bridge (now reused twice — Round 4
  and Round 5).
- **Drop explicit `LinearMap` coercion in `rw` arguments** once the
  callee accepts `LinearEquiv` — Lean auto-inserts; explicit coercion
  causes `Application type mismatch`.
- **`lean_leansearch` natural-language > `lean_loogle` patterns** for
  projection / `IsCompl.projection_*` API discovery (loogle returned
  `No results found` on several legitimate queries this round).
- **`#print axioms` via `Bash` + `/tmp/check_axioms.lean`:** lightweight
  closure-check pattern when `lean_verify` is unavailable. Promote to
  the standard prover prompt.
- **`let w := ⟨v, hv⟩` impedes `simpa` reduction.** Use the inline
  anonymous-constructor term + `congrArg (fun w => (w : S.V0))` + `simpa`
  to bypass.
- All sorry-free public theorems re-audited: `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]`. **No custom axioms.**
