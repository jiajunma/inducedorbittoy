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

## Prover Round 6 (session 8 — Levi machinery additive in `Slice.lean`)

Net: 4 → 5 declaration-use `sorry` (additive: a single new sorry on the
deferred `parabolic_decompose`). NormalForm/Orbits sorry counts and
locations unchanged (3 + 1, lines 195/319/348/324). `lake build` ✅;
0 custom axioms.

Single-file dispatch — only `Slice.lean` was edited. ~414 lines
appended (lines 679–1093) after the existing `uD_conj_XCB`. Lines 1–678
are byte-for-byte unchanged.

### `InducedOrbitToy/Slice.lean` — Levi-action machinery

14 new declarations, 13 sorry-free:

#### Section 6.1 — Dual transpose on `E`
- `lambdaDualE` — `S.E →ₗ[F] S.E` for `g : S.E' →ₗ[F] S.E'`, defined
  via `S.lambda.toPerfPair.symm ∘ g.dualMap ∘ S.lambda` (mirrors the
  `Cdual` construction at line 71).
- `lambdaDualE_pairing_eq` — defining identity `λ(g^∨ e, e') = λ(e, g e')`
  via `apply_symm_toPerfPair_self` + `dualMap_apply`.
- `lambdaDualE_id`, `lambdaDualE_comp` — functoriality, proved by
  pairing both sides via `S.paired.isPerfect.1`.
- Private helpers: `lambdaDualE_symm_comp`, `lambdaDualE_comp_symm` —
  iso composition collapses to identity.

#### Section 6.2 — Levi block embeddings
- `leviGL_E S d : Module.End F S.V` for `d : S.E' ≃ₗ[F] S.E'`, acting
  as `((d⁻¹)^∨, id, d)` on `E × V0 × E'`.
- `leviGL_V0 S g : Module.End F S.V` for `g : S.V0 ≃ₗ[F] S.V0`, acting
  as `(id, g, id)`. **Definition does not depend on isometry hypothesis.**
- `leviGL_E_apply`, `leviGL_V0_apply` — pointwise formulas via
  `unfold` + `simp`.

#### Section 6.3 — Inverses
- `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse` — composition with
  `_symm` is `id`. **Key insight:** `d.symm.symm = d` is `rfl` for
  `LinearEquiv`, halving the inverse-proof work.

#### Section 6.4 — Parabolicity
- `leviGL_E_isParabolic`, `leviGL_V0_isParabolic` — 4-conjunct
  predicate (IsUnit ∧ flagE preserved ∧ flagEV0 preserved ∧
  IsOrthogonal). The Levi `V0` block needs the `formV0`-isometry
  hypothesis for the IsOrthogonal conjunct only.

#### Section 6.5 — Conjugation transformation of `XCB`
- `leviGL_E_conj_XCB` —
  `leviGL_E d ∘ XCB(C, B) = XCB(C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm) ∘ leviGL_E d`.
- `leviGL_V0_conj_XCB` — analogous, parameterised by hypotheses
  `(g ∘ X0 = X0 ∘ g)` and a g-pairwise condition `hgC` on `C`.
- Private helper `lambdaDualE_Cdual` — bridges the dual transpose and
  Cdual: `lambdaDualE g (Cdual C v) = Cdual (C ∘ g) v`.

#### Section 6.6 — Levi/unipotent decomposition (DEFERRED)
- `parabolic_decompose` (line 1078) — **NEW SORRY**. Carries an
  explicit `/-** Gap: ... -/` comment block (24 lines) outlining the
  three substantive sub-constructions needed: (a) `g₀` extraction via
  quotient `flagEV0 / flagE ≃ V0`; (b) `(d⁻¹)^∨` extraction from
  `Submodule.map p flagE = flagE`; (c) residual `D` via
  `parametrizeX0PlusU_uniqueness`.
  - Deferred to Round 8 per PROGRESS.md stop conditions ("do NOT spend
    more than ~30% of round budget on `parabolic_decompose`").

### Cross-cutting wins (session 8 / Round 6)

- **`d.symm.symm = d` is `rfl` for `LinearEquiv`.** Allows
  `leviGL_E_symm_inverse S d.symm` to directly give the
  other-direction inverse. Reused for `IsUnit` witnesses via
  `Units.mkOfMulEqOne`.
- **LinearEquiv vs LinearMap FunLike coercion mismatch in `rw`
  patterns.** When stating an isometry-style hypothesis used in `rw`,
  match the `LinearMap`-coerced form that appears in the goal *after*
  `LinearMap.comp_apply` rewrites. Asymmetric statements
  `(g : V →ₗ V) (C e'') = C e''` win where symmetric ones lose.
- **`show` to convert composed-form goals to nested-application form**
  before `rw`-ing perfect-pairing equations. Pattern:
  `show ... = ... f (g e)` to make `rw` targets visible.
- **Block-matrix inverse via componentwise identity proofs.** The
  `Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩`
  pattern reusable for any `Module.End F (E × V0 × E')` proofs.
- **`leviGL_V0` definition does NOT bundle the isometry hypothesis.**
  The hypothesis is passed separately at consumer sites
  (`leviGL_V0_isParabolic`, `leviGL_V0_conj_XCB`). This avoids the
  Round-5 subtype-wrapping anti-pattern.

### Audit (session 8)

`#print axioms` on each of `lambdaDualE`, `lambdaDualE_pairing_eq`,
`lambdaDualE_id`, `lambdaDualE_comp`, `leviGL_E`, `leviGL_V0`,
`leviGL_E_apply`, `leviGL_V0_apply`, `leviGL_E_symm_inverse`,
`leviGL_V0_symm_inverse`, `leviGL_E_isParabolic`,
`leviGL_V0_isParabolic`, `leviGL_E_conj_XCB`, `leviGL_V0_conj_XCB`
returns `[propext, Classical.choice, Quot.sound]`. **No custom
axioms.**

## Prover Round 7 (session 9 — NormalForm.lean closure cascade)

Net: 5 → 3 declaration-use `sorry` (−2). `lake build` ✅ at end of
round; 0 custom axioms.  Single-file dispatch — only
`NormalForm.lean` was edited.

### `InducedOrbitToy/NormalForm.lean` — Tier S #5 + 2 sorries closed

- **Tier S #5 — `pNormalForm_witnesses` signature restructure
  (landed).** Replaced the mathematically-false
  `uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T` with the corrected
  Levi-factor form
  ```lean
  ∃ (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
    (d : S.E' ≃ₗ[F] S.E') (T : S.L0' →ₗ[F] S.L0),
    IsSkewT S T ∧
    uD S D ∘ₗ leviGL_E S d ∘ₗ XCB S C B
      = XST S (↑Sₕ) T ∘ₗ uD S D ∘ₗ leviGL_E S d
  ```
  `Sₕ` strengthened from `LinearMap` to `LinearEquiv` (its
  surjectivity is needed by the `pNormalForm_residual_orbit_iso`
  consumer). Cascaded correctly through `pNormalForm`,
  `pNormalForm_residual_orbit_iso`, and the two `residual_levi_*`
  helpers.

- **`residual_levi_extract` (line 440) — sorry-free.** ~250 lines
  closed. Forward extraction of the L0' isometry `h` from a
  parabolic conjugator. Four-step skeleton:
  1. **Step A:** preserve L0' via V0-component analysis +
     `Sₕ.injective` (LinearEquiv strengthening).
  2. **Step B:** define `qFun = codRestrict L0' qFunRaw _` where
     `qFunRaw := projE'_V ∘ p ∘ inE' ∘ L0'.subtype`.
  3. **Step C:** show injectivity via `flagEV0` preservation by
     `p` and `p⁻¹`.
  4. **Step D:** verify isometry via `IsOrthogonal p` + `XST_apply`
     substitution + `Cdual_pairing_eq` + reduction to
     `BT T₂ (h u) (h v) = BT T₁ u v`.

- **`residual_levi_build` (line 847) — sorry-free.** Constructs
  the Levi factor `d := extendL0'IsoToE' S h` extending
  `h : L0' ≃ L0'` by `id` on L1'; takes `p := leviGL_E S d`;
  verifies the conjugation via `leviGL_E_conj_XCB` reduced to two
  component identities (`CST Sₕ ∘ d.symm = CST Sₕ` and
  `lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂`).

- **`pNormalForm_residual_orbit_iso` — sorry-free** (public
  consumer). `Sₕ` as `LinearEquiv` enables direct passage to
  `residual_levi_extract` / `residual_levi_build`. `#print axioms`
  clean.

- **`pNormalForm` body** refactored to consume the new
  `pNormalForm_witnesses` signature (extract parabolic
  `p := uD D ∘ leviGL_E d`). Body sorry-free; depends on
  `pNormalForm_witnesses` so transitively `sorryAx`.

- **5 new helpers (private):**
  - `XST_apply` (line 329) — explicit unfolding of the
    multi-let block-matrix `XST` definition. Saves ~10 lines per
    consumer.
  - `extendL0'IsoToE'` (private noncomputable def) — block
    extension via `Submodule.prodEquivOfIsCompl`.
  - `extendL0'IsoToE'_symm_apply` — pointwise formula.
  - `projL1'_extendL0'IsoToE'_symm` — `projL1' ∘ d.symm = projL1'`.
  - `projL0'_extendL0'IsoToE'_symm` —
    `projL0' ∘ d.symm = h.symm ∘ projL0'`.

### Cross-cutting wins (session 9 / Round 7)

- **`prodEquivOfIsCompl` symm via
  `Submodule.toLinearMap_prodEquivOfIsCompl_symm`.** The symm
  coerces to `(linearProjOfIsCompl p q h).prod (linearProjOfIsCompl q p _)`,
  i.e., `prodEq.symm e' = (projL1' e', projL0' e')` for our
  `IsCompl L1' L0'`. Bypasses unfolding through `LinearEquiv.trans`.
- **`set ... with hdef` for opaque shorthands, BUT NOT for sums.**
  `set lhs_E := Cdual ... + T₂ ...` opaquefies the sum, breaking
  subsequent `rw [LinearMap.add_apply]`. Use `set` only for opaque
  applications.
- **`congr 1` does NOT split through outer `LinearMap.comp`.**
  For `XCB(A, B) = XCB(A', B') ∘ leviGL_E d`-style equations,
  prove `A = A'` and `B = B'` as separate `have`s and chain.
- **Linearity in 1st arg of `S.paired.pairing`: `map_add` first,
  then `add_apply`.** Reversed order fails.
- **`(qFun l : L0').val = qFunRaw l` is *definitionally* equal**
  when `qFun = LinearMap.codRestrict L0' qFunRaw _`. Use
  `exact h_val` (no `simpa`).
- **Trailing `rfl` after `simp only [..., map_zero]` is "No goals"
  lint.** Drop it.
- **LinearEquiv at definition; pass directly at use site.** When
  a private theorem strengthens `Sₕ` from LinearMap to LinearEquiv,
  the consumer call site that expects LinearMap should pass `Sₕ`
  directly (Lean auto-coerces). Explicit coercion fails type-check.
- **`S.V` ≡ `S.paired.E'` abbrev boundary requires explicit type
  ascription in helper defs.** Every `↑d.symm e'` application in
  helpers like `extendL0'IsoToE'` needs
  `(d.symm : S.paired.E' →ₗ[F] S.paired.E')` to bridge the abbrev.
- **`XST_apply` private helper near top of consuming section.**
  When a proof needs explicit unfolding of a multi-let block-matrix
  def, write a `private theorem _apply` early in the section.
- All public theorems re-audited via `#print axioms`:
  `pNormalForm_residual_orbit_iso`, `kernelImage_ker`,
  `kernelImage_im`, `kernelImage_dim` show only
  `[propext, Classical.choice, Quot.sound]`. `pNormalForm`
  transitively depends on `sorryAx` via `pNormalForm_witnesses`
  body (expected per Round 7 plan). **No custom axioms.**

## Prover Round 8 (session 10 — three-file parallel; partial closure + mathematical finding)

Net: 3 → 3 declaration-use `sorry` (positions changed; bare body-sorries
relocated into focused private helpers). `lake build` ✅ end of round;
0 custom axioms. **All public-theorem bodies are now sorry-free**;
remaining sorries are confined to private helpers. `pNormalForm`,
`sIndependenceAndOrbitCriterion`, and `main` carry transitive `sorryAx`
through those helpers, but the consumer-facing surface is clean.

### `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion` body sorry-free

**Public effect:** body of `sIndependenceAndOrbitCriterion` (line 502)
contains zero `sorry`s.  Both forward and reverse directions are fully
constructive.  Two scoped sorries on flag-stability conjuncts moved
into a focused private helper `isParabolicElement_ringInverse_of_orbit_witness`
(line 438), where they are documented with a Gap comment.

- **Signature change (option (a) + option (i) per Round 8 plan):** added
  `(hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)` hypotheses;
  collapsed `(Sₕ₁ Sₕ₂)` to a single `(Sₕ : S.L1' ≃ₗ[F] S.Vplus)`.
  Cascaded through `main`.

- **Reverse direction (sorry-free):** two-line proof:
  ```lean
  obtain ⟨p, hP, hConj⟩ :=
    (S.pNormalForm_residual_orbit_iso hNondeg hChar Sₕ T₁ T₂
        hT₁.1 hT₂.1).mpr hiso
  exact GOrbit_eq_of_isometry_conj S hP.1 hP.2.2.2 hConj
  ```
  Key insight: parabolic flag-stability is *not* needed for orbit
  equality — only the unit/orthogonal data of `p`. Helper
  `GOrbit_eq_of_isometry_conj` exposes this weakened hypothesis.

- **Forward direction (sorry-free body modulo helper):** four-step
  Route-B construction:
  1. Extract orbit witness `g` via `XST T₁ ∈ GOrbit (XST T₁)` +
     `rw [horbit]`.
  2. Lift `g` to `IsParabolicElement (Ring.inverse g)` via the new
     helper `isParabolicElement_ringInverse_of_orbit_witness` (the
     helper carries the only remaining sorries).
  3. Algebraically derive
     `Ring.inverse g ∘ XST T₁ = XST T₂ ∘ Ring.inverse g` via
     `Ring.inverse_mul_cancel`.
  4. Apply `pNormalForm_residual_orbit_iso (→)` with
     `p := Ring.inverse g`.

- **3 new private helpers added (sorry-free):**
  - `IsOrthogonal_mul` — composition closure under `IsOrthogonal`.
  - `IsOrthogonal_ringInverse` — `Ring.inverse` of an invertible
    isometry is an isometry.
  - `GOrbit_eq_of_isometry_conj` — orbit equality from a single
    conjugating isometry.  Uses an inline derivation of
    `Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g` via
    `noncomm_ring`.

- **1 new private helper with documented sorries:**
  `isParabolicElement_ringInverse_of_orbit_witness` — extracts an
  `IsParabolicElement` witness from `IsometryEnd` + a slice
  conjugation.  Sorry-free conjuncts: `IsUnit`, `IsOrthogonal`.
  Sorry'd conjuncts: `Submodule.map p flagE = flagE`,
  `Submodule.map p flagEV0 = flagEV0` (slice-transversality
  argument; needs `parametrizeX0PlusU_uniqueness`).

### `InducedOrbitToy/NormalForm.lean` — Tier A relocated to helper

Round 8 NormalForm prover punted the four-step
`pNormalForm_witnesses` construction, restructuring the bare body
sorry into a single isolated private helper.

- **`pNormalForm_witnesses_aux` (line 197) — sorry'd helper.** Holds
  the entire `(Sₕ, D, d, T) + IsSkewT + conjugation` existential.
  Carries the only remaining `sorry` in this file.  Body docstring
  (lines 152–196) walks through the full four-step blueprint plan.
- **`pNormalForm_witnesses` body (line 264) — sorry-free one-liner.**
  Replaced the body sorry with `exact pNormalForm_witnesses_aux ...`.
- **`pNormalForm` body** unchanged (already sorry-free).

This relocation is permitted by the Round-8 PROGRESS.md acceptance
criterion: "Acceptable to introduce one isolated helper `private def`
with its own sorry if Step 1 (d-construction) is intractable; in that
case the helper sorry must be documented with a `Gap:` comment block."

### `InducedOrbitToy/Slice.lean` — substantial structural data + mathematical gap finding

`parabolic_decompose` (line 1109) still carries one body-sorry, but
the proof body now contains ~460 lines of sorry-free structural data
(blocks, isos, isometry/pairing identities) and a mathematical
analysis identifying that the *statement* of `parabolic_decompose`
is too narrow.

- **Sorry-free data extracted:**
  - `pE_equiv : S.E ≃ₗ[F] S.E`, `pV0_equiv : S.V0 ≃ₗ[F] S.V0`,
    `pE'_equiv : S.E' ≃ₗ[F] S.E'` — diagonal-block actions of `p` and
    `p⁻¹`, packaged as `LinearEquiv`s.
  - Round-trip identities (`pE_round_left/right`, etc.) via
    decomposition `(βi, γi, pE'_inv e') = (βi, 0, 0) + (0, γi, 0) +
    (0, 0, pE'_inv e')` + linearity of `p`.
  - `pV0_iso : ∀ u v, S.formV0 (pV0_fn u) (pV0_fn v) = S.formV0 u v`
    via `_hpIso` on V0-pairs.
  - `hkey : ∀ e e', λ(pE_fn e, pE'_fn e') = λ(e, e')` — forces
    `pE = lambdaDualE pE'_equiv.symm`.

- **Mathematical gap identified.** Setting `d := pE'_equiv`, `g := pV0_equiv`,
  `D e' := (p (0, 0, d.symm e')).2.1`, the V0- and E'-components match
  automatically and the E-component splits into:
  - `(p (0, v, 0)).1 = Cdual D (pV0_fn v)` — provable from `_hpIso`.
  - `(p (0, 0, e')).1 = ½ Cdual D (D (pE'_fn e'))` — **NOT provable**
    from `_hpIso` alone.  Setting
    `f e' := (p (0, 0, e')).1 - ½ Cdual D (D (pE'_fn e'))`, the
    isometry only forces
    `λ(f e₁', pE'_fn e₂') + ε λ(f e₂', pE'_fn e₁') = 0` — i.e.
    `f` is `IsSkewB`-shaped.  In general `f ≠ 0`.

- **Conclusion:** `parabolic_decompose` as stated requires the
  unipotent factor to have shape `uD D` (i.e. zero residual `B'`),
  but a general parabolic isometry decomposes as
  `(uD D) ∘ (uB' B')_skew ∘ leviGL_E d ∘ leviGL_V0 g` where
  `B' : E' →ₗ E` is `IsSkewB`-shaped.  The current `uD` definition
  is missing the `B'` parameter.

- **Recommendation:** option (a) generalise `uD` to accept a residual
  `B'`, restate `parabolic_decompose` to expose `(D, B', d, g)`.
  Option (b) narrow the hypothesis to "geometric parabolic" elements
  satisfying `B' = 0` implicitly.  Round 7 consumers
  (`residual_levi_extract`, `residual_levi_build`) sidestepped
  `parabolic_decompose` via Option B, so this signature change is
  **non-blocking** for the public theorems.

- **`parabolic_decompose` has zero consumers** in the project — the
  helper is purely structural.  Carrying its sorry does not block
  any public-theorem axiom-cleanliness goal.

### Cross-cutting wins (session 10 / Round 8)

- **`Ring.inverse` for orbit/conjugation algebra on `Module.End F V`.**
  `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`,
  `IsUnit.ringInverse` are the canonical tools for "best-effort
  inverse" constructions in orbit predicates.  No division-ring
  needed.
- **`noncomm_ring` for module-endomorphism associativity.** Closes
  associativity-only goals on `Module.End F V` where `ring`
  (commutative-only) fails.  Critical for the inline derivation
  `Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g`.
- **Body-sorry → helper-sorry refactor pattern.** When a body proof
  requires substantial new infrastructure but the surrounding
  theorem-shape is correct, extract the obstruction into a focused
  private helper with its own sorry + Gap comment.  The public-facing
  body becomes a one-liner; the sorry is pinned to a specific
  construction.  Acceptance criterion explicitly permits this when
  the helper Gap is documented.
- **Mathematical-gap finding via partial closure.** The Slice prover
  attempted a full closure of `parabolic_decompose`, extracted ~460
  lines of structural data, then identified that the statement is
  itself imprecise.  This is a **structural-fix outcome**, not a
  prover failure: the next round needs a `parabolic_decompose`
  signature change, not a "try harder" pass.
- **Public-surface vs helper-surface accounting.** End-of-round audit
  separated public-theorem axioms (clean for
  `pNormalForm_residual_orbit_iso`, `inducedOrbits`, `multiplicity*`)
  from transitive `sorryAx` (in `pNormalForm`,
  `sIndependenceAndOrbitCriterion`, `main`).  This framing makes
  partial-closure outcomes legible to the next round's planner.

## Prover Round 9 (session 11 — partial; build break in NormalForm; signature cascade landed)

**Net (verified by plan agent):** `lake build` is **NOT green** at end
of round — `InducedOrbitToy/NormalForm.lean` has compilation errors at
lines 302–308 from a partial Step 0.75 sub-construction the prover
left in unfinished form.  The prover's report claimed `lake build` is
green; this is incorrect.  `Orbits.lean` and `Slice.lean` both compile
in isolation.

Round 9 still delivered real partial progress that Round 10 inherits:

### `InducedOrbitToy/NormalForm.lean` — signature cascade + dim chain

- **`_hL1' : Module.finrank F S.L1' = c S.toX0Setup` hypothesis** added
  and threaded through:
  - `pNormalForm_witnesses_aux` (line 197),
  - `pNormalForm_witnesses` (line 264),
  - `pNormalForm` (line 306, public).
  No cross-file cascade (verified: `pNormalForm` has zero in-project
  consumers).  `pNormalForm_residual_orbit_iso` is independent and
  remains unchanged.
- **Step 0 (sorry-free):** `Sₕ : L1' ≃ Vplus` constructed via
  `LinearEquiv.ofFinrankEq` using `_hL1'` + `finrank_Vplus_eq_c`.
- **Step 0.5 — full dimension chain (sorry-free):**
  - `h_Cbar_surj : Function.Surjective (Cbar S C)` — via
    `LinearMap.range_eq_top.mp` + `Submodule.eq_top_of_finrank_eq` +
    `_hRank` + `c_eq_finrank_quotient`.
  - `h_dim_ker_Cbar : finrank (ker (Cbar S C)) = finrank E' - c` —
    rank-nullity via `LinearMap.finrank_range_add_finrank_ker`.
  - `h_dim_L0' : finrank L0' = finrank E' - c` — uses `IsCompl L1' L0'`
    + `_hL1'` + `Submodule.finrank_sup_add_finrank_inf_eq`.
  - `h_dim_match : finrank L0' = finrank (ker (Cbar S C))`.
- **Step 0.75 — partial isomorphism setup (sorry-free):**
  - `gL0 : S.L0' ≃ₗ[F] (LinearMap.ker (Cbar S C))` via
    `LinearEquiv.ofFinrankEq`.
  - `K' ⊕ ker(Cbar)` complement extracted via
    `Submodule.exists_isCompl`.
- **Step 0.75 partial-broken:** the inline `CbarK'_inj`/`CbarK'_surj`
  closure attempt at lines 277–310 is unfinished and contains TWO
  bugs:
  1. **Variable swap:** at line 300 the destructure
     `obtain ⟨k, hk_K', n, hn_ker, hsum⟩ := hz_top` names `hk_K'` and
     `hn_ker` opposite to their actual types.  After
     `rw [← hK'_compl.codisjoint.eq_top, Submodule.mem_sup]` on
     `hK'_compl : IsCompl (ker (Cbar S C)) K'`, the destructure yields
     `k ∈ ker(Cbar)`, `n ∈ K'`, `k + n = z`.  The prover swapped the
     names.
  2. **`linarith` over a non-ordered field:** line 308 uses
     `linarith [hsum]` to derive `k = z - n` from `k + n = z`, but the
     codomain `S.paired.E'` is a generic `[Field F]`-module, not a
     `LinearOrderedField`.  Use `linear_combination hsum` (or
     equivalently `eq_sub_of_add_eq hsum.symm`) instead.

  Two `sorry`s remain inside this block (lines 309, 310) — Round 10
  must either remove this block entirely (preferring a cleaner
  approach) or fix the two bugs and complete it.
- **Step 1 (sorry, line 322), Step 2 (sorry, line 339), Step 3 (sorry,
  line 356):** the three substantive existential sub-claims of the
  d/D/T construction.

### `InducedOrbitToy/Orbits.lean` — kernel-identification refactor (real progress)

- **Sorry count:** 2 → 2 (positions changed; clean structural refactor).
- **3 new sorry-free private helpers** added near line 421:
  - `orbit_conj_rearr` (line 421) — algebraic rearrangement of
    `XST T₁ = g · XST T₂ · Ring.inverse g` into
    `Ring.inverse g · XST T₁ = XST T₂ · Ring.inverse g` and
    `g · XST T₂ = XST T₁ · g`.  Uses `Ring.inverse_mul_cancel`,
    `Ring.mul_inverse_cancel`.
  - `flagE_le_ker_XST` (line 457) — unconditionally
    `S.flagE ⊆ ker (XST Sₕ T)` via the explicit `XST(e, 0, 0) = 0`.
  - `ker_XST_eq_flagE_of_injective` (line 444) — under
    `LinearMap.ker T = ⊥`, `ker (XST Sₕ T) = S.flagE`.  Uses
    `kernelImage_ker` (NormalForm) + `Submodule.map_bot`.
- **Helper body refactor:** the body of
  `isParabolicElement_ringInverse_of_orbit_witness` now extracts the
  kernel containments
  `(Ring.inverse g)(flagE) ⊆ ker XST T₂` and
  `g(flagE) ⊆ ker XST T₁` fully constructively (~40 lines).  The
  flagE conjunct closes fully **conditional on**
  `ker XST T₁ = flagE ∧ ker XST T₂ = flagE` (via `obtain ⟨hkerT1, hkerT2⟩`).
- **2 surviving sorries** (positions changed):
  - Line 563: kernel-identification claim
    `ker XST T_i = flagE` for both indices.  Mathematical truth in 2
    of 3 cases (ε=-1; ε=+1, l even — both have `ker T_i = ⊥`).
    **Mis-stated in case 3** (ε=+1, l odd): `dim ker T_i = 1`, so
    `ker XST T_i ⊋ flagE`.  Round 10 fix: tighten helper signature.
  - Line 624: flagEV0 conjunct.  Kernel-based argument doesn't apply
    (`flagEV0 ⊄ ker XST` generically).  Needs the
    `parabolic_decompose` Bruhat-style argument; deferred until Tier S
    #6 lands in polish.
- **`#print axioms` (Orbits.lean public surface, unchanged):**
  - `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`,
    `multiplicityEvenSymmCase` — clean
    `[propext, Classical.choice, Quot.sound]`.
  - `sIndependenceAndOrbitCriterion`, `main` — transitive `sorryAx`
    via the helper's two sorries.

### `InducedOrbitToy/Slice.lean`, `Basic.lean`, `LocalForms.lean`, `X0Geometry.lean` — verify-only

No edits this round.  All four files compile in isolation.

### Cross-cutting wins (session 11 / Round 9)

- **Round 8 → Round 9 dim chain pattern (NormalForm).**  When a
  helper takes a structural-finrank hypothesis (`_hL1'`,
  `_hRank`), the dim chain (Cbar surjectivity, ker dim, complement
  dim) is fully closeable via Mathlib lemmas without any sorrys.
  Pattern is reusable for future bundle/quotient constructions.
- **Kernel-identification refactor pattern (Orbits).**  When two
  scoped sorries reduce to a common sub-claim
  (`ker(XST T_i) = flagE` for `i = 1, 2`), bundle them into one
  conjunctive sorry consumed by `obtain ⟨hkerT1, hkerT2⟩`.  Cleaner
  than repeated case work and exposes the precise mathematical truth
  condition.
- **Kernel-form via `kernelImage_ker` + `Submodule.map_bot`:**
  when `ker T = ⊥`, the `(ker T).map L0'.subtype` quotient collapses
  to `⊥`, reducing `ker XST = ⊤ ×ˢ ⊥ ×ˢ (ker T).map L0'.subtype` to
  `S.flagE = ⊤ ×ˢ ⊥ ×ˢ ⊥`.
- **Mathematical-validity case split.**  The Round-9 Orbits prover
  verified that the helper's claim is **case-dependent** (true in
  cases 1-2, false in case 3) and identified the correct fix as
  signature tightening (option (a)).  This is structural, not a
  prover failure.
- **Build-break vs prover self-report dissonance.** Round 9 NormalForm
  prover claimed `lake build` green; plan-agent verification disproved
  this.  Lesson: always run `lake build` independently before merging
  task results.
