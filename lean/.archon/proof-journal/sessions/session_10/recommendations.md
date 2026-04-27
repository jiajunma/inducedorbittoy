# Recommendations for Round 9 Plan Agent

## Round 8 outcome at a glance

- **Sorry count:** 3 → **3** (0 net). Plan target was 3 → 0; achieved structural reorganisation but no net closure.
- **Each remaining sorry is now isolated** to a focused private helper with a documented Gap:
  - `pNormalForm_witnesses_aux` (NormalForm.lean line 197) — single isolated sorry; full four-step plan in docstring.
  - `isParabolicElement_ringInverse_of_orbit_witness` (Orbits.lean line 438) — 2 scoped sorries on flag-stability conjuncts.
  - `parabolic_decompose` (Slice.lean line 1109) — body has ~460 new constructive lines; final assembly sorry'd at line 1572. **Statement-level gap identified — see Slice action item below.**
- **Public theorems status:**
  - `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`, `pNormalForm_residual_orbit_iso`: clean axioms (no `sorryAx`).
  - `sIndependenceAndOrbitCriterion`, `main`, `pNormalForm`: still depend transitively on `sorryAx` via private helpers.
- **Build:** green; 3 sorry warnings + 1 pre-existing unused-variable lint.

## Critical decision for Round 9: the `parabolic_decompose` signature gap

The Slice prover discovered that the **statement** of `parabolic_decompose` — not just the proof — is too narrow. A general parabolic isometry has form `(uD D + B') ∘ leviGL_E d ∘ leviGL_V0 g` for some skew `B' : E' →ₗ[F] E`, and the current `uD D` only captures the `B' = 0` case.

**Two options for Round 9:**

(a) **Mathematically correct route (preferred):** generalise `uD` to accept a residual skew parameter `B' : E' →ₗ[F] E` satisfying `IsSkewB S B'`. Cascade through:
- `uD` definition (Slice.lean) — add `B'` parameter.
- All `uD_*` lemmas (`uD_apply`, `uD_neg_inverse`, `uD_isParabolic`, `uD_conj_XCB`, `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`).
- `pNormalForm_witnesses` (NormalForm.lean) — Sₕ + d + D + **B'** + T.
- `pNormalForm` consumer.
- `pNormalForm_residual_orbit_iso` consumer.

This is a **major refactor** spanning Slice.lean + NormalForm.lean. Estimated 200–400 lines of touched code. **Non-trivial cross-file coordination.**

(b) **Narrowing route:** keep `parabolic_decompose` signature as-is and add a hypothesis that `B' = 0` (i.e., a hypothesis that `p` lies in the geometric subgroup `uD D ∘ leviGL_E d ∘ leviGL_V0 g`). Less mathematically clean; downstream consumers may not be able to verify the new hypothesis.

(c) **Pragmatic route (recommended for Round 9):** **Don't touch `parabolic_decompose` in Round 9.** It is non-blocking for public theorems (Round 7 sidestepped it via Option B). The ~460 lines of new constructive content is preserved as scaffolding. Defer the (a) vs (b) decision to polish stage. Round 9 focuses on the other two helpers.

## Recommended Round 9 plan

### Option A — single-objective focus on `pNormalForm_witnesses_aux` (preferred for Round 9)

**Assign one prover to `NormalForm.lean :: pNormalForm_witnesses_aux` (line 197).**

This is the deepest-blocking helper. Closing it makes `pNormalForm_witnesses` and `pNormalForm` sorry-free, and propagates cleanliness through `pNormalForm_residual_orbit_iso` (already sorry-free transitively).

**Four-step body plan** (already in the in-file Gap docstring at lines 152–196):

1. **Build `(Sₕ, d)` from `_hRank`.**
   - `Cbar S C` is surjective by `_hRank` + `dim (V0/range X0) = c` (`finrank_Vplus_eq_c`).
   - `dim ker (Cbar S C) = dim E' - c`.
   - **Subtle:** `dim L1' = c` is needed for `Sₕ : L1' ≃ Vplus`. **This is NOT enforceable from `SliceSetup` alone** (counterexamples: `L1' = E', L0' = 0`). Round-9 prover should **add a hypothesis** `(_hL1' : Module.finrank F S.L1' = c S.toX0Setup)` to `pNormalForm_witnesses_aux`'s signature, and cascade through `pNormalForm_witnesses`, `pNormalForm`, and `pNormalForm_residual_orbit_iso`.
   - Construct `d : E' ≃ E'` by combining `L0' ≃ ker (Cbar S C)` with `L1' ≃ K'` (a chosen complement of `ker (Cbar S C)`) normalised so that `(Cbar S C) ∘ d.symm |_{L1'} = mkQ ∘ Sₕ`.

2. **Lift `(C ∘ d.symm - CST Sₕ)` through `X0`.**
   - The map lands in `range X0` by Step 1.
   - Lift via a section of `X0 |_K : K ≃ range X0` (any complement `K` of `ker X0` in `V0`).
   - Mathlib: `Submodule.exists_isCompl`, `LinearEquiv.ofInjective`, `LinearMap.codRestrict`.

3. **Identify `T : L0' →ₗ L0`.**
   - After `leviGL_E_conj_XCB` and `uD_conj_XCB`, the conjugated operator equals `XCB(C', B'')` with explicit `(C', B'')`.
   - `C' = C ∘ d.symm - X0 ∘ D = CST Sₕ` (by Step 2).
   - `B''` is the Cdual-corrected `B' = lambdaDualE d.symm ∘ B ∘ d.symm`.
   - Choose `D|_{L1'}` carefully (via `vplusKerPairing_isPerfPair`) so that `B''(L1') = 0` and the skew condition forces `B''(L0') ⊂ L0`. The L0'-restriction defines `T`.

4. **Verify `IsSkewT T` + conjugation.**
   - Skewness propagates from `_hB`.
   - Conjugation reduces to `parametrizeX0PlusU_uniqueness` applied to `(C', B'')` and `(CST Sₕ, BST T)`.

**Estimated effort:** ~200–300 lines. May exceed a single round; if so, Round 9 may further split:
- `pNormalForm_levi_data` (Step 1) — d-construction.
- `pNormalForm_lift_D` (Step 2) — X0-lift.
- `pNormalForm_T_construction` (Step 3) — T extraction.
- `pNormalForm_verify` (Step 4) — final verification.

If split, each helper would carry its own sorry; net declaration count would increase from 1 to 4 temporarily. The plan agent should weigh single-helper vs split-helper based on tractability.

**Stop conditions:**
- If Step 1 is intractable, leave the helper as-is and instead spend the round refining its Gap docstring with detailed sub-step plans.
- If `dim L1' = c` cannot be derived from existing hypotheses, add the explicit hypothesis as outlined above.

**Acceptance criteria:**
- `lake build` is green.
- The sorry at `pNormalForm_witnesses_aux` is replaced by a real proof (or split into smaller helpers each with one focused sorry).
- `#print axioms pNormalForm` shows only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`) — assuming the helper closes fully.

### Option B — parallel two-file dispatch (closes both Orbits + NormalForm helpers in one round)

If the harness can dispatch multiple provers concurrently, try:

- **Prover 1:** `NormalForm.lean :: pNormalForm_witnesses_aux` (Option A above).
- **Prover 2:** `Orbits.lean :: isParabolicElement_ringInverse_of_orbit_witness` (lines 451 + 454 — the two flag-stability sorries).

The two are **independent** at the source level (no edit overlap). End-of-round merge is conflict-free.

**Orbits prover plan (per session-10 task report):**

The helper extracts `IsParabolicElement S (Ring.inverse g)` from `IsometryEnd S g` plus a slice conjugation hypothesis. Sorry-free conjuncts (already done): `IsUnit (Ring.inverse g)`, `IsOrthogonal S.ambientForm (Ring.inverse g)`. Sorry'd conjuncts: the two flag-stability sorries.

**Two routes:**
- **Route A (depends on `parabolic_decompose`):** wait for Slice prover to land `parabolic_decompose`, then apply it to `Ring.inverse g` after upgrading `IsometryEnd` to a flag-preserving form. *Round 9 is unlikely to land `parabolic_decompose` per the gap analysis — defer this route.*
- **Route B (preferred for Round 9):** direct slice-transversality argument using `parametrizeX0PlusU_uniqueness` + the structure of `range XST`. The conjugation equation `XST T₁ = g ∘ₗ XST T₂ ∘ₗ Ring.inverse g` translates to constraints on `g`'s action on `flagEV0`. Concretely:
  1. Compute `g (flagEV0)` using the conjugation equation and `range XST ⊆ flagEV0`.
  2. Use `parametrizeX0PlusU_uniqueness` to descend to flag preservation.
  3. Symmetric argument for `flagE` via the `flagE ⊂ flagEV0` inclusion.

**Estimated effort:** ~80–120 lines.

**Stop conditions:**
- If Route B requires substantial new infrastructure (e.g., a "range XST" lemma), build that infrastructure as a separate sorry-free helper first.
- If both flag-stability conjuncts cannot be closed in a single round, focus on `flagE` first (the easier of the two), leaving `flagEV0` sorry'd.

### NOT recommended for Round 9

- **Closing `parabolic_decompose` directly with the current signature.** The mathematical analysis in session 10's Slice task report shows the statement is not provable in full generality — a parameter is missing.
- **Generalising `uD` to accept a `B'` parameter in Round 9.** This is the (a) route from the gap discussion above; it requires a major refactor of Slice.lean + NormalForm.lean. Defer to polish stage.

## Targets closest to completion (priority order for Round 9)

1. **`pNormalForm_witnesses_aux`** (NormalForm.lean line 197) — single isolated sorry, well-documented body plan. Closing it makes `pNormalForm` sorry-free. **Top priority.**

2. **`isParabolicElement_ringInverse_of_orbit_witness`** (Orbits.lean line 438) — 2 scoped sorries on flag-stability. Route B (direct slice-transversality) is tractable and independent of `parabolic_decompose`. **Secondary priority; can run in parallel with #1.**

3. **`parabolic_decompose`** (Slice.lean line 1109) — defer to polish stage. The statement-level gap is the main blocker, not the proof. The ~460 lines of new constructive content already in the body are preserved as scaffolding for whoever picks it up.

## Approaches that showed promise but need more work (Round 9 carry-forward)

- **`noncomm_ring` for module-endomorphism associativity.** Use it freely on `Module.End F V` goals where commutative `ring` fails. Critical for `Ring.inverse` algebra.

- **`Ring.inverse` packaging for orbit predicates.** No division-ring needed. The pair `Ring.inverse_mul_cancel` / `Ring.mul_inverse_cancel` plus `IsUnit.ringInverse` covers most use cases.

- **`GOrbit_eq_of_isometry_conj` weakened hypothesis.** Orbit equality from a single conjugating *isometry* (not parabolic) — flag-stability not needed. Reusable for any future orbit-equality argument.

- **Diagonal-block extraction from `_hpUnit.unit.inv` for parabolic isometries.** Round 8's pattern in `parabolic_decompose` is sound and reusable; just doesn't close the statement-as-written. The helper extractions (pE_fn, pV0_fn, pE'_fn, bijectivity, V0-isometry, cross-pairing) are general-purpose.

- **`LinearEquiv` from `LinearMap` + inverse via anonymous-constructor.** `{ pE_fn with invFun := pE_inv, left_inv, right_inv }` is cleaner than `LinearEquiv.ofBijective`.

## Targets blocked (do not assign)

- **`parabolic_decompose`** (Slice.lean line 1109) — **the statement is too narrow** (missing `B'` parameter). Do not assign Round 9 prover to this; let the existing scaffolding sit and revisit at polish stage with a refactor decision.

## Reusable proof patterns discovered (Round 8)

These flow into PROJECT_STATUS.md's knowledge base. Augments session-9 list.

1. **`noncomm_ring` for `Module.End F V` associativity.** Where commutative `ring` fails, `noncomm_ring` closes any associativity goal on module endomorphisms. Essential.

2. **`Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g` (units).** Derive via uniqueness from `(g * Ring.inverse p) * (p * Ring.inverse g) = 1` plus `Ring.inverse_mul_cancel` and `Ring.mul_inverse_cancel`. Closing associativity with `noncomm_ring`.

3. **Orbit equality from single conjugating isometry — flag-stability NOT needed.** New `GOrbit_eq_of_isometry_conj` helper in Orbits.lean. Both inclusions transit through `g ↦ g * Ring.inverse p` (or dual).

4. **Diagonal-block extraction from `_hpUnit.unit.inv`.** When `p` preserves a flag, build inverse maps `pE_inv`, `pV0_inv`, `pE'_inv` from `pinv` and prove bijectivity via round-trip identities (3-step calc chains). Used in `parabolic_decompose` body.

5. **`LinearEquiv` via anonymous-constructor `{ linear_map with invFun := ..., left_inv := ..., right_inv := ... }`.** Cleaner than `LinearEquiv.ofBijective` when both `LinearMap` and explicit inverse are already in scope.

6. **Forward calc with reverse-direction `rw`.** When `rw [pE_inv_eq]` doesn't fire on `p (pinv (e, 0, 0)) = (pE_fn (pE_inv e), 0, 0)`, restructure as forward calc starting from the desired identity: `(e, 0, 0) = p (pinv (e, 0, 0)) = p (pE_inv e, 0, 0) = (pE_fn (pE_inv e), 0, 0)`. The `rw` fires when the goal has the substituted form on the right.

7. **Statement-level gap analysis.** When a proof is repeatedly blocked at the same step despite multiple approaches, examine whether the *statement* is provable. The `parabolic_decompose` gap (`uD D` should be `uD D + B'`) is a model example. Document the gap analysis directly in the in-file docstring so future provers don't re-discover it.

8. **Cross-file parallel dispatch with line-range partitioning.** Plan agent's careful partitioning (NormalForm 190–230, Orbits 292–630, Slice 1065–1574) enabled three concurrent provers with clean end-of-round merge. Reusable pattern for future multi-file rounds.

## End-of-round housekeeping

- **Stale comments:** `NormalForm.lean` lines 344, 357 reference the long-removed `L0_isotropic` field. They compile cleanly but should be refreshed during the next NormalForm edit pass (Round 8 carried forward; Round 9 may again carry forward).
- **`Slice.lean` warnings:** simp argument trimming was completed in Round 8 (removed unused `zero_add`, `LinearMap.zero_apply`).
- **Task results files:** Round 8's reports under `task_results/InducedOrbitToy_*.lean.md` should be archived under `processed/round8/` at the start of Round 9 to maintain history.
- **Pre-existing lint:** `X0Geometry.lean:221:35: unused variable hlambda` — must be left intact (part of the autoformalised signature for `sDual_restrict_ker_isIso`).
