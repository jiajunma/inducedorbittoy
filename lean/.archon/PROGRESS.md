# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 2)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Latest review: `.archon/proof-journal/sessions/session_3/summary.md`
  and `.archon/proof-journal/sessions/session_3/recommendations.md`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, 2026-04-27)

- `lake build` succeeds; only `sorry` warnings.
- Custom `axiom` declarations: 0 (verified by inspection of all 6 .lean files).
- Round-1 progress: 22 → 8 declaration-use `sorry` warnings.
- Remaining declaration-use `sorry` lines (verified by `lake build`):
  - `InducedOrbitToy/X0Geometry.lean`: 1 (line 206 — `sDual_restrict_ker_isIso`,
    body still contains 2 scoped `sorry` at lines 261, 264).
  - `InducedOrbitToy/Slice.lean`: 2 (line 232 — `parametrizeX0PlusU_existence`;
    line 391 — `uD_isParabolic`). Both documented as autoformalization bugs;
    do **not** retry until upstream data fixes land.
  - `InducedOrbitToy/NormalForm.lean`: 4 (line 167 — `pNormalForm`;
    line 199 — `pNormalForm_residual_orbit_iso`;
    line 302 — `kernelImage_ker` (body contains 2 scoped `sorry` at 344, 350);
    line 397 — `kernelImage_im`).
  - `InducedOrbitToy/LocalForms.lean`: 0 ✅
  - `InducedOrbitToy/Orbits.lean`: 1 (line 242 — `sIndependenceAndOrbitCriterion`,
    body contains 2 scoped `sorry` at 260, 268).

## Round Plan

The remaining 8 sorries split into four tiers (see session 3
recommendations). This round (Round 2) handles only **Tier A** —
proofs that are provable now without any upstream data refactor.

| Tier | Targets | Status |
|---|---|---|
| A | `pNormalForm`, `pNormalForm_residual_orbit_iso` (NormalForm.lean) — provable now | **assigned this round** |
| A (deferred) | `sIndependenceAndOrbitCriterion` (Orbits.lean) — depends on Tier A NormalForm targets | round 3 (after this lands) |
| B | `sDual_restrict_ker_isIso` (X0Geometry.lean) — needs `Basic.lean :: DualTransposeData` to expose `range Tdual ≤ L1` and `finrank L1 = finrank ker S.X0` | round 4 (data refactor) |
| C | `kernelImage_ker`, `kernelImage_im` (NormalForm.lean) — needs `SliceSetup` to expose Lagrangian condition `λ(L1, L0') = 0` and `Sₕ` typed as `LinearEquiv` | round 4/5 (data refactor) |
| D | `parametrizeX0PlusU_existence`, `uD_isParabolic` (Slice.lean) — autoformalization statement bugs (`UnipotentRadical` too loose; `IsAdjointPair` self-adjoint vs isometry) | round 5+ (statement refactor by directive) |

This split keeps each round atomic (one file per agent, no cross-file
edits in flight) and avoids cascading data-refactor breakage.

## Current Objectives (Round 2)

**One objective.** All other files are blocked on upstream data refactors
or downstream of the NormalForm targets below; do not assign them this
round.

### 1. `InducedOrbitToy/NormalForm.lean` — fill 2 of 4 sorries

Targets (Tier A — both provable now, no data refactor required):

- `pNormalForm` (line 167)
- `pNormalForm_residual_orbit_iso` (line 199)

Do **not** touch `kernelImage_ker` (line 302) or `kernelImage_im`
(line 397) — they are blocked on upstream `SliceSetup` data and will be
re-decomposed in a later round. Leave them as-is (their bodies already
have helpful scoped `sorry`s and outline comments).

#### Informal content

The blueprint outline is already inline as docstrings above each
declaration in `NormalForm.lean`. The prover should re-read those before
drafting. Cross-references:

- `references/blueprint_verified.md §prop:p-normal-form` — items 1–3 for
  `pNormalForm`; "residual-orbit isometry" for `pNormalForm_residual_orbit_iso`.
- `.archon/informal/normalform.md` — per-file informal sketch.

#### Strategy for `pNormalForm` (line 167)

The hypothesis bundle is
`(_hNondeg, _hChar, C, B, _hB : IsSkewB B, _hRank)`. The conclusion
asks for `(Sₕ, T, hSkewT, p, hPara, hConj)` such that
`p ∘ XCB C B = XST Sₕ T ∘ p`.

1. **Construct `Sₕ : L1' →ₗ[F] Vplus`.** Use `_hRank` (rank `Cbar S C =
   c S`) plus the rank-nullity bridge `c_eq_finrank_quotient` and
   `finrank_Vplus_eq_c` (both already in scope from `X0Geometry.lean` /
   `Basic.lean`) to obtain a linear map whose rank matches the dimension
   of `Vplus`. The simplest route is:
   - factor `Cbar S C` through its image inside `S.V0 ⧸ range S.X0`,
   - identify the image with `S.Vplus` via `VplusEquivQuotientRange`
     (already proved in `X0Geometry.lean`),
   - precompose with the (unique) factorisation of `Cbar S C` from
     `_hRank` to obtain `Sₕ : L1' →ₗ[F] Vplus`.
   This is the Levi factor adjustment — the `C|_{L1'} = Sₕ`,
   `C|_{L0'} = 0` decomposition the blueprint describes.

2. **Pick `D : E' →ₗ[F] V0`** that absorbs the `B|_{L1'}` block via the
   unipotent conjugation `uD S D` (from `Slice.lean`, sorry-free this
   round). The blueprint specifies `D` as the unique solution of
   `λ(D e', v) = formV0 v (C e')` for `e' ∈ L1'`, `v ∈ S.Vplus`.
   Concretely, define `D : E' →ₗ[F] V0` componentwise on the `L1' ⊕ L0'`
   decomposition (`S.isComplL'`):
   - on `L0'`: zero,
   - on `L1'`: the dual transpose of `C` along `lambda` (the same
     `Cdual` construction that `Slice.lean` uses, but in the opposite
     direction — invoke `S.lambda.toPerfPair` directly).

3. **Set `T := projL0' (B - Cdual D ∘ C)`** (the residual `L0' →ₗ[F] L0`
   block after absorbing `B|_{L1'}` and `Cdual D C` cross-terms). Verify
   `IsSkewT T` from `_hB : IsSkewB B`, `Cdual_X0_apply`, `S.epsSymm`,
   and `S.skew` — the same identity used in `uD_conj_XCB`.

4. **Set `p := uD S D`** (parabolic from Slice.lean). The conjugation
   `p ∘ XCB C B = XST Sₕ T ∘ p` is exactly `uD_conj_XCB` once the
   parameters are aligned.

5. **`IsParabolicElement p`** is an open obligation — its
   `IsAdjointPair B B p p` conjunct is currently `sorry` (Tier D).
   For *this* round, build `IsParabolicElement` using:
   - `IsUnit p` from `uD_neg_inverse` (proved): `uD D` and `uD (-D)`
     are mutual inverses, hence each is a unit;
   - flag preservation from `uD_isParabolic` (the two non-Tier-D
     conjuncts are proved);
   - the `IsAdjointPair B B p p` conjunct: the prover may either
     (a) attempt a direct proof here (it is *false in general* per the
     `uD_isParabolic` doc; do not waste cycles on this), or
     (b) leave a single scoped `sorry` and document that this conjunct
     of `pNormalForm` inherits the Tier D blocker. Option (b) is
     **preferred**.

#### Strategy for `pNormalForm_residual_orbit_iso` (line 199)

Bidirectional iff between (a) existence of a parabolic `p` with
`p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` and (b) `Bilinear.AreIsometric (BT T₁) (BT T₂)`.

- **(→)** Given parabolic `p`, the action descends to a Levi factor
  `h : L0' ≃ₗ[F] L0'` (use `S.isComplL'` to extract the `L0'` block of
  `p`). Compute `BT T₂ (h u) (h v) = BT T₁ u v` from
  `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` and the `XST_apply` formula
  (already proved in `NormalForm.lean`).
- **(←)** Given `h : L0' ≃ₗ[F] L0'` an isometry of `BT T₁ ↦ BT T₂`,
  build `p` as `(h⁻¹)^∨ ⊕ id ⊕ h` on the block decomposition
  `S.V = E × V₀ × E'` (with `E = L1 ⊕ L0`, `E' = L1' ⊕ L0'`). The
  conjugation calculation reduces to the diagonal blocks via
  `XST_apply` and the isometry hypothesis.

For the `IsParabolicElement p` part of the (←) direction, apply the
same option (b) above: leave the `IsAdjointPair B B p p` conjunct as a
scoped `sorry` if needed and document the Tier D inheritance.

#### Acceptance criteria for this objective

- Both `pNormalForm` and `pNormalForm_residual_orbit_iso` either
  - close completely, or
  - close everything *except* the `IsAdjointPair B B p p` conjunct of
    `IsParabolicElement` (which inherits the Slice.lean Tier D bug).
    Use a clearly-scoped internal `sorry` for *only* that conjunct, with
    an explicit comment naming the upstream blocker.
- File compiles in isolation (`lake env lean InducedOrbitToy/NormalForm.lean`).
- `lake build` is still green (only `sorry` warnings).
- No new `axiom` declarations.
- Helpers introduced are `private` and live inside `NormalForm.lean`.

#### Reusable Mathlib lemmas confirmed available (carry forward)

- `LinearMap.IsPerfPair.of_injective`, `LinearMap.toPerfPair`,
  `LinearMap.toPerfPair_apply`, `LinearMap.apply_symm_toPerfPair_self`.
- `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`,
  `Subspace.dual_finrank_eq`.
- `LinearMap.IsAdjointPair`, `LinearMap.IsAdjointPair.eq` (note the bare
  `LinearMap` namespace, **not** `LinearMap.BilinForm`).
- `Submodule.linearProjOfIsCompl`, `IsCompl.disjoint`, `IsCompl.codisjoint`,
  `Disjoint.eq_bot`, `Codisjoint.eq_top`.
- `Module.finrank_prod`, `Submodule.finrank_map_subtype_eq`,
  `LinearMap.finrank_range_add_finrank_ker`,
  `Submodule.finrank_quotient_add_finrank`.
- `submoduleProdEquiv` and `finrank_submodule_prod` already exist as
  `private` helpers in `NormalForm.lean` — reuse, do not duplicate.

#### Reusable Slice.lean lemmas (already proved this stage)

All of the following are sorry-free in `Slice.lean` and may be invoked
freely:
- `Cdual` (def), `Cdual_pairing_eq`, `Cdual_neg`, `Cdual_X0_apply`.
- `lambda_isPerfPair`.
- `XCB_apply`, `X0Lift_apply`, `uD_apply`.
- `parametrizeX0PlusU_mem`, `parametrizeX0PlusU_uniqueness`.
- `uD`, `uD_neg_inverse`, `uD_conj_XCB`.

(`parametrizeX0PlusU_existence` and `uD_isParabolic` are *not* in this
list — they are Tier D and remain `sorry`.)

#### Anti-patterns (do not retry — discovered in earlier rounds)

- `XCB_apply ... := rfl` — fails on multi-`let` definitions; the
  pre-existing `show ...; rfl` form is required.
- `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise — use
  `open Classical in if … then … else …` *inside* the def body.
- `omega` cannot see `S.E = S.paired.E` (abbrev boundary) — insert
  `change Module.finrank F S.paired.E + _ = _` first.
- `field_simp` leaves residual `1 + 1 = 2` for `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`
  — use `rw [← two_mul, mul_inv_cancel₀ hChar]` instead.

### Files NOT assigned this round

The following files have remaining sorries but are blocked. **Do not
assign provers to them this round.** Their objectives will be created
once the upstream refactors are scoped.

- `InducedOrbitToy/X0Geometry.lean` — `sDual_restrict_ker_isIso` blocked
  on `Basic.lean :: DualTransposeData` refactor.
- `InducedOrbitToy/Slice.lean` — `parametrizeX0PlusU_existence` blocked
  on `Basic.lean :: UnipotentRadical` refactor; `uD_isParabolic` blocked
  on autoformalization statement fix.
- `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion`
  depends on this round's Tier A NormalForm targets landing first.
- `InducedOrbitToy/LocalForms.lean` — done; no work.

## Reusable Gotchas (carry forward, augmented)

- `LinearMap.IsAdjointPair`, **not** `LinearMap.BilinForm.IsAdjointPair`.
- `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise.
- Trim `simp` argument lists; lints-as-errors reject unused simp args.
- `lean_diagnostic_messages` MCP needs absolute file paths.
- `[TopologicalSpace (Module.End F S.V)]` cannot be a file-level
  `variable` instance binder; thread it as an explicit hypothesis.
- `Submodule.linearProjOfIsCompl` is the right tool for `L1' ⊕ L0'`
  / `L1 ⊕ L0` decompositions.
- Term-mode `sorry`s must be replaced with a real construction before
  any downstream theorem about them can be discharged.
- Polymorphic typeclass over multi-universe structures: declare with
  explicit `class C.{u, v, w, x} ...`; `Type*` placeholders in class
  fields do not unify across uses (lesson from session 3 LocalForms).
- `change Module.finrank F S.paired.E + _ = _` to bridge `S.E ≡ S.paired.E`
  abbrev boundary before `omega`.
- Block-matrix `_apply` helpers: write the fully unfolded RHS in a
  `show` clause before `rfl` (multi-`let` defs aren't definitionally
  equal to their RHS without the `show`).
- `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`: `rw [← two_mul, mul_inv_cancel₀ hChar]`
  (do **not** `field_simp` — leaves residual `1 + 1 = 2`).
- `Ring.inverse` on `Module.End F V` is the right packaging for
  "best-effort inverse" in orbit predicates (no division-ring needed).

## Reporting

Each prover writes `.archon/task_results/<File>.md` with:
- which sorries were closed (line numbers + theorem names);
- exact Mathlib lemmas used;
- remaining subgoals and notable failed attempts (so the plan agent does
  not repeat dead ends);
- confirmation that the assigned file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`);
- confirmation that `lake build` is still green;
- confirmation that no `axiom` was introduced
  (`#print axioms` for each public theorem in the file).
