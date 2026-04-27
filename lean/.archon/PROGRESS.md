# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Latest review: `.archon/proof-journal/sessions/session_2/summary.md`
  and `.archon/proof-journal/sessions/session_2/recommendations.md`.

## Verified State (independent checks)

- `lake build` succeeds; only `sorry` warnings.
- Custom `axiom` declarations: 0 (verified by inspection of all 6 .lean files).
- `Basic.lean :: c_eq_finrank_quotient` is proved.
- `Orbits.lean :: multiplicityNonDeg` and `multiplicityOddCase` are proved
  from the abstract `MultiplicityTheory` package; the previous false
  `Multiplicity := 0` blocker is gone.
- Remaining actual `sorry` occurrences: 22.
  - `InducedOrbitToy/X0Geometry.lean`: 2  (lines 114, 154)
  - `InducedOrbitToy/Slice.lean`: 9       (lines 51, 58, 137, 146, 156, 169, 177, 187, 201)
  - `InducedOrbitToy/NormalForm.lean`: 5  (lines 155, 167, 187, 204, 213)
  - `InducedOrbitToy/LocalForms.lean`: 3  (lines 73, 88, 103)
  - `InducedOrbitToy/Orbits.lean`: 3      (lines 124, 137, 187)

## Prover Strategy

Prioritise local linear-algebra sorries before topology / orbit statements.
Keep the existing public theorem statements fixed; add `private` helper
lemmas inside the owning file as needed. Do not introduce `axiom`. Do not
edit any file other than the one assigned. Each prover should consult the
matching `.archon/informal/<file>.md` before drafting a strategy and emit
`.archon/task_results/<File>.md` on completion.

## Current Objectives

Five objectives, one per file. Each prover may add `private` helper lemmas
in its own file but must not touch others.

### 1. `InducedOrbitToy/X0Geometry.lean` — 2 sorries

Informal: `.archon/informal/` (no separate file; goal is rooted in this
module's docstring and the structure of already-proved lemmas).

Targets:
- `vplusKerPairing_isPerfPair` (line 111).
  Strategy:
  * Use `LinearMap.IsPerfPair.of_injective`.
  * **Left injectivity** (`vplusKerPairing` injective on `S.Vplus`): if
    `v ∈ S.Vplus` pairs to zero against every `x ∈ ker S.X0`, then
    `v ∈ S.formV0.orthogonal (LinearMap.ker S.X0)`. Use the already-proved
    `orthogonal_range_eq_ker` (combined with `S.epsSymm`-driven `IsRefl`)
    to deduce `v ∈ LinearMap.range S.X0`. Finish via
    `S.isCompl.disjoint`: `S.Vplus ⊓ LinearMap.range S.X0 = ⊥`.
  * **Right injectivity** (the flipped pairing injective on `ker S.X0`): if
    `x ∈ ker S.X0` pairs to zero against every `v ∈ S.Vplus`, decompose an
    arbitrary `y ∈ S.V0` through the complement (`S.isCompl.codisjoint` →
    `S.Vplus ⊔ LinearMap.range S.X0 = ⊤`); the `LinearMap.range S.X0`
    component pairs to zero against `x` by `ker_le_orthogonal_range`.
    Conclude using `hnondeg`.
- `sDual_restrict_ker_isIso` (line 142).
  Strategy:
  * `D.pairing_eq` together with `vplusKerPairing_isPerfPair` (above)
    determines `D.Tdual w` for `w ∈ ker S.X0` uniquely as a functional that
    pairs against `T (a' : L1')` via `S.formV0`. This places
    `D.Tdual w ∈ E` in the image of the perfect pairing `lambda`.
  * Via `hlambda` (`lambda.IsPerfPair`) and `hL1'` (`finrank L1' = c S`),
    construct the equivalence `(LinearMap.ker S.X0) ≃ₗ[F] L1` componentwise
    and check the pointwise identity.

Already proved in this file (do not redo):
`ker_le_orthogonal_range`, `orthogonal_range_eq_ker`,
`finrank_quotient_range_eq_finrank_ker`, `finrank_Vplus_eq_c`,
`VplusEquivQuotientRange`, `vplusKerPairing` (sorry-free def),
the aggregate `x0Geometry` (sorry-free; reduces to the two targets).

### 2. `InducedOrbitToy/Slice.lean` — 9 sorries

Informal: `.archon/informal/slice.md` (covers all 9 sorries, including
the `Cdual` and `uD` term-mode placeholders and the explicit
block-matrix formula for `uD`).

Order of attack (matches the informal doc's recommendations):
1. Replace `Cdual`'s term-mode `sorry` (line 51) using
   `S.paired.isPerfect : (S.paired.pairing).IsPerfPair`. Concretely the
   functional `e' ↦ - S.formV0 v (C e')` is in `Module.Dual F S.E'`; its
   inverse image under the perfect pairing's flip lives in `S.E`.
2. Prove `Cdual_pairing_eq` (line 58) — direct unfolding once `Cdual` is
   constructed.
3. Replace `uD`'s term-mode `sorry` (line 169) with the explicit
   block-matrix formula
   `(e + Cdual D v + ½ Cdual D (D e'), v + D e', e')`. Bring in
   `(2 : F) ≠ 0` as `Invertible (2 : F)` via `invertibleOfNonzero`.
4. Discharge the seven theorem sorries (`parametrizeX0PlusU_mem`,
   `_existence`, `_uniqueness`, `uD_neg_inverse`, `uD_isParabolic`,
   `uD_conj_XCB`) by `Prod`-API block-matrix calculation on
   `S.V = S.E × S.V0 × S.E'`. Use `LinearMap.fst/snd/inl/inr`,
   `Submodule.linearProjOfIsCompl` (with `S.isComplL'`),
   `LinearMap.ext_iff` for endomorphism equalities.

Reusable Mathlib hints from session 2: `LinearMap.IsAdjointPair` lives in
the bare `LinearMap` namespace, **not** `LinearMap.BilinForm.IsAdjointPair`.

### 3. `InducedOrbitToy/NormalForm.lean` — 5 sorries

Informal: `.archon/informal/normalform.md`.

Recommended order: kernel/image first (they are concrete `Submodule`
equalities on `S.V = S.E × S.V0 × S.E'`), then dimension, then the
classifying theorems.

1. `kernelImage_ker` (line 187): `LinearMap.ker (XST S Sₕ T) = kerXST_submod S Sₕ T`.
   Use `LinearMap.mem_ker`, the explicit `Prod` decomposition of `XST`, and
   `Submodule.prod_mem` / `Submodule.mem_map`.
2. `kernelImage_im` (line 204): symmetric, using
   `LinearMap.mem_range_iff` and `Submodule.sup_mem`.
3. `kernelImage_dim` (line 213): combine the two above with
   `Module.finrank_prod`, `Submodule.finrank_map_subtype`,
   `Submodule.finrank_quotient_add_finrank` (or
   `LinearMap.finrank_range_add_finrank_ker`), and `omega`.
4. `pNormalForm` (line 155) and `pNormalForm_residual_orbit_iso`
   (line 167): heavier blueprint material; defer until 1–3 are stable.
   These rely on `IsParabolicElement`, `Bilinear.AreIsometric` and the
   blueprint's normal-form construction. If progress on these stalls,
   extract sub-lemmas and surface them through `task_results` so the plan
   agent can re-decompose.

### 4. `InducedOrbitToy/LocalForms.lean` — 3 sorries

Informal: `.archon/informal/localforms.md`. The current
`ClassifyBilinearForms F` typeclass has a vacuous `∃ _ : ℕ, True` body —
**this is intentional** for autoformalize and is a soft blocker for
non-trivial proofs.

Path A (preferred for this iteration): enrich `ClassifyBilinearForms F`
inside this file so its content is strong enough to discharge
`localFormClasses_finite` (`∃ Finset of representatives`) and
`localFormClasses_open`. The natural enrichment is to require:
* a finite set of `Bilinear.AreIsometric` representatives for non-degenerate
  ε-symmetric forms on `S.L0'`-shaped modules, and
* a "locally constant" property of the classifying invariants under
  `[TopologicalSpace _] [ContinuousAdd _]`.

Keep the public theorem names stable. Do **not** introduce concrete
instances for `ℝ` / non-archimedean locals — that is out of scope.

If enriching the typeclass turns out to break downstream files, fall back
to writing a `private` strengthened typeclass and use the existing
`ClassifyBilinearForms` as a shim.

### 5. `InducedOrbitToy/Orbits.lean` — 3 sorries

Informal: `.archon/informal/orbits.md`. `multiplicityNonDeg` and
`multiplicityOddCase` are already proved via `MultiplicityTheory`.

Targets:
1. `inducedOrbits` (line 118).  This is the *containment* form
   `GOrbit S (XST S Sₕ T) ⊆ IndPG S` — **do not weaken further and do not
   try to lift to the maximal-orbit classification** (that is polish-stage
   work). Strategy: `IndPG` is `closure (G · (O₀ + 𝔲))`, so any `g · XST`
   is in `G · (O₀ + 𝔲)` once `XST - X0Lift ∈ UnipotentRadical`; reuse
   `parametrizeX0PlusU_mem` from `Slice.lean` (will be available after
   objective 2 lands; if Slice is still pending, pull just the statement
   and apply via `parametrizeX0PlusU_mem` as an external hypothesis).
2. `sIndependenceAndOrbitCriterion` (line 128). Both directions:
   - `→`: if `g ∈ G` conjugates `XST Sₕ₁ T₁` to `XST Sₕ₂ T₂`, then `g`
     is a `P`-element (preserves `flagE`) and the residual block is an
     isometry between `BT T₁` and `BT T₂`.
   - `←`: build a conjugating `g ∈ G` from any
     `Bilinear.AreIsometric (BT T₁) (BT T₂)` witness.
   `pNormalForm_residual_orbit_iso` from `NormalForm.lean` is the
   needed bridge.
3. `main` (line 171). Quadruple conjunction; discharge each conjunct via
   the previous lemmas.

Do **not** revert the `MultiplicityTheory` refactor.

## Reusable Gotchas (carry forward)

- `LinearMap.IsAdjointPair`, **not** `LinearMap.BilinForm.IsAdjointPair`.
- `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise — use
  `open Classical in if … then … else …` *inside* the def body, or
  `haveI : Decidable _ := Classical.dec _`.
- Trim `simp` argument lists; lints-as-errors reject unused simp args.
- `lean_diagnostic_messages` MCP needs absolute file paths.
- `[TopologicalSpace (Module.End F S.V)]` cannot be a file-level
  `variable` instance binder; thread it as an explicit hypothesis on each
  theorem that needs it.
- `Submodule.linearProjOfIsCompl` is the right tool for the `L1' ⊕ L0'`
  / `L1 ⊕ L0` decompositions.
- Term-mode `sorry`s (e.g. `Cdual`, `uD`) must be replaced with a real
  construction before any downstream theorem about them can be discharged.

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
