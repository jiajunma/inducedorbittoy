# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 6)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- **NEW Round 6 informal sketch:** `.archon/informal/levi.md` — Levi
  machinery additive plan for `Slice.lean`.
- Latest reviews: `.archon/proof-journal/sessions/session_7/summary.md`
  and `.archon/proof-journal/sessions/session_7/recommendations.md`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, 2026-04-28 — end of Round 5)

- `lake build` succeeds; only `sorry` warnings + 1 unused-variable lint
  (`InducedOrbitToy/X0Geometry.lean:221:35: unused variable hlambda` —
  pre-existing, do not remove; the hypothesis is part of the
  autoformalised statement of `sDual_restrict_ker_isIso`).
- Custom `axiom` declarations: 0. `#print axioms` on every sorry-free
  public theorem returns only `[propext, Classical.choice, Quot.sound]`.
- Round-5 progress: 6 → 4 declaration-use `sorry` warnings.
  - **`NormalForm.lean :: kernelImage_ker` is sorry-free** (Tier S #4
    landed; `Sₕ : S.L1' ≃ₗ[F] S.Vplus`).
  - **`NormalForm.lean :: kernelImage_im` is sorry-free.**
  - 3 new private helpers added to `NormalForm.lean`: `Cdual_CST_mem_L1`,
    `kernelImage_DTD`, `lambda_isPerfPair_local`.
- Remaining declaration-use `sorry` lines (verified by `lake build`):
  - `InducedOrbitToy/NormalForm.lean`: 3
    - line 195 — `pNormalForm_witnesses` (Tier A, **Round 7**),
    - line 319 — `residual_levi_extract` (Tier A, **Round 7**),
    - line 348 — `residual_levi_build` (Tier A, **Round 7**).
  - `InducedOrbitToy/Orbits.lean`: 1
    - line 324 — `sIndependenceAndOrbitCriterion` (Tier A deferred,
      depends on `pNormalForm_residual_orbit_iso` fully closing;
      **Round 8**).

## Round Plan (revised after Round 5)

The 4 remaining sorries split into one infrastructure round (Round 6,
adding Levi machinery to `Slice.lean`), one closure round (Round 7,
closing the three NormalForm sorries), and one deferred Tier A round
(Round 8, closing `sIndependenceAndOrbitCriterion`).

| Round | Focus | Files | Sorry Δ |
|---|---|---|---|
| **6 (this round)** | **Add Levi machinery (additive) to `Slice.lean`** | Slice | 4 → 4 (additive) |
| 7 | Close `pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build` | NormalForm | 4 → 1 |
| 8 | Close `sIndependenceAndOrbitCriterion` | Orbits | 1 → 0 |

**Round 6 is single-file** (Slice.lean only) and **does not change the
sorry count** — it adds new infrastructure that Round 7 will consume.
This is a deliberate one-round delay relative to the review's two-file
recommendation: the Levi machinery is novel, complex, and the
NormalForm consumer would race against an unfinalised Slice contract.
By splitting, Round 7's prover sees the finalised Slice API and writes
proofs against concrete signatures.

## Current Objectives (Round 6)

**One objective.** All other files are blocked on Round 7+ work or are
already complete; **do not assign provers to them this round**.

### 1. `InducedOrbitToy/Slice.lean` — Add Levi-action machinery (additive)

**Reference:** `.archon/informal/levi.md` (the full informal sketch with
exact Lean signatures Round 7 will consume).

**Reference (blueprint):** `references/blueprint_verified.md` lines
200–319 (`prop:p-normal-form` proof, where the Levi factor is described
on lines 201–205, 266–278, and 305–311).

**Reference (project files):**
- `Slice.lean` lines 38–679 — existing API. Levi machinery appends
  cleanly after the existing `uD_conj_XCB` (around line 564).
- `Basic.lean` — `IsParabolicElement`, `UnipotentRadical`, `S.flagE`,
  `S.flagEV0`, `S.ambientForm`.
- `X0Geometry.lean` — `vplusKerPairing_isPerfPair`,
  `sDual_restrict_ker_isIso`, `DualTransposeData`.

**Concrete deliverables (use the exact signatures in `levi.md`):**

1. **`lambdaDualE`** + `lambdaDualE_pairing_eq` + `lambdaDualE_id` +
   `lambdaDualE_comp` — the dual transpose `g^∨ : S.E →ₗ[F] S.E` for
   `g : S.E' →ₗ[F] S.E'`, defined via `S.lambda` perfect pairing.
2. **`leviGL_E`** + `leviGL_E_apply` + `leviGL_E_symm_inverse` — the
   `GL(E')` Levi block, `((d⁻¹)^∨, id_{V0}, d)` on `S.V`.
3. **`leviGL_V0`** + `leviGL_V0_apply` + `leviGL_V0_symm_inverse` — the
   `G_0` Levi block, `(id_E, g, id_{E'})` on `S.V`. **Definition does
   NOT depend on `g` being an isometry**; only the parabolicity proof
   does.
4. **`leviGL_E_isParabolic`** — `IsParabolicElement S (leviGL_E S d)`.
5. **`leviGL_V0_isParabolic`** — same for `leviGL_V0` with the extra
   isometry hypothesis `(hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v)`.
6. **`leviGL_E_conj_XCB`** — block formula
   `leviGL_E d ∘ XCB(C, B) = XCB(C ∘ d⁻¹, (d⁻¹)^∨ ∘ B ∘ d⁻¹) ∘ leviGL_E d`.
7. **`leviGL_V0_conj_XCB`** — block formula on the `V0`-side. (May
   require `g` commuting with `S.X0`; see `levi.md` §6.5 for the
   discussion. The prover may state this conditionally on `g = id` or
   on the commutator hypothesis, whichever is cleanest.)
8. **`parabolic_decompose`** — every `IsParabolicElement S p` factors
   as `p = uD D ∘ leviGL_E d ∘ leviGL_V0 g`. **This is the hardest
   piece.** If intractable in one round, the prover may leave it as a
   `sorry` with a one-line gap explanation; Round 7 will close it.

**Acceptance criteria:**

- `lake env lean InducedOrbitToy/Slice.lean` compiles.
- Helpers 1–7 (`lambdaDualE` through `leviGL_V0_conj_XCB`) are all
  sorry-free.
- Helper 8 (`parabolic_decompose`) may carry a `sorry` IF the prover
  documents the gap in a `/- ... -/` comment block above the theorem.
- `lake build` remains green. **The 4 declaration-use `sorry`s from end
  of Round 5 must be unchanged in count and location** (3 in
  `NormalForm.lean` lines 195/319/348, 1 in `Orbits.lean` line 324).
  Acceptable if `parabolic_decompose` adds one **additional** `sorry`,
  yielding 5 declaration-use warnings — but no other sorry count change.
- `#print axioms` on every newly-closed declaration shows only
  `[propext, Classical.choice, Quot.sound]`.
- All existing `Slice.lean` declarations are unchanged. The Levi
  machinery is a strictly additive append after `uD_conj_XCB`.

**Informal proof outlines:** see `.archon/informal/levi.md`. Each
declaration there has a `-- Hint:` comment pointing at the right
Mathlib API to use.

**Stop conditions for the Round-6 prover:**
- If `lambdaDualE_pairing_eq` proves intractable: the dual transpose is
  defined via `S.paired.isPerfect`, which exposes
  `LinearMap.IsPerfPair.symm_apply` and `apply_symm_toPerfPair_self` —
  the same pattern that built `Cdual` in `Slice.lean` lines 71–95.
  Mirror that construction.
- If `parabolic_decompose` proves intractable: stop and report. Do
  NOT spend more than ~30% of the round budget on it; helpers 1–7 are
  the priority.
- If `lake build` breaks: revert and re-attempt smaller pieces. The
  Levi machinery is purely additive, so a `git diff` should show only
  appended lines after `uD_conj_XCB`.

### Files NOT assigned this round

The following files have remaining sorries but are blocked on Round 7+
work, or are already complete. **Do not assign provers to them this
round.** If the harness dispatches a prover anyway, the prover should:
- verify the file compiles in isolation (`lake env lean
  InducedOrbitToy/<File>.lean`),
- write a brief "no work" `task_results/<File>.md`, and
- **not edit anything**.

- `InducedOrbitToy/Basic.lean` — already done; no work.
- `InducedOrbitToy/X0Geometry.lean` — already done (session 4); no work.
- `InducedOrbitToy/LocalForms.lean` — already done; no work.
- `InducedOrbitToy/NormalForm.lean` — 3 sorries deferred to Round 7. Do
  NOT edit this file in Round 6 (the proofs depend on `Slice.lean`'s
  Levi machinery being finalised first).
- `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion` is
  Round 8 (needs `pNormalForm_residual_orbit_iso` fully closed via
  Round 7's NormalForm work).

## Coordination notes for Round 6 (parallel-safety)

Round 6 is **single-file** (Slice.lean only). Adding ~150 additive lines
at the end of one file. No cross-file cascade.

There is no parallel race this round; provers dispatched to other files
should write "no work" reports immediately.

## Reusable Gotchas (carry forward, augmented)

- `LinearMap.IsAdjointPair`, **not** `LinearMap.BilinForm.IsAdjointPair`.
- `LinearMap.IsOrthogonal B g` unfolds to `∀ x y, B (g x) (g y) = B x y`.
- `IsSkewAdjoint B X` (project-local) unfolds to
  `∀ x y, B (X x) y + B x (X y) = 0`.
- `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise; use
  `open Classical in if … then … else …` inside `def` bodies.
- Trim `simp` argument lists; lints-as-errors reject unused simp args.
- `lean_diagnostic_messages` MCP needs absolute file paths.
- `[TopologicalSpace (Module.End F S.V)]` cannot be a file-level
  `variable` instance binder; thread it as an explicit hypothesis.
- `Submodule.linearProjOfIsCompl` is the right tool for `L1' ⊕ L0'` /
  `L1 ⊕ L0` decompositions.
- Term-mode `sorry`s must be replaced with a real construction before
  any downstream theorem about them can be discharged.
- Polymorphic typeclass over multi-universe structures: declare with
  explicit `class C.{u, v, w, x} ...`; `Type*` placeholders in class
  fields do not unify across uses.
- `change Module.finrank F S.paired.E + _ = _` to bridge `S.E ≡ S.paired.E`
  abbrev boundary before `omega`.
- Block-matrix `_apply` helpers: write the fully unfolded RHS in a
  `show` clause before `rfl` (multi-`let` defs aren't definitionally
  equal to their RHS without the `show`).
- `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`: `rw [← two_mul, mul_inv_cancel₀ hChar]`
  (do **not** `field_simp` — leaves residual `1 + 1 = 2`).
- `Ring.inverse` on `Module.End F V` is the right packaging for
  "best-effort inverse" in orbit predicates (no division-ring needed).
- `Units.mkOfMulEqOne` for `IsUnit` from one-sided inverse on
  `Module.End F V` (finite-dim V):
  `(Units.mkOfMulEqOne _ _ h).isUnit`. Replaces the deprecated
  `LinearMap.mul_eq_one_of_mul_eq_one`.
- `obtain ⟨a, b, c⟩ := <existential>` makes destructured fields opaque
  — fix by packaging the equation directly in helper's conclusion
  (avoid the existential wrapper).
- Verify structure location via `grep` before scoping a refactor.
- **(session 5) Adjoint-pair → orthogonal via paired inverse:**
  given `IsAdjointPair B B f g` and `g ∘ f = id`, conclude
  `IsOrthogonal B f` via `intro u v; calc B (f u) (f v) = B u (g (f v))
  := hAdj u (f v) _ = B u v := by rw [hinv_apply]`.
- **(session 5) Cross-file proof structure validation via
  `lean_run_code`:** when a proof depends on a sister-prover's signature
  change not yet landed, validate the local proof shape with hypothetical
  inputs of the correct shape via a standalone `example`. Eliminates
  uncertainty during the parallel race.
- **(session 5) Bilinear-form identities via block-decomposition +
  `linear_combination`:** for an identity in `S.ambientForm`, destruct
  vectors as `(e, v, e')`, apply `*_apply` lemmas, use the standard
  `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, …]` set,
  apply pairing-eq lemmas to all `λ(F ·, ·)` atoms, then close with
  `linear_combination` using ε-symmetry-derived hypotheses (`hε`, `hε2`,
  point-specific instantiations).
- **(Round 4) `IsSkewAdjoint` closure proofs over generic `[Field F]`:**
  use `linear_combination hf + hg` (add) / `linear_combination c * hf`
  (smul). **Do not use `linarith`** — it requires `LinearOrderedField`
  and fails over generic `Field`.
- **(Round 4) `Submodule.IsCompl.projection_add_projection_eq_self`**
  (not `linearProjOfIsCompl_add_…`, which leansearch suggests but
  **does not exist** in current Mathlib) combined with
  `Submodule.IsCompl.projection_apply` to bridge between the
  `IsCompl.projection` and `linearProjOfIsCompl`-coerced-subtype forms.
- **(Round 4) `conv_lhs => rw [...]`** to scope a rewrite to the LHS
  only when bare `rw [← h]` would over-rewrite (e.g. rewriting `v` while
  `projL0' v` appears as a sub-expression on the RHS).
- **(Round 4) Cross-file 4-tuple cascade:** when a structure or
  predicate gains a new conjunct, every `obtain ⟨...⟩` and `refine
  ⟨..., ?_⟩` site that constructs/destructs the value needs a parallel
  arity bump.
- **(NEW Round 5) `linear_combination` is scalar-only over generic
  Modules.** It synthesises `CommSemiring`/`CommRing` on the *target*
  type. `S.E` is `AddCommGroup F + Module F`, not a `CommRing`. Vector
  identities over modules cannot be discharged with `linear_combination`;
  only **scalar** identities qualify. For module identities, drop to
  `rw` chains + `abel`. Refines the Round-4 "`linear_combination` over
  generic Field" boundary.
- **(NEW Round 5) Subtype-wrapping anti-pattern for `Iso + Property`:**
  packaging `{φ : … // ∀ w, …}` inside a helper `def` fails when the
  proof needs `cases` on `IsCompl.codisjoint` (Prop-eliminator
  restriction). Inline the `obtain` at each Prop-conclusion call site.
- **(NEW Round 5) Drop explicit `LinearMap` coercion in `rw` arguments**
  once the callee accepts `LinearEquiv` — Lean auto-inserts; explicit
  coercion causes `Application type mismatch`.
- **(NEW Round 5) `lean_leansearch` natural-language >> `lean_loogle`
  patterns** for projection / `IsCompl.projection_*` API discovery.
  When `lean_loogle` returns `No results found`, try natural-language
  prose queries on `lean_leansearch`. Always verify via `lean_run_code`
  `#check` or `lean_multi_attempt` before relying on a name.
- **(NEW Round 5) `let w := ⟨v, hv⟩` impedes `simpa` reduction.** Use
  the inline anonymous-constructor term directly + `congrArg (fun w =>
  (w : S.V0))` + `simpa`.
- **(NEW Round 5) `#print axioms` via `Bash` + `/tmp/check_axioms.lean`:**
  promotes to a standard prover closure-check pattern when `lean_verify`
  is unavailable. Build a one-off `.lean` file that imports the project
  module and `#print axioms` each newly closed theorem.

## Reporting

Each prover writes `.archon/task_results/<File>.md` with:
- which sorries were closed (line numbers + theorem names);
- which definitions / theorems were *added* (Round 6 is purely additive,
  so this section will be the bulk of the Slice prover's report);
- exact Mathlib lemmas used;
- any helper that was punted as `sorry` with a one-line gap explanation;
- confirmation that the assigned file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`);
- confirmation that `lake build` is green at end of round;
- confirmation that no `axiom` was introduced
  (`#print axioms` for each newly-closed theorem in the file).
