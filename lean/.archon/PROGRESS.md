# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 8)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Round 6 informal sketch: `.archon/informal/levi.md` — Levi machinery
  for `Slice.lean`. Includes § 6.6 sketch for `parabolic_decompose`.
- Round 7 informal sketch: `.archon/informal/normalform_round7.md` —
  full proof outline for `pNormalForm_witnesses` (Tier A #1) plus the
  two `residual_levi_*` helpers.
- Latest review: `.archon/proof-journal/sessions/session_9/summary.md`
  and `.archon/proof-journal/sessions/session_9/recommendations.md`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, end of Round 7)

- `lake build` succeeds; only `sorry` warnings + 1 unused-variable lint
  (`InducedOrbitToy/X0Geometry.lean:221:35: unused variable hlambda` —
  pre-existing, do not remove; the hypothesis is part of the
  autoformalised statement of `sDual_restrict_ker_isIso`).
- Custom `axiom` declarations: 0. `#print axioms` on every sorry-free
  public theorem returns only `[propext, Classical.choice, Quot.sound]`.
- Round-7 progress: 5 → 3 declaration-use `sorry` warnings.
  - `residual_levi_extract` (NormalForm) closed sorry-free.
  - `residual_levi_build` (NormalForm) closed sorry-free.
  - `pNormalForm_residual_orbit_iso` (public consumer) sorry-free.
  - Tier S #5 signature restructure landed (Sₕ : L1' ≃ₗ Vplus,
    Levi factor `d` exposed in `pNormalForm_witnesses`).
- Remaining declaration-use `sorry` lines (verified by
  `lake build` 2026-04-28):
  - `InducedOrbitToy/NormalForm.lean:203` — `pNormalForm_witnesses`
    (single isolated body sorry at line 216; declaration line 203).
    **Round 8 primary.**
  - `InducedOrbitToy/Slice.lean:1078` — `parabolic_decompose`
    (deferred from Round 6, Gap comment at lines 1062–1077).
    **Round 8 tertiary (parallel, optional).**
  - `InducedOrbitToy/Orbits.lean:324` — `sIndependenceAndOrbitCriterion`
    (two scoped sorries at body lines 358 + 376).
    **Round 8 secondary.**

## Round Plan

| Round | Focus | Files | Sorry Δ |
|---|---|---|---|
| 6 (done) | Add Levi machinery to `Slice.lean` | Slice | 4 → 5 (additive) |
| 7 (done) | Close `residual_levi_extract`, `residual_levi_build`, restructure `pNormalForm_witnesses` signature | NormalForm | 5 → 3 |
| **8 (this round)** | **Close `pNormalForm_witnesses` body + `sIndependenceAndOrbitCriterion` (+ optional `parabolic_decompose`)** | NormalForm + Orbits + Slice (parallel) | **3 → 0 (target)** |

If Round 8 closes all 3 declaration-use sorries, the project advances
from `prover` to `polish`. If only 2 of 3 close (most likely:
`pNormalForm_witnesses` and `sIndependenceAndOrbitCriterion` close,
`parabolic_decompose` is left for a Round 9 cleanup), the project still
advances on the **public-theorem** axis: every public theorem will be
sorry-free. `parabolic_decompose` carries its `sorry` purely for an
internal helper and does not block any downstream consumer (Round 7
sidestepped it via Option B in `residual_levi_*`).

## Current Objectives (Round 8)

**Three independent files, three independent objectives, dispatched
in parallel.** No cross-file edit overlap; harness runs them
concurrently.

### 1. `InducedOrbitToy/NormalForm.lean` — close `pNormalForm_witnesses` body (line 216)

**Reference:** in-file docstring at lines 175–202; full informal
proof outline at `.archon/informal/normalform_round7.md` § Tier A #1;
session 9 recommendations at
`.archon/proof-journal/sessions/session_9/recommendations.md` § Option A.

**Reference (blueprint):** `references/blueprint_verified.md` lines
200–264 — the `prop:p-normal-form` proof.

**Reference (project files):**
- `Slice.lean` Round 6 Levi machinery: `lambdaDualE`,
  `lambdaDualE_pairing_eq`, `leviGL_E`, `leviGL_E_apply`,
  `leviGL_E_isParabolic`, `leviGL_E_conj_XCB`,
  `leviGL_E_symm_inverse`. All sorry-free; APIs stable.
- `Slice.lean` unipotent half: `parametrizeX0PlusU_existence`,
  `parametrizeX0PlusU_uniqueness`, `uD`, `uD_apply`, `uD_neg_inverse`,
  `uD_conj_XCB`, `uD_isParabolic`. All sorry-free.
- `NormalForm.lean` already-landed Round 7 helpers: `XST_apply`,
  `extendL0'IsoToE'` (private), and the `kernelImage_*` API.
- `X0Geometry.lean`: `vplusKerPairing_isPerfPair`,
  `sDual_restrict_ker_isIso`.

**Concrete deliverable:** close the single `sorry` at body line 216.
The body docstring at lines 188–202 outlines a four-step plan:

1. **Build `(Sₕ, d)` from `_hRank : rank Cbar = c`.** Use
   `LinearEquiv.ofBijective` on a `LinearMap.codRestrict` of
   `Cbar S C` to its image, then dim-match against
   `Module.finrank F S.Vplus` via `_hRank` and the `c` accountancy
   in `X0Setup`. Lift the resulting `L0' ≃ ker (Cbar S C)` to
   `d : E' ≃ E'` extending by `id` on L1' — same
   `Submodule.prodEquivOfIsCompl` pattern as Round 7's
   `extendL0'IsoToE'`.
2. **Apply `leviGL_E_conj_XCB`.** Sets the LHS to
   `XCB(C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm) ∘ leviGL_E d`.
   The C-block of `C ∘ d.symm` now has `ker = L0'` and the L1'
   restriction is `mkQ ∘ Sₕ`.
3. **Build `D` so `X0 ∘ D = C' - CST Sₕ`.** Note `C' - CST Sₕ`
   lands in `range X0` because the L0' part of `C'` is zero
   (Step 1 construction) and the L1' part equals `CST Sₕ` by
   definition of `Sₕ`. Use `S.isCompl : Vplus ⊕ range X0 = V0`
   plus surjectivity of `X0` onto its range to extract `D`. `T`
   reads off the `B`-block residual after the unipotent
   normalisation.
4. **Combine via `uD_conj_XCB` + `parametrizeX0PlusU_uniqueness`
   + `uD_neg_inverse`.** `parametrizeX0PlusU_uniqueness` identifies
   the resulting `(C'', B'')` with `(CST Sₕ, BST T)`.

**Stop conditions:**
- If Step 1 (the d-construction) proves intractable due to
  `Module.finrank` plumbing, extract Step 1 as a separate
  `private def` skeleton with its own `sorry`, then close
  Steps 2–4 against the opaque `(Sₕ, d)`. The sorry localises
  to a smaller, more tractable piece for Round 9.
- If `lake build` breaks: revert and re-attempt smaller pieces.
  `pNormalForm_witnesses` is private; only its body may change.
  Do NOT modify the signature (the Tier S #5 restructure landed
  in Round 7).
- Estimated effort: ~150 lines.

**Acceptance criteria:**
- `lake env lean InducedOrbitToy/NormalForm.lean` compiles.
- The `sorry` at body line 216 is replaced by a real proof.
  Acceptable to introduce one isolated helper `private def`
  with its own sorry if Step 1 (d-construction) is intractable;
  in that case the helper sorry must be documented with a
  `Gap:` comment block.
- `lake build` is green at end of round.
- `#print axioms pNormalForm_witnesses` shows only
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`),
  unless the prover punted on Step 1 with a documented helper
  sorry.
- `#print axioms pNormalForm` then also shows clean axioms
  (the body is already sorry-free; only the transitive
  dependence on `pNormalForm_witnesses` brought in `sorryAx`).
- Stale comment hygiene: refresh lines 344, 357 if they still
  reference the removed `L0_isotropic` field (Round 6 carry-forward).

### 2. `InducedOrbitToy/Orbits.lean` — close `sIndependenceAndOrbitCriterion` (line 324)

**Reference:** session 9 recommendations
(`.archon/proof-journal/sessions/session_9/recommendations.md`
§ Option B "Orbits prover's plan"); session 8 task report's "Next
session note" (archived under
`.archon/task_results/processed/round6/Orbits.lean.md`).

**Reference (project files):**
- `NormalForm.lean :: pNormalForm_residual_orbit_iso` — sorry-free
  public theorem (Round 7). Returns
  `IsParabolicElement S p ∧ p ∘ₗ XST T₁ = XST T₂ ∘ₗ p ↔ IsometryRel S T₁ T₂`
  conjugation/isometry equivalence. Now usable as a black box.
- `Basic.lean :: IsParabolicElement`, `IsometryEnd`, `GOrbit`,
  `IndPG`, `Tset_circ`, `IsometryRel`, `BT`, `XST`.
- `Slice.lean :: parabolic_decompose` (still sorry'd, but the
  *statement* is callable; if Objective 3 lands in parallel its
  proof becomes available).

**Concrete deliverables:** close both scoped sorries.

**Reverse direction (line 376) — direct, do this first:**
1. `unfold IsometryRel Bilinear.AreIsometric at hiso` already
   landed (Round 4). Have `_h : L0' ≃ₗ L0'` and
   `_h_isom : ∀ u v, BT T₂ (_h u) (_h v) = BT T₁ u v`.
2. Apply `pNormalForm_residual_orbit_iso` (or its appropriate
   half) to lift `_h` to a P-element `p` with
   `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p`. Need `Sₕ₁ = Sₕ₂` to do this
   directly; see Hypothesis additions below.
3. Use parabolic ⊂ isometry group: `IsParabolicElement → IsometryEnd`
   (extract from `IsParabolicElement`'s 4th conjunct
   `IsOrthogonal S.ambientForm p`, which is exactly `IsometryEnd`).
4. Mutual inclusion of orbits via `p ∈ G` membership-witnessing.

**Forward direction (line 358) — harder, do this second:**
1. Have `_g : Module.End F S.V`, `_hg : IsometryEnd S _g`,
   `_hyeq : XST S Sₕ₁ T₁ = _g ∘ₗ XST S Sₕ₂ T₂ ∘ₗ Ring.inverse _g`
   (already extracted via `obtain` in Round 4).
2. Need `_g ∈ P` (i.e. `IsParabolicElement S _g`). Two routes:
   - **Route A — use `parabolic_decompose`:** if Objective 3 (Slice
     prover) lands `parabolic_decompose` in parallel, applying it
     to `_g` (after upgrading `IsometryEnd` to `IsParabolicElement`
     via slice-stability) yields the decomposition directly. **But
     parabolic_decompose itself takes `IsParabolicElement` as input,
     not `IsometryEnd`** — so this route still needs the
     slice-stability step.
   - **Route B (preferred for round-8 independence):** direct
     flag-stability argument from `_hg` + `_hyeq`. The conjugation
     equation forces `_g` to preserve flagE and flagEV0 (since
     `XST` does, and `_hg` is an isometry, and the conjugation
     equation translates the flag conditions). With
     `Nondegenerate` and `(2 : F) ≠ 0`, this can be proved
     directly without invoking `parabolic_decompose`.
3. Apply `pNormalForm_residual_orbit_iso` (forward half) to extract
   the bilinear isometry `h : L0' ≃ L0'` matching `BT T₁` and
   `BT T₂`, repackage as `IsometryRel S T₁ T₂`.

**Hypothesis additions.** Both directions need extra hypotheses:
- `S.formV0.Nondegenerate`,
- `(2 : F) ≠ 0`,
- `Sₕ₁ = Sₕ₂` (or equivalently, replace the two distinct `Sₕ₁`,
  `Sₕ₂` in the statement with a single `Sₕ`).

**Recommended approach (option (b) per session-9 review):**
strengthen `pNormalForm_residual_orbit_iso` to absorb the
`Nondegenerate` and `(2 : F) ≠ 0` hypotheses, keeping
`sIndependenceAndOrbitCriterion`'s public statement clean. Note
that this is a NormalForm.lean signature change, which means the
Orbits prover should NOT edit NormalForm.lean (file-ownership rule).
Instead:
- Option (a): add hypotheses to `sIndependenceAndOrbitCriterion`
  directly. Cleaner for Round 8 (no cross-file race with the
  NormalForm prover); slightly less clean public API. **Take
  option (a).**
- The downstream `main` theorem in `Orbits.lean` calls
  `sIndependenceAndOrbitCriterion`; thread the new hypotheses
  through there as well (`main` already takes
  `hNondeg : S.formV0.Nondegenerate` and
  `_hChar : (2 : F) ≠ 0` — those are reusable).
- For the `Sₕ₁ = Sₕ₂` issue, Round 8 may either (i) restrict the
  statement to a single `Sₕ` parameter (cleaner, breaks API
  symmetry with two separate `Sₕ`s), or (ii) keep two `Sₕ`s but
  add `Sₕ₁ = Sₕ₂` as an explicit hypothesis. **Option (i)
  preferred** — replace `Sₕ₁ Sₕ₂ : S.L1' ≃ₗ[F] S.Vplus` with a
  single `Sₕ : S.L1' ≃ₗ[F] S.Vplus`, since the blueprint argument
  uses a single `Sₕ` anyway.

**Stop conditions:**
- If the forward direction (Route B) proves intractable — i.e.
  the slice-stability argument requires significant new
  infrastructure — reduce it to a separate `private lemma
  isParabolic_of_isometry_conj` with its own sorry. The Round 8
  delivers reverse direction sorry-free + forward direction
  reduced to the skeleton.
- Estimated effort: ~80 lines (forward + reverse combined).

**Acceptance criteria:**
- `lake env lean InducedOrbitToy/Orbits.lean` compiles.
- Both scoped sorries (lines 358, 376) replaced. If forward
  direction punted, the surviving sorry is in a private helper,
  not in `sIndependenceAndOrbitCriterion`'s body.
- `lake build` is green at end of round.
- `#print axioms sIndependenceAndOrbitCriterion` shows only
  `[propext, Classical.choice, Quot.sound]` (or transitive
  `sorryAx` if a private helper still carries a sorry).
- `main` in Orbits.lean compiles after the
  `sIndependenceAndOrbitCriterion` signature update (any new
  hypotheses are threaded through).
- Stale comment refresh: line 357 reference to `L0_isotropic`,
  if any (carry-forward).

### 3. `InducedOrbitToy/Slice.lean` — close `parabolic_decompose` (line 1078, OPTIONAL)

**Reference:** Gap comment block in-file at lines 1062–1077;
`.archon/informal/levi.md` § 6.6.

**Reference (project files):**
- `Slice.lean` Round 6 Levi machinery: all sorry-free in scope.
- `Slice.lean :: parametrizeX0PlusU_existence`,
  `parametrizeX0PlusU_uniqueness` — used in Step C.
- `X0Geometry.lean :: vplusKerPairing_isPerfPair` — used in Step B.

**Concrete deliverable:** close the single `sorry` at line 1089
(declaration line 1078).

**Three substantive sub-constructions per `informal/levi.md` §6.6:**
1. **Step A (g₀ extraction):** action of `p` on the quotient
   `flagEV0 / flagE ≃ V0`. Since `p` preserves both `flagE` and
   `flagEV0`, it descends to a quotient automorphism, which —
   under the canonical iso `flagEV0/flagE ≃ V0` — yields
   `g₀ : V0 ≃ V0`. Need to verify `g₀` commutes with `S.X0` (or
   equivalently is a `formV0`-isometry under the
   `vplusKerPairing` perfect pairing).
2. **Step B (`(d⁻¹)^∨` extraction):** action of `p` on
   `flagE = E`. Restricting `p` to `flagE` (a 1-dim'l submodule
   isomorphic to `E`) gives `pE : E ≃ E`. Take its inverse-dual
   `d := lambdaDualE pE.symm` interpreted on `E'`.
3. **Step C (residual D):** apply
   `parametrizeX0PlusU_uniqueness` to
   `p ∘ leviGL_E d.symm ∘ leviGL_V0 g₀.symm`. The resulting
   element fixes both `flagE` and `flagEV0` *with the identity
   action on quotients*, so it factors through `uD D` for some
   `D : E' →ₗ V0` by `parametrizeX0PlusU_uniqueness`.

**Stop conditions:**
- This objective is **OPTIONAL** for Round 8. Round 7 sidestepped
  `parabolic_decompose` via Option B (direct construction in
  `residual_levi_extract` / `residual_levi_build`), and the
  Orbits prover (Objective 2) has Route B as its primary plan,
  also independent of `parabolic_decompose`.
- If `parabolic_decompose` proves intractable in one round (which
  is plausible — Round 6 already deferred it once), the prover
  may stop and report. The `sorry` stays. Round 9 (or polish stage)
  picks it up.
- The prover should NOT spend more than ~50% of the round budget
  on this objective if it stalls; redirect to verifying the rest
  of `Slice.lean` compiles cleanly and reporting progress.
- Estimated effort: ~85 lines if all three steps land cleanly.

**Acceptance criteria (if the prover attempts to close):**
- `lake env lean InducedOrbitToy/Slice.lean` compiles.
- The `sorry` at line 1089 is replaced by a real proof.
- `lake build` is green at end of round.
- `#print axioms parabolic_decompose` shows only
  `[propext, Classical.choice, Quot.sound]`.
- All existing Slice.lean declarations through line 1077 are
  byte-for-byte unchanged (the proof is body-only).

**Acceptance criteria (if the prover does NOT attempt or fails):**
- `lake build` remains green; no regressions.
- A "no work" or "attempted but stalled" report is filed in
  task_results/InducedOrbitToy_Slice.lean.md with a brief note on
  what was tried.

### Files NOT assigned this round

The following files have no remaining sorries and are blocked from
edits this round.  If the harness dispatches a prover anyway, the
prover should:
- verify the file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`),
- write a brief "no work" `task_results/<File>.md`, and
- **not edit anything**.

- `InducedOrbitToy/Basic.lean` — already done; no sorries.
- `InducedOrbitToy/X0Geometry.lean` — already done (session 4);
  no sorries. Pre-existing `unused variable hlambda` lint at
  line 221 must be left intact (part of the autoformalised
  signature).
- `InducedOrbitToy/LocalForms.lean` — already done; no sorries.

## Coordination notes for Round 8 (parallel-safety)

- **Three files edited simultaneously.** No source-level overlap:
  NormalForm prover edits lines ~190–230, Orbits prover edits
  lines ~324–376 + main signature thread, Slice prover edits
  lines ~1078–1089 (body of `parabolic_decompose` only).
- **Cross-file dependencies:**
  - NormalForm Objective 1 has `Slice.lean` Round 6 + Round 7
    APIs as dependencies — all stable, sorry-free.
  - Orbits Objective 2 has `pNormalForm_residual_orbit_iso` as
    its main dependency — sorry-free (Round 7).
  - Slice Objective 3 has `parametrizeX0PlusU_uniqueness` and the
    Round 6 Levi machinery as dependencies — all stable.
  - **Critical:** if Orbits Objective 2 attempts Route A (uses
    `parabolic_decompose`), it depends on Objective 3 landing.
    Round 8 plan recommends Route B to maintain independence.
  - **Signature change in Orbits Objective 2:** the prover will
    add hypotheses to `sIndependenceAndOrbitCriterion` and update
    `main`. Both edits are inside `Orbits.lean`; no cross-file
    cascade unless the prover takes option (b) (strengthen
    `pNormalForm_residual_orbit_iso`), which we discourage.
- **End-of-round merge:** harness merges all three file edits.
  Mid-round build breakage is possible (e.g., if Orbits prover's
  signature change cascades through `main`); end-of-round build
  must be green.

## Reusable Gotchas (carry forward, augmented through Round 7)

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
- **Adjoint-pair → orthogonal via paired inverse:**
  given `IsAdjointPair B B f g` and `g ∘ f = id`, conclude
  `IsOrthogonal B f` via `intro u v; calc B (f u) (f v) = B u (g (f v))
  := hAdj u (f v) _ = B u v := by rw [hinv_apply]`.
- **Cross-file proof structure validation via `lean_run_code`:** when a
  proof depends on a sister-prover's signature change not yet landed,
  validate the local proof shape with hypothetical inputs of the correct
  shape via a standalone `example`.
- **Bilinear-form identities via block-decomposition + `linear_combination`:**
  destruct vectors as `(e, v, e')`, apply `*_apply` lemmas, use the
  standard `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, …]`
  set, apply pairing-eq lemmas, then close with `linear_combination`
  using ε-symmetry hypotheses.
- **`IsSkewAdjoint` closure proofs over generic `[Field F]`:** use
  `linear_combination hf + hg` (add) / `linear_combination c * hf` (smul).
  **Do not use `linarith`** — it requires `LinearOrderedField`.
- **`Submodule.IsCompl.projection_add_projection_eq_self`** combined
  with `Submodule.IsCompl.projection_apply` to bridge the
  `IsCompl.projection` and `linearProjOfIsCompl`-coerced-subtype forms.
- **`conv_lhs => rw [...]`** to scope a rewrite to the LHS only.
- **Cross-file 4-tuple cascade:** when a structure or predicate gains a
  new conjunct, every `obtain ⟨...⟩` and `refine ⟨..., ?_⟩` site needs
  a parallel arity bump.
- **`linear_combination` is scalar-only over generic Modules.** It
  synthesises `CommSemiring`/`CommRing` on the *target* type. For module
  identities, drop to `rw` chains + `abel`.
- **Subtype-wrapping anti-pattern for `Iso + Property`:**
  packaging `{φ : … // ∀ w, …}` inside a helper `def` fails when the
  proof needs `cases` on `IsCompl.codisjoint` (Prop-eliminator
  restriction). Inline the `obtain` at each Prop-conclusion call site.
- **Drop explicit `LinearMap` coercion in `rw` arguments** once the
  callee accepts `LinearEquiv` — Lean auto-inserts.
- **`lean_leansearch` natural-language >> `lean_loogle`** for
  projection / `IsCompl.projection_*` API discovery.
- **`#print axioms` via `Bash` + `/tmp/check_axioms.lean`:** standard
  closure-check pattern.
- **(Round 7) `prodEquivOfIsCompl` symm via
  `Submodule.toLinearMap_prodEquivOfIsCompl_symm`:** the symm coerces
  to `(linearProjOfIsCompl p q h).prod (linearProjOfIsCompl q p _)`.
- **(Round 7) `set ... with hdef` for opaque shorthands, BUT NOT for
  sums you'll later `LinearMap.add_apply`-rewrite.**
- **(Round 7) `congr 1` does NOT split through outer `LinearMap.comp`.**
  Prove component identities as separate `have`s.
- **(Round 7) Linearity in 1st arg of `S.paired.pairing`: `map_add`
  first, then `add_apply`.**
- **(Round 7) `(qFun l : L0').val = qFunRaw l` is *definitionally* equal**
  when `qFun = LinearMap.codRestrict L0' qFunRaw _`.
- **(Round 7) Trailing `rfl` after `simp only [..., map_zero]` is
  "No goals" lint.**
- **(Round 7) LinearEquiv at definition; pass directly at use site.**
  Lean auto-coerces via `LinearEquiv.toLinearMap`-via-CoeFun. Explicit
  coercion fails type-check.
- **(Round 7) `S.V` ≡ `S.paired.E'` abbrev boundary requires explicit
  type ascription in helper defs:** every `↑d.symm e'` needs
  `(d.symm : S.paired.E' →ₗ[F] S.paired.E')`.
- **(Round 7) `XST_apply` private helper near top of consuming
  section.** Saves ~10 lines per consumer.
- **(Round 7) `extendL0'IsoToE'` block-extension pattern.** Build
  `E' ≃ E'` extending an `L0' ≃ L0'` iso by `id` on `L1'` via
  `prodEq.symm ≪≫ₗ (refl × h) ≪≫ₗ prodEq`. The two bridge lemmas
  (`projL1' ∘ d.symm = projL1'`, `projL0' ∘ d.symm = h.symm ∘ projL0'`)
  are reusable.

## Reporting

Each prover writes `.archon/task_results/<File>.md` with:
- which sorries were closed (line numbers + theorem names);
- which definitions / theorems were *added* (private helpers, signature
  updates);
- exact Mathlib lemmas used;
- any helper that was punted as `sorry` with a one-line gap explanation;
- confirmation that the assigned file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`);
- confirmation that `lake build` is green at end of round;
- confirmation that no `axiom` was introduced
  (`#print axioms` for each newly-closed theorem in the file).
