# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 3)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Latest review: `.archon/proof-journal/sessions/session_4/summary.md`
  and `.archon/proof-journal/sessions/session_4/recommendations.md`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, 2026-04-28)

- `lake build` succeeds; only `sorry` warnings + 1 unused-variable lint
  (`InducedOrbitToy/X0Geometry.lean:221:35: unused variable hlambda` —
  pre-existing, do not remove; the hypothesis is part of the
  autoformalised statement).
- Custom `axiom` declarations: 0 (re-verified by `lean_verify` /
  `#print axioms` on every public theorem; only
  `[propext, Classical.choice, Quot.sound]` appears, plus `sorryAx` on
  declarations that still embed an explicit `sorry`).
- Round-2 progress: 8 → 9 declaration-use `sorry` warnings (count rose
  by 1 due to deliberate helper-extraction in `NormalForm.lean`; one
  Tier B target was fully closed in `X0Geometry.lean`).
- Remaining declaration-use `sorry` lines (verified by `lake build`):
  - `InducedOrbitToy/X0Geometry.lean`: **0** ✅ (Tier B closed in session 4).
  - `InducedOrbitToy/Slice.lean`: 2
    - line 232 — `parametrizeX0PlusU_existence` (Tier D, 2 internal
      scoped `sorry`s at lines ≈256 and ≈294; do not retry until
      Tier S #2 lands),
    - line 442 — `uD_isParabolic` (Tier D, 1 internal scoped `sorry` at
      line 460; **assigned this round** — Tier S #1 corrects the
      statement so the sorry becomes provable).
  - `InducedOrbitToy/NormalForm.lean`: 6
    - line 196 — `pNormalForm_witnesses` (Tier A, blocked on Levi
      machinery; Round 4),
    - line 237 — `pNormalForm` (Tier D inheritance; **assigned this
      round** — closes once IsParabolicElement is restated),
    - line 307 — `residual_levi_extract` (Tier A, Round 4),
    - line 336 — `residual_levi_build` (Tier A + Tier S #3, Round 4 / 5),
    - line 482 — `kernelImage_ker` (Tier C + Tier S #3 + #4, Round 4 / 5),
    - line 577 — `kernelImage_im` (Tier C + Tier S #3, Round 4 / 5).
  - `InducedOrbitToy/Orbits.lean`: 1
    - line 242 — `sIndependenceAndOrbitCriterion` (Tier A deferred,
      depends on `pNormalForm_residual_orbit_iso` fully closing; Round 5).

## Round Plan (revised after session 4)

The 9 remaining sorries split into the four tiers below. This round
(Round 3) handles only **Tier S #1** — a focused statement-level
correction that unblocks 2 sorries directly and clears the IsParabolic
inheritance from a third.

| Tier | Targets | Status |
|---|---|---|
| **S #1** (this round) | `IsParabolicElement` is currently self-adjoint; should be isometry | **assigned this round** — 2 files (Slice + NormalForm) |
| A | `pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build` (NormalForm.lean) — need Levi-action machinery in Slice.lean | round 4 |
| S #2, #3, #4 | `UnipotentRadical` skew-adjoint, `SliceSetup.L0_paired`, `kernelImage_ker` Sₕ as `LinearEquiv` | round 4 / 5 |
| C | `kernelImage_ker`, `kernelImage_im` (NormalForm.lean) | round 4 / 5 (after S #3 + S #4) |
| D | `parametrizeX0PlusU_existence` (Slice.lean) | round 5 (after S #2) |
| A (deferred) | `sIndependenceAndOrbitCriterion` (Orbits.lean) | round 5 (after Tier A NormalForm round 4 lands) |

This split keeps each round atomic and avoids cascading data-refactor
breakage. Round 3's two objectives are tightly coupled — one prover per
file, but both files must land together. Mid-round build breakage is
expected (the harness runs in parallel); end-of-round build must be
green.

## Current Objectives (Round 3)

**Two objectives.** All other files are blocked on round-4+ work or are
already complete; **do not assign provers to them this round**.

### 1. `InducedOrbitToy/Slice.lean` — fix `uD_isParabolic` statement (Tier S #1, half 1)

**Target:** `uD_isParabolic` (line 442) — change the `IsAdjointPair`
conjunct from `IsAdjointPair B B (uD D) (uD D)` (self-adjoint, **false**)
to `IsAdjointPair B B (uD D) (uD (-D))` (isometry, **true**).

**Existing scoped sorry:** line 460, inside the IsAdjointPair conjunct
proof. Closes once the statement is corrected.

**Do NOT touch:** `parametrizeX0PlusU_existence` (line 232 — Tier D,
needs Tier S #2 / round 5). Leave its proof body unchanged.

#### Required statement edit

The current statement reads (verbatim):
```lean
theorem uD_isParabolic (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    LinearMap.IsAdjointPair S.ambientForm S.ambientForm
        (uD S D) (uD S D) ∧
      Submodule.map (uD S D) S.flagE ≤ S.flagE ∧
      Submodule.map (uD S D) S.flagEV0 ≤ S.flagEV0 := by
```

Change to:
```lean
theorem uD_isParabolic (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    LinearMap.IsAdjointPair S.ambientForm S.ambientForm
        (uD S D) (uD S (-D)) ∧
      Submodule.map (uD S D) S.flagE ≤ S.flagE ∧
      Submodule.map (uD S D) S.flagEV0 ≤ S.flagEV0 := by
```

(The two flag-preservation conjuncts are unchanged and already proven —
keep them as-is.)

#### Proof strategy for the corrected IsAdjointPair conjunct

The blueprint identity is `B (uD D x) y = B x (uD (-D) y)` for all `x, y`.
By direct expansion at `x = (e₁, v₁, e₁')`, `y = (e₂, v₂, e₂')`:

- Both sides expand to a sum of `λ(·, ·)` and `B₀(·, ·)` terms via the
  `ambientForm` definition.
- Use the existing helpers `Cdual_pairing_eq` (or `Cdual_pairing` for
  the no-`Nondeg` variant) and `S.epsSymm`.
- Use `(2 : F)⁻¹ + (2 : F)⁻¹ = 1` via `rw [← two_mul, mul_inv_cancel₀ _hChar]`
  (NOT `field_simp`).
- The `S.skew` / `IsSkewAdjoint S.formV0 S.X0` hypothesis is **not**
  needed here (the blueprint isometry identity is purely about the
  `Cdual D` and `D` blocks).

The same toolkit was used in `uD_conj_XCB` (sorry-free, lines ~280–350
of `Slice.lean`); follow that template.

#### Anti-patterns (do not retry — discovered in earlier rounds)

- `field_simp` leaves residual `1 + 1 = 2` for `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`
  — use `rw [← two_mul, mul_inv_cancel₀ _hChar]` instead.
- Multi-`let` defs (`uD`) are not definitionally equal to their RHS — use
  `uD_apply` and `uD_neg_apply` (the latter follows from `uD_apply` via
  congruence on `D ↦ -D`) to unfold before `linear_combination`.
- `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise — irrelevant here
  but mentioned for completeness.

#### Acceptance criteria

- `uD_isParabolic` is sorry-free at end of round.
- File compiles in isolation: `lake env lean InducedOrbitToy/Slice.lean`
  produces only the line 232 `sorry` warning (Tier D, untouched).
- `lake build` is green at end of round (after `NormalForm.lean` also
  lands its half).
- No new `axiom` declarations; `#print axioms uD_isParabolic` shows only
  `[propext, Classical.choice, Quot.sound]`.
- `parametrizeX0PlusU_existence` (line 232) is **untouched**.
- `XCB_apply`, `XST_apply`, `uD_apply`, `uD_conj_XCB`, `Cdual_pairing_eq`
  signatures are **unchanged** (they are load-bearing for `NormalForm.lean`).

### 2. `InducedOrbitToy/NormalForm.lean` — fix `IsParabolicElement` definition (Tier S #1, half 2)

**Target:** `IsParabolicElement` (line 86–89) — change the 4th conjunct
from `IsAdjointPair S.ambientForm S.ambientForm p p` (self-adjoint) to
`LinearMap.IsOrthogonal S.ambientForm p` (isometry). This matches the
predicate `IsometryEnd` already used in `Orbits.lean:34`.

**Existing scoped sorry to close:** line 272, inside `pNormalForm`'s
proof of `IsParabolicElement (uD D)`, the IsAdjointPair conjunct
(currently a Tier-D inheritance sorry).

**Do NOT touch:** `pNormalForm_witnesses` (line 196), `residual_levi_extract`
(line 307), `residual_levi_build` (line 336), `kernelImage_ker` (line 482),
`kernelImage_im` (line 577) — these are Round 4 / 5 work. Leave their
sorries intact.

#### Required definition edit

Current:
```lean
def IsParabolicElement (p : Module.End F S.V) : Prop :=
  IsUnit p ∧ Submodule.map p S.flagE = S.flagE ∧
    Submodule.map p S.flagEV0 = S.flagEV0 ∧
    LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p
```

Change to:
```lean
def IsParabolicElement (p : Module.End F S.V) : Prop :=
  IsUnit p ∧ Submodule.map p S.flagE = S.flagE ∧
    Submodule.map p S.flagEV0 = S.flagEV0 ∧
    LinearMap.IsOrthogonal S.ambientForm p
```

Update the docstring to reflect the new (correct) blueprint shape: "p is
an isometry of the ambient form" (replacing "form-preserving via the
Mathlib pair-adjoint predicate").

#### Proof strategy for the now-corrected IsAdjointPair conjunct in `pNormalForm`

The new 4th conjunct is `LinearMap.IsOrthogonal S.ambientForm (uD S D)`,
which unfolds to `∀ u v, S.ambientForm (uD D u) (uD D v) = S.ambientForm u v`.

Chain (after Slice.lean's `uD_isParabolic` has been corrected):
1. From the new `uD_isParabolic`'s 1st conjunct:
   `S.ambientForm (uD D x) y = S.ambientForm x (uD (-D) y)` for all `x, y`.
2. Substitute `y := uD D y`:
   `S.ambientForm (uD D x) (uD D y) = S.ambientForm x (uD (-D) (uD D y))`.
3. Use `uD_neg_inverse` (or `uD (-D) ∘ uD D = id`, which is
   `uD_neg_inverse S _hNondeg _hChar (-D)` after `neg_neg`) to reduce
   the RHS to `S.ambientForm x y`.

Concretely:
```lean
· -- LinearMap.IsOrthogonal S.ambientForm (uD S D)
  intro u v
  have hAdj := (uD_isParabolic S _hNondeg _hChar D).1   -- IsAdjointPair (uD D) (uD (-D))
  have hinv : uD S (-D) ∘ₗ uD S D = LinearMap.id := by
    have := uD_neg_inverse S _hNondeg _hChar (-D)
    simpa [neg_neg] using this
  -- B (uD D u) (uD D v) = B u (uD (-D) (uD D v)) = B u v.
  calc S.ambientForm (uD S D u) (uD S D v)
      = S.ambientForm u (uD S (-D) (uD S D v)) := hAdj u (uD S D v)
    _ = S.ambientForm u v := by
        congr 1
        exact congrArg (fun f : Module.End F S.V => f v) hinv
```

(Adjust syntax — `LinearMap.IsAdjointPair B B f g` unfolds to
`∀ x y, B (f x) y = B x (g y)`, which is what `hAdj u (uD S D v)` invokes.
Verify the exact unfold via `lean_hover_info` if needed.)

#### Side-effect: review existing `IsParabolicElement` consumers

After the definition change, the file's other consumers of
`IsParabolicElement` will need a one-liner update:

- `pNormalForm` — the explicit construction (lines 250–272) is the one
  with the sorry at line 272; close it as above.
- `residual_levi_extract` (line 307) — only consumes `IsParabolicElement
  S p` as a hypothesis; the body is still sorry'd. **No change needed**
  beyond ensuring the file compiles.
- `residual_levi_build` (line 336) — produces `IsParabolicElement S p` in
  its existential conclusion; still sorry'd as a whole. **No change
  needed** beyond ensuring the file compiles.
- `pNormalForm_residual_orbit_iso` (line 373) — only uses
  `IsParabolicElement` in the iff statement; the body delegates to the
  helpers. **No change needed.**

Verify all of these still compile after the definition change.

#### Acceptance criteria

- `IsParabolicElement` definition uses `LinearMap.IsOrthogonal
  S.ambientForm p` for its 4th conjunct.
- `pNormalForm`'s line-272 sorry is closed (replaced with the calc /
  rewrite chain above; ~6–10 lines).
- All other sorries in `NormalForm.lean` are **unchanged** (still
  present at lines 196, 307, 336, 482, 577).
- Sorry count in `NormalForm.lean`: 6 → 5 (one closed).
- File compiles in isolation: `lake env lean InducedOrbitToy/NormalForm.lean`
  produces 5 `sorry` warnings, no errors.
- `lake build` is green at end of round.
- No new `axiom` declarations; `#print axioms pNormalForm` shows only
  `[propext, Classical.choice, Quot.sound, sorryAx]` (the `sorryAx` is
  from the still-unfilled `pNormalForm_witnesses` — unrelated to this
  round's work).
- Helpers `isUnit_uD`, `map_uD_eq_of_le`, `XST_apply`,
  `kerXST_submod_le_ker`, `submoduleProdEquiv`, `finrank_submodule_prod`
  are **unchanged** (load-bearing for downstream rounds).

### Files NOT assigned this round

The following files have remaining sorries but are blocked by Round 4+
work. **Do not assign provers to them this round.**

- `InducedOrbitToy/Basic.lean` — Tier S #2 / #3 deferred to Round 4 / 5
  (require cascading consumer updates).
- `InducedOrbitToy/X0Geometry.lean` — done (closed in session 4); no work.
- `InducedOrbitToy/LocalForms.lean` — done; no work.
- `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion` Tier A
  deferred; Round 5 work after `pNormalForm_residual_orbit_iso` closes.

The harness has been observed to dispatch provers to all 6 files
regardless of `PROGRESS.md`'s stated assignments (session 4
"Process observation"). Provers receiving non-objective files this round
should:
- verify the file compiles in isolation,
- write a brief "no work" `task_results/<File>.md`, and
- **not edit anything**.

## Coordination notes for Round 3 (parallel-safety)

Round 3's two objectives are tightly **coupled across files**:

- `Slice.lean :: uD_isParabolic`'s new statement is consumed by
  `NormalForm.lean :: pNormalForm`'s line-272 proof.
- If the `NormalForm.lean` prover finishes first (using the new
  `uD_isParabolic` form), `lake build` will fail until the Slice.lean
  prover lands. Vice versa.

**Provers must NOT panic at mid-round build breakage** when the only
errors are in the *other* file. The plan-agent post-round verification
will check end-of-round `lake build` after both provers finish.

If a prover finishes its own file's edits but `lake build` still has
errors only in the *other* assigned file, the prover should:
- still write its `task_results/<File>.md` reporting its file's edits,
- explicitly note that the cross-file error is expected and will resolve
  when the sister prover lands.

## Reusable Gotchas (carry forward, augmented)

- `LinearMap.IsAdjointPair`, **not** `LinearMap.BilinForm.IsAdjointPair`.
- `LinearMap.IsOrthogonal B g` unfolds to `∀ x y, B (g x) (g y) = B x y`.
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
- **(NEW session 4) `Units.mkOfMulEqOne` for `IsUnit` from one-sided
  inverse on `Module.End F V` (finite-dim V):**
  `(Units.mkOfMulEqOne _ _ h).isUnit`. Replaces deprecated
  `LinearMap.mul_eq_one_of_mul_eq_one`; works because
  `Module.End F V` is `IsDedekindFiniteMonoid` for finite-dim V.
- **(NEW session 4) `obtain ⟨a, b, c⟩ := <existential>` makes
  destructured fields opaque** — fix by packaging the equation directly
  in helper's conclusion (avoid the existential wrapper).
- **(NEW session 4) Verify structure location via `grep` before scoping
  a refactor**; session 3 mis-located `DualTransposeData` to `Basic.lean`,
  but it actually lives in `X0Geometry.lean`.

## Reporting

Each prover writes `.archon/task_results/<File>.md` with:
- which sorries were closed (line numbers + theorem names);
- which statements were *changed* (definitions, hypothesis lists, etc.);
- exact Mathlib lemmas used;
- remaining subgoals and notable failed attempts (so the plan agent does
  not repeat dead ends);
- confirmation that the assigned file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`);
- confirmation that `lake build` is green **at end of round** (after the
  sister file lands; cross-file errors mid-round are expected for
  Round 3);
- confirmation that no `axiom` was introduced
  (`#print axioms` for each public theorem in the file).
