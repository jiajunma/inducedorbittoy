# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 4)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Latest review: `.archon/proof-journal/sessions/session_5/summary.md`
  and `.archon/proof-journal/sessions/session_5/recommendations.md`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, 2026-04-28 — end of Round 3)

- `lake build` succeeds; only `sorry` warnings + 1 unused-variable lint
  (`InducedOrbitToy/X0Geometry.lean:221:35: unused variable hlambda` —
  pre-existing, do not remove; the hypothesis is part of the
  autoformalised statement of `sDual_restrict_ker_isIso`).
- Custom `axiom` declarations: 0 (re-verified by `lean_verify` on every
  public theorem; only `[propext, Classical.choice, Quot.sound]` appears,
  plus `sorryAx` on declarations that still embed an explicit `sorry`).
- Round-3 progress: 9 → 7 declaration-use `sorry` warnings (Tier S #1
  landed: `uD_isParabolic` and `pNormalForm`'s IsOrthogonal conjunct
  both closed).
- Remaining declaration-use `sorry` lines (verified by `lake build`):
  - `InducedOrbitToy/Slice.lean`: 1
    - line 232 — `parametrizeX0PlusU_existence` (Tier D, 2 internal
      scoped `sorry`s at lines 256 and 294; **assigned this round**
      — Tier S #2 unblocks it).
  - `InducedOrbitToy/NormalForm.lean`: 5
    - line 195 — `pNormalForm_witnesses` (Tier A, blocked on Levi
      machinery; Round 6),
    - line 319 — `residual_levi_extract` (Tier A, Round 6),
    - line 348 — `residual_levi_build` (Tier A + Tier S #3, Round 6),
    - line 495 — `kernelImage_ker` (Tier C + Tier S #3 + #4, Round 5),
    - line 590 — `kernelImage_im` (Tier C + Tier S #3, Round 5).
  - `InducedOrbitToy/Orbits.lean`: 1
    - line 242 — `sIndependenceAndOrbitCriterion` (Tier A deferred,
      depends on `pNormalForm_residual_orbit_iso` fully closing; Round 7).

## Round Plan (revised after session 5)

The 7 remaining sorries split across Tier S structural fixes, Tier A
infrastructure, Tier C closes, and the deferred Tier A in `Orbits.lean`.
The plan-agent expects **4 more prover rounds** (4 → 7), each focused on
a single block of work to keep mid-round build coupling manageable:

| Round | Focus | Files | Sorry Δ |
|---|---|---|---|
| **4 (this round)** | **Tier S #2** + Tier S #3 (additive) + close `parametrizeX0PlusU_existence` | Basic, Slice, Orbits | 7 → 6 |
| 5 | Tier S #4 + close `kernelImage_ker`, `kernelImage_im` | NormalForm, Orbits | 6 → 4 |
| 6 | Levi machinery (additive) + close `pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build` | Slice, NormalForm | 4 → 1 |
| 7 | Close `sIndependenceAndOrbitCriterion` | Orbits | 1 → 0 |

Round 4's three objectives are **tightly coupled**: `Basic.lean`'s
`UnipotentRadical` tightening cascades to consumers in `Slice.lean` and
`Orbits.lean`. Mid-round build breakage is expected (the harness runs in
parallel); end-of-round build must be green.

## Current Objectives (Round 4)

**Three objectives.** All other files are blocked on Round 5+ work or are
already complete; **do not assign provers to them this round**.

### 1. `InducedOrbitToy/Basic.lean` — Tier S #2 + Tier S #3 (structural fixes)

Two structural changes to definitions/structures. Both are
*plan-agent-mandated* — the prover must apply them as written below, then
verify the file still type-checks.

#### 1a. Tier S #2 — Tighten `UnipotentRadical` with skew-adjointness

**Target:** `UnipotentRadical` (line 208).

**Current definition** (verbatim, lines 208–213):
```lean
noncomputable def UnipotentRadical {F : Type*} [Field F] (S : SliceSetup F) :
    Submodule F (Module.End F S.V) where
  carrier :=
    { f | (∀ x ∈ S.flagE, f x = 0) ∧
          (∀ x ∈ S.flagEV0, f x ∈ S.flagE) ∧
          (∀ x : S.V, f x ∈ S.flagEV0) }
```

**Change to** (4 conjuncts):
```lean
noncomputable def UnipotentRadical {F : Type*} [Field F] (S : SliceSetup F) :
    Submodule F (Module.End F S.V) where
  carrier :=
    { f | (∀ x ∈ S.flagE, f x = 0) ∧
          (∀ x ∈ S.flagEV0, f x ∈ S.flagE) ∧
          (∀ x : S.V, f x ∈ S.flagEV0) ∧
          IsSkewAdjoint S.ambientForm f }
```

(Add the 4th conjunct `IsSkewAdjoint S.ambientForm f`, which encodes
"`f` is skew w.r.t. the ambient bilinear form".)

**Update the closure proofs** (`zero_mem'`, `add_mem'`, `smul_mem'`):
extend each `refine ⟨?_, ?_, ?_⟩` to `refine ⟨?_, ?_, ?_, ?_⟩` and discharge
the new IsSkewAdjoint goal:
- `zero_mem'`: trivial — `IsSkewAdjoint B 0` reduces to `B 0 _ + B _ 0 = 0`,
  i.e. `0 + 0 = 0`. `intro x y; simp [LinearMap.zero_apply, map_zero]` or
  `intro x y; simp` should close it.
- `add_mem'`: `IsSkewAdjoint B (f + g)` from `IsSkewAdjoint B f` +
  `IsSkewAdjoint B g`. Unfold `(f + g) x = f x + g x`, distribute `B`,
  rearrange. Pattern: `intro x y; simp only [LinearMap.add_apply,
  map_add, LinearMap.add_apply]; linear_combination (h_f x y) + (h_g x y)`
  — or just `linarith` after distributing.
- `smul_mem'`: `IsSkewAdjoint B (c • f)` from `IsSkewAdjoint B f`.
  Pattern: `intro x y; simp only [LinearMap.smul_apply, map_smul,
  LinearMap.smul_apply, smul_eq_mul]; linear_combination c * (h_f x y)`.

**Update the docstring** at line 200–207 to mention the 4th conjunct
("`f` is skew-adjoint w.r.t. `S.ambientForm`") and remove the
"loose 𝔭" framing — the new definition matches `𝔲 = 𝔭 ∩ 𝔤`.

#### 1b. Tier S #3 — Add Lagrangian-condition fields to `SliceSetup`

**Target:** `SliceSetup` (line 129–138).

**Current structure** has fields:
```lean
structure SliceSetup (F : Type*) [Field F] extends X0Setup F where
  paired : PairedSpaces F
  L1 : Submodule F paired.E
  L0 : Submodule F paired.E
  L1' : Submodule F paired.E'
  L0' : Submodule F paired.E'
  isComplL : IsCompl L1 L0
  isComplL' : IsCompl L1' L0'
  L1_paired : IsPaired paired.pairing L1 L1'
  L0_isotropic : IsIsotropic paired.pairing L0 L0'
```

**Notes on the existing `L0_isotropic` field:**

The blueprint requires the standard Lagrangian decomposition:
- `L1 ↔ L1'` perfectly paired (already there as `L1_paired`),
- `L0 ↔ L0'` perfectly paired (MISSING; the planned `L0_paired` field),
- `λ(L1, L0') = 0` (MISSING; needed by `kernelImage_ker` /
  `kernelImage_im` / `residual_levi_build`),
- `λ(L0, L1') = 0` (MISSING; symmetric).

The current `L0_isotropic` (typed as `IsIsotropic paired.pairing L0 L0'`)
is **mathematically inconsistent with `L0_paired`** — the latter says
`L0 × L0' → F` is non-degenerate (perfect pairing), so it cannot also be
identically zero. The `L0_isotropic` field appears to have been a
mis-named placeholder during autoformalize.

**Audit step (do this first):** grep all uses of `L0_isotropic` in the
codebase. The expected outcome:

```bash
grep -rn "L0_isotropic" InducedOrbitToy/
```

If the field is unused (or used only in autoformalization scaffolding
that can be retargeted), remove it and replace with the intended
`L1_isotropic_L0'` (the cross-isotropy condition `λ(L1, L0') = 0`). If it
is used and the use site genuinely requires `λ(L0, L0') = 0`, then there
is a deeper modelling bug — escalate to the plan agent before proceeding.

**Change** (assuming `L0_isotropic` is replaceable):
```lean
structure SliceSetup (F : Type*) [Field F] extends X0Setup F where
  paired : PairedSpaces F
  L1 : Submodule F paired.E
  L0 : Submodule F paired.E
  L1' : Submodule F paired.E'
  L0' : Submodule F paired.E'
  isComplL : IsCompl L1 L0
  isComplL' : IsCompl L1' L0'
  L1_paired : IsPaired paired.pairing L1 L1'
  L0_paired : IsPaired paired.pairing L0 L0'
  L1_isotropic_L0' : IsIsotropic paired.pairing L1 L0'
  L0_isotropic_L1' : IsIsotropic paired.pairing L0 L1'
```

If `L0_isotropic` *is* used somewhere mathematically (i.e. a downstream
proof actively relies on `λ(L0, L0') = 0`), keep it but **add the three
new fields alongside** — and flag the inconsistency in the prover's
report so the plan agent can untangle it next round.

**No proof body to discharge** — these are structure fields, additive
data only. Existing `SliceSetup` instances in the codebase (if any —
unlikely given this is a structure parameter not a singleton) will need
to be updated, but a quick audit suggests there are no such instances
(only the parameter `(S : SliceSetup F)` is threaded through proofs).

#### Acceptance criteria for objective 1

- `Basic.lean` compiles in isolation:
  `lake env lean InducedOrbitToy/Basic.lean` produces no errors.
- The 4 conjuncts of `UnipotentRadical` are present (in the order: vanish
  on flagE, send flagEV0 to flagE, send V to flagEV0, IsSkewAdjoint
  ambientForm).
- The 3 (or 4 if `L0_isotropic` is preserved) new fields of `SliceSetup`
  are present.
- `lake build` is green at end of round (after sister provers land).
- No new `axiom` declarations.
- `c_eq_finrank_quotient` (the only theorem in this file) is unchanged
  and still proven.

### 2. `InducedOrbitToy/Slice.lean` — close `parametrizeX0PlusU_existence`

**Target:** `parametrizeX0PlusU_existence` (line 232) — close both
internal scoped sorries (lines 256 and 294) using the **new** 4th conjunct
of `UnipotentRadical` (which provides skew-adjointness of `Y`).

**Do NOT touch:** `uD_isParabolic` (line 442) — closed in Round 3, no
work this round. `Cdual`, `uD`, `XCB`, `XST`, `BST`, `CST`, `projL0'`,
`projL1'`, all `_apply` helpers — all sorry-free, do not modify.

#### Required changes

After Tier S #2 lands, the hypothesis `_hY : Y ∈ UnipotentRadical S` now
gives a 4-tuple destructure: `_hY = ⟨hflagE, hflagEV0, hAll, hSkewY⟩`
where `hSkewY : IsSkewAdjoint S.ambientForm Y` (i.e.
`∀ x y, S.ambientForm (Y x) y + S.ambientForm x (Y y) = 0`).

Update line 264 from:
```lean
obtain ⟨hflagE, hflagEV0, hAll⟩ := _hY
```
to:
```lean
obtain ⟨hflagE, hflagEV0, hAll, hSkewY⟩ := _hY
```

#### Sorry at line 256 — `IsSkewB B`

**Goal** after the existing `intro u v; show ...`:
```
S.lambda ((projE ∘ₗ Y ∘ₗ inE') u) v
    + S.eps * S.lambda ((projE ∘ₗ Y ∘ₗ inE') v) u = 0
```

**Strategy:** This is the `(E', E')`-block of the skew-adjointness identity
for `Y` w.r.t. `S.ambientForm` evaluated at the points
`(0, 0, u)` and `(0, 0, v)`. Apply `hSkewY (0, 0, u) (0, 0, v)`:
```
S.ambientForm (Y (0, 0, u)) (0, 0, v) +
  S.ambientForm (0, 0, u) (Y (0, 0, v)) = 0
```

Unfold `ambientForm` (it's `λ + B₀ + ε·λ` per `LinearMap.mk₂`).
Both `(0, 0, u)` and `(0, 0, v)` have zero E and V0 parts, so the
`B₀` and the `ε·λ(_.1, _.2.2)` terms collapse on the appropriate sides.
What remains is exactly `λ((Y (0,0,u)).1, v) + ε · λ((Y (0,0,v)).1, u) = 0`,
i.e. `λ(projE(Y(inE'(u))), v) + ε · λ(projE(Y(inE'(v))), u) = 0`. The
`projE` and `inE'` definitions match by `simp` / `rfl`.

Suggested proof skeleton:
```lean
intro u v
show S.lambda ((projE ∘ₗ Y ∘ₗ inE') u) v
    + S.eps * S.lambda ((projE ∘ₗ Y ∘ₗ inE') v) u = 0
have h := hSkewY (0, 0, u) (0, 0, v)
-- h : S.ambientForm (Y (0,0,u)) (0,0,v) + S.ambientForm (0,0,u) (Y (0,0,v)) = 0
simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, projE, inE',
  LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.inl_apply,
  LinearMap.fst_apply, LinearMap.snd_apply,
  Prod.fst, Prod.snd, map_zero, LinearMap.zero_apply, zero_add, add_zero,
  mul_zero, mul_one] at h
-- After simp, h should match the goal up to ordering / commutativity
linarith
```
(Adjust the `simp only` set as needed — the precise lemmas to peel
`S.ambientForm` of `(0, 0, u)` are `Prod.fst_zero`, `Prod.snd_zero`, plus
`map_zero` to kill the `λ(_.1, _.2.2)` and `B₀(_.2.1, _.2.1)` terms.)

If `linarith` fails, try `linear_combination h` after a final `ring_nf`.

#### Sorry at line 294 — E component of the equality

**Goal:** at `(e, v, e') ∈ S.V`, after the existing `LinearMap.sub_apply`,
`XCB_apply`, `X0Lift_apply`, `hY_sum` rewrites, the E-component of
`XCB S C B - X0Lift S = Y` evaluated at `(e, v, e')` reduces to:
```
Cdual S C v + B e' = (Y (0, v, 0)).1 + (Y (0, 0, e')).1
```
where `C := projV0 ∘ₗ Y ∘ₗ inE'` and `B := projE ∘ₗ Y ∘ₗ inE'`.

The first summand on the RHS, `(Y (0, v, 0)).1`, is the V₀→E block of
`Y` applied to `v`. The new skew-adjointness lets us identify this as
`Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v` (modulo sign/ε via `Cdual_pairing_eq`).
The second summand, `(Y (0, 0, e')).1`, is exactly `B e'` by the
definition of `B = projE ∘ₗ Y ∘ₗ inE'`.

**Strategy:** Use `hSkewY (0, v, 0) (0, 0, w)` for an arbitrary `w ∈ S.E'`
to extract the E-block identity. Specifically, the V₀→E block of `Y` is
forced by skew-adjointness to equal `Cdual` of the E'→V₀ block via the
identity:
```
λ((Y (0, v, 0)).1, w) = -ε · λ((Y (0, 0, w)).1, v) ... no, that's wrong.
```

Actually, work it out: `S.ambientForm (Y (0, v, 0)) (0, 0, w) +
S.ambientForm (0, v, 0) (Y (0, 0, w)) = 0`. Unfolding (with the V0×E'
component zero on the left of the second term and the E×V0 components
zero on the right of the first term), we get:

```
λ((Y(0,v,0)).1, w) + S.formV0 v ((Y (0,0,w)).2.1) = 0
```

(The other terms vanish: `B₀(_.2.1, _.2.1)` for the first half has
`(Y(0,v,0)).2.1` paired with `0`, etc.)

Rearranging:
```
λ((Y(0,v,0)).1, w) = - S.formV0 v ((Y(0,0,w)).2.1)
                   = - S.formV0 v ((projV0 ∘ Y ∘ inE') w)
                   = - S.formV0 v (C w)
```

where `C := projV0 ∘ₗ Y ∘ₗ inE'` (our chosen `C`). Now
`Cdual_pairing_eq` says `λ(Cdual D v, w) = S.formV0 (D w) v` (for any
`D : S.E' →ₗ[F] S.V0`). With `D := -C` (or with a sign adjustment), this
gives `λ((Y(0,v,0)).1, w) = λ(Cdual (-C) v, w) = -λ(Cdual C v, w)`.

Hmm — this would say `(Y(0,v,0)).1 = -Cdual C v` (by non-degeneracy of
`λ`). The expected E component of the equation is:
```
(Cdual C) v + B e' - 0 = (Y(0,v,0)).1 + (Y(0,0,e')).1
```
(via `XCB(C, B) - X0Lift` evaluated at `(e, v, e')`). With
`(Y(0,0,e')).1 = (projE ∘ Y ∘ inE') e' = B e'`, the equation reduces to
`(Cdual C) v = (Y(0,v,0)).1`, but skew-adjointness gives
`(Y(0,v,0)).1 = -(Cdual C) v`. There's a sign discrepancy.

This may indicate that `C` should be defined as `-(projV0 ∘ₗ Y ∘ₗ inE')`
(negate), or that `XCB_apply` has the opposite sign convention from what
the proof expects. **Audit `XCB_apply` and `Cdual_pairing_eq` for the
exact sign convention before committing to a fix** (use `lean_hover_info`).

The blueprint identity is documented in `informal/slice.md`. Cross-check
against the existing successful proof of `uD_conj_XCB` (sorry-free in
Slice.lean), which uses the same toolkit and has the right signs.

If the sign analysis reveals that `C := -(projV0 ∘ₗ Y ∘ₗ inE')` is the
right choice, update line 246 from
`refine ⟨projV0 ∘ₗ Y ∘ₗ inE', projE ∘ₗ Y ∘ₗ inE', ?_, ?_⟩`
to
`refine ⟨-(projV0 ∘ₗ Y ∘ₗ inE'), projE ∘ₗ Y ∘ₗ inE', ?_, ?_⟩`,
adjust the IsSkewB proof accordingly (the negation flips the sign in the
identity), and discharge the line-294 sorry as
`λ((Y(0,v,0)).1, w) = λ(Cdual C v, w)` for the new `C`.

#### Acceptance criteria for objective 2

- `parametrizeX0PlusU_existence` (line 232) is sorry-free at end of round.
- File compiles in isolation:
  `lake env lean InducedOrbitToy/Slice.lean` produces no `sorry`
  warnings.
- `lake build` is green at end of round (after sister provers land).
- No new `axiom` declarations; `#print axioms parametrizeX0PlusU_existence`
  shows only `[propext, Classical.choice, Quot.sound]`.
- `uD_isParabolic`, `uD_conj_XCB`, `Cdual_pairing_eq`, `Cdual`, `uD`,
  `XCB`, `XST`, `BST`, `CST`, `projL0'`, `projL1'`, and all `_apply`
  helpers are **unchanged** (they are load-bearing for `NormalForm.lean`).

### 3. `InducedOrbitToy/Orbits.lean` — cascade for tightened `UnipotentRadical`

**Target:** `XCB_sub_X0Lift_mem_unipotent` (line 166) and
`XST_sub_X0Lift_mem_unipotent` (line 196). With the new 4th conjunct in
`UnipotentRadical`, both helpers must now also prove
`IsSkewAdjoint S.ambientForm (XCB C B - X0Lift S)` (or the analogous
statement for `XST`).

**Do NOT touch:** `sIndependenceAndOrbitCriterion` (line 242, Tier A
deferred to Round 7) — leave its sorries unchanged. `inducedOrbits` and
`main` proof structures should remain intact; only the cascade lemmas
need updating.

#### Required changes

##### `XCB_sub_X0Lift_mem_unipotent` (line 166)

This helper currently claims membership without any skew hypothesis on
`(C, B)`. The new tight `UnipotentRadical` requires skew-adjointness,
which **does not hold for arbitrary `(C, B)`**. Two acceptable fixes:

**Option A — add a skew hypothesis to the helper:**
```lean
private lemma XCB_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  refine ⟨?_, ?_, ?_, hskew⟩
  -- existing proof of the 3 flag-stability conjuncts unchanged
```
The caller (`XST_sub_X0Lift_mem_unipotent`) then constructs `hskew` from
`IsSkewT T` + `S.skew` and passes it through.

**Option B — bypass `XCB_sub_X0Lift_mem_unipotent` from `XST_sub_X0Lift_mem_unipotent`:**
Inline the 3 flag-stability proofs directly in `XST_sub_X0Lift_mem_unipotent`
and add the skew-adjointness proof. Keep `XCB_sub_X0Lift_mem_unipotent`
either deleted, or kept as a private "loose flag-stability only" lemma
that no longer claims `UnipotentRadical` membership (e.g. just claim the
3 flag-stability properties separately).

**Recommended:** Option A is cleaner and preserves the helper.

##### `XST_sub_X0Lift_mem_unipotent` (line 196)

Currently:
```lean
private lemma XST_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) :
    XST S Sₕ T - X0Lift S ∈ UnipotentRadical S :=
  XCB_sub_X0Lift_mem_unipotent S (CST S Sₕ) (BST S T)
```

Change to add `IsSkewT T` hypothesis and discharge skew-adjointness:
```lean
private lemma XST_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (hT : IsSkewT S T) :
    XST S Sₕ T - X0Lift S ∈ UnipotentRadical S := by
  apply XCB_sub_X0Lift_mem_unipotent S (CST S Sₕ) (BST S T)
  -- prove `IsSkewAdjoint S.ambientForm (XST S Sₕ T - X0Lift S)`
  intro x y
  obtain ⟨e₁, v₁, e₁'⟩ := x
  obtain ⟨e₂, v₂, e₂'⟩ := y
  rw [LinearMap.sub_apply, LinearMap.sub_apply, XST_apply, X0Lift_apply]
  -- Now expand `S.ambientForm` (`mk₂` of `λ + B₀ + ε·λ`) and apply:
  -- - `S.skew` (X0 skew on V0): `B₀ (X0 v₁) v₂ + B₀ v₁ (X0 v₂) = 0`
  -- - `IsSkewT T` on the L0' components projected through projL0'
  -- - `S.epsSymm` for the cross-pairing terms
  -- The blueprint identity is in informal/slice.md / informal/orbits.md
  sorry  -- detailed expansion needed
```

The proof of the new skew-adjointness goal is **the substantive new
content** for this round in Orbits.lean. The expansion mirrors
`uD_conj_XCB`'s proof in `Slice.lean`: destruct vectors, `simp only` with
the `ambientForm` lemma set, apply `S.skew` + `IsSkewT T` + `S.epsSymm`,
close with `linear_combination`.

If the prover finds the skew-adjointness proof intractable, **escalate**
by reporting the blocker — do not introduce a new `sorry` in
`XST_sub_X0Lift_mem_unipotent` itself; the helper is private and not in
the round's "remaining sorry" budget.

##### Update call sites of `XST_sub_X0Lift_mem_unipotent`

The new signature has two extra hypotheses (`_hNondeg`, `_hChar`) and one
extra explicit hypothesis (`hT : IsSkewT S T`). Update:
- `XST_mem_O0PlusU` (line 204) — currently passes `Sₕ T` only; needs
  `_hNondeg`, `_hChar`, and the skew hypothesis. The caller has access
  to these (or can take them as new parameters).
- `inducedOrbits` (line 218) — has `_hT : T ∈ Tset_circ`; unfold to
  extract `IsSkewT T` (i.e. `_hT.1`) for the call.
- Any other call site found by `grep -n XST_sub_X0Lift_mem_unipotent`.

The propagating `_hNondeg` / `_hChar` may also need to be threaded into
intermediate helpers; if so, add them to `XST_mem_O0PlusU` and propagate
upward.

#### Acceptance criteria for objective 3

- `XCB_sub_X0Lift_mem_unipotent` and `XST_sub_X0Lift_mem_unipotent`
  produce a proof of the *tightened* (4-conjunct) `UnipotentRadical`
  membership.
- All call sites of `XST_sub_X0Lift_mem_unipotent` updated to pass the
  new hypothesis (and any new `_hNondeg` / `_hChar` if they are added).
- `lake env lean InducedOrbitToy/Orbits.lean` has only the line 242
  `sIndependenceAndOrbitCriterion` `sorry` warning — same as start of
  round.
- `lake build` is green at end of round.
- No new `axiom` declarations; `#print axioms` for `inducedOrbits` /
  `main` shows `[propext, Classical.choice, Quot.sound]` (plus `sorryAx`
  for `main`'s downstream call to `sIndependenceAndOrbitCriterion`).
- `inducedOrbits`, `main`, `multiplicityNonDeg`, `multiplicityOddCase`,
  `embO0`, `O0`, `IndPG`, `O0PlusU`, `GOrbit` signatures and proof
  structures **unchanged** (only the cascade helpers are modified).

### Files NOT assigned this round

The following files have remaining sorries but are blocked by Round 5+
work. **Do not assign provers to them this round.**

- `InducedOrbitToy/X0Geometry.lean` — already done (closed in session 4);
  no work.
- `InducedOrbitToy/LocalForms.lean` — already done; no work.
- `InducedOrbitToy/NormalForm.lean` — `kernelImage_ker`, `kernelImage_im`
  are Round 5 (need Tier S #4 + Tier S #3 fields, both landing this
  round and next); `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` are Round 6 (need Levi machinery).

The harness has been observed to dispatch provers to all 6 files
regardless of `PROGRESS.md`'s stated assignments. Provers receiving
non-objective files this round should:
- verify the file compiles in isolation (modulo expected mid-round
  cross-file errors from Tier S #2's cascade),
- write a brief "no work" `task_results/<File>.md`, and
- **not edit anything**.

## Coordination notes for Round 4 (parallel-safety)

Round 4's three objectives are **tightly coupled across files**:

- `Basic.lean`'s tightened `UnipotentRadical` cascades to:
  - `Slice.lean :: parametrizeX0PlusU_existence` (consumes the new 4th
    conjunct via the `_hY` hypothesis destructure);
  - `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent` /
    `XST_sub_X0Lift_mem_unipotent` (must produce the new 4th conjunct
    in their `refine` blocks).
- `Basic.lean`'s new `SliceSetup` fields are purely additive — no
  existing proof breaks (they are new fields no proof currently
  references).

Mid-round build breakage is expected when:
- The Slice prover finishes first using the 4-tuple `obtain` while
  Basic is still 3-tuple → "expected 3, got 4" error.
- The Orbits prover finishes first proving the 4-conjunct `refine` while
  Basic is still 3-conjunct → "expected 3, got 4" error.
- The Basic prover finishes first → Slice and Orbits both fail until
  they land their cascade.

**Provers must NOT panic at mid-round build breakage** when the only
errors are in the *other* file's still-pending edits. The plan-agent
post-round verification will check end-of-round `lake build` after all
three provers finish.

If a prover finishes its own file's edits but `lake build` still has
errors only in the *other* assigned files, the prover should:
- still write its `task_results/<File>.md` reporting its file's edits,
- explicitly note that the cross-file error is expected and will resolve
  when the sister provers land.

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
- **(NEW session 5) Adjoint-pair → orthogonal via paired inverse:**
  given `IsAdjointPair B B f g` and `g ∘ f = id`, conclude
  `IsOrthogonal B f` via `intro u v; calc B (f u) (f v) = B u (g (f v))
  := hAdj u (f v) _ = B u v := by rw [hinv_apply]`.
- **(NEW session 5) Cross-file proof structure validation via
  `lean_run_code`:** when a proof depends on a sister-prover's signature
  change not yet landed, validate the local proof shape with hypothetical
  inputs of the correct shape via a standalone `example`. Eliminates
  uncertainty during the parallel race.
- **(NEW session 5) Bilinear-form identities via block-decomposition +
  `linear_combination`:** for an identity in `S.ambientForm`, destruct
  vectors as `(e, v, e')`, apply `*_apply` lemmas, use the standard
  `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, …]` set,
  apply pairing-eq lemmas to all `λ(F ·, ·)` atoms, then close with
  `linear_combination` using ε-symmetry-derived hypotheses (`hε`, `hε2`,
  point-specific instantiations).

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
  sister files land; cross-file errors mid-round are expected for
  Round 4);
- confirmation that no `axiom` was introduced
  (`#print axioms` for each public theorem in the file).
