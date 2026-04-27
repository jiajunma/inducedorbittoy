# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 5)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Latest reviews: `.archon/proof-journal/sessions/session_5/summary.md`
  and `.archon/proof-journal/sessions/session_5/recommendations.md`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, 2026-04-28 — end of Round 4)

- `lake build` succeeds; only `sorry` warnings + 1 unused-variable lint
  (`InducedOrbitToy/X0Geometry.lean:221:35: unused variable hlambda` —
  pre-existing, do not remove; the hypothesis is part of the
  autoformalised statement of `sDual_restrict_ker_isIso`).
- Custom `axiom` declarations: 0 (re-verified by `lean_verify` on every
  public theorem; only `[propext, Classical.choice, Quot.sound]` appears,
  plus `sorryAx` on declarations that still embed an explicit `sorry`).
- Round-4 progress: 7 → 6 declaration-use `sorry` warnings.
  - **`Slice.lean :: parametrizeX0PlusU_existence` is sorry-free** (Tier D
    closed via Tier S #2's new `IsSkewAdjoint` conjunct on
    `UnipotentRadical`).
  - Tier S #2 (`UnipotentRadical` tightening) and Tier S #3 (`SliceSetup`
    Lagrangian quartet `L0_paired`, `L1_isotropic_L0'`, `L0_isotropic_L1'`,
    replacing mis-named `L0_isotropic`) both landed in Basic.lean with
    full cascades through Slice.lean (`parametrizeX0PlusU_mem`) and
    Orbits.lean (`XCB_sub_X0Lift_mem_unipotent`,
    `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`, `inducedOrbits`,
    `main`).
- Remaining declaration-use `sorry` lines (verified by `lake build`):
  - `InducedOrbitToy/NormalForm.lean`: 5
    - line 195 — `pNormalForm_witnesses` (Tier A, blocked on Levi
      machinery; Round 6),
    - line 319 — `residual_levi_extract` (Tier A, Round 6),
    - line 348 — `residual_levi_build` (Tier A; Tier S #3 fields now
      present, but Levi machinery still needed; Round 6),
    - line 495 — `kernelImage_ker` (Tier C + Tier S #4;
      **assigned this round**),
    - line 590 — `kernelImage_im` (Tier C; Tier S #3 condition now
      available; **assigned this round**).
  - `InducedOrbitToy/Orbits.lean`: 1
    - line 324 — `sIndependenceAndOrbitCriterion` (Tier A deferred,
      depends on `pNormalForm_residual_orbit_iso` fully closing; Round 7).

## Round Plan (revised after Round 4)

The 6 remaining sorries split across one Tier S structural fix
(Tier S #4), two Tier C closes (this round), three Tier A items
requiring Levi machinery (Round 6), and one deferred Tier A in
`Orbits.lean` (Round 7).

| Round | Focus | Files | Sorry Δ |
|---|---|---|---|
| **5 (this round)** | **Tier S #4 + close `kernelImage_ker`, `kernelImage_im`** | NormalForm | 6 → 4 |
| 6 | Levi machinery (additive) + close `pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build` | Slice, NormalForm | 4 → 1 |
| 7 | Close `sIndependenceAndOrbitCriterion` | Orbits | 1 → 0 |

Round 5 is **single-file**: only `NormalForm.lean` has work this round.
All other files are either complete or blocked on Round 6+ infrastructure.

## Current Objectives (Round 5)

**One objective.** All other files are blocked on Round 6+ work or are
already complete; **do not assign provers to them this round**.

### 1. `InducedOrbitToy/NormalForm.lean` — Tier S #4 + close `kernelImage_ker` + `kernelImage_im`

Three sub-tasks, in order:

#### 1a. Tier S #4 — Retype `kernelImage_ker`'s `Sₕ` to a `LinearEquiv`

**Target:** `kernelImage_ker` (line 495).

**Current signature** (verbatim, lines 495–498):
```lean
theorem kernelImage_ker
    (_hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.ker (XST S Sₕ T) = kerXST_submod S Sₕ T := by
```

**Change to** (mirroring `kernelImage_im` line 590–594):
```lean
theorem kernelImage_ker
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (hT : IsSkewT S T) :
    LinearMap.ker (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) =
      kerXST_submod S (Sₕ : S.L1' →ₗ[F] S.Vplus) T := by
```

(Underscore-prefix → real name on hypotheses now that they will be used.
Coerce `Sₕ` explicitly inside `XST` and `kerXST_submod` since both still
take a `LinearMap`.)

**Update the call site at `kernelImage_dim` line 611:** currently:
```lean
rw [kernelImage_ker S _hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) T _hT]
```
After retype, `kernelImage_dim`'s `Sₕ` is already a `LinearEquiv` (line
606); pass it directly:
```lean
rw [kernelImage_ker S _hNondeg Sₕ T _hT]
```

#### 1b. Close `kernelImage_ker` (lines 537, 543)

Both sorries are in the reverse inclusion `ker XST ⊆ kerXST_submod`.
The proof prefix (lines 502–530) already establishes:
- `hX0v_zero : S.X0 v = 0`,
- `hSh_zero : (Sₕ (projL1' S e') : S.V0) = 0`,
- `hv_in_kerX0 : v ∈ LinearMap.ker S.X0`.

After retyping `Sₕ` to `LinearEquiv`, use `Sₕ.injective` to push
`hSh_zero` to `(projL1' S e' : S.E') = 0`. Combined with the
decomposition `e' = projL1' e' + projL0' e'` (via `S.isComplL'`), this
gives `e' ∈ L0'` (i.e. `e' = projL0' e'` viewed in `E'`).

Then the equation `Cdual S (CST Sₕ) v + (T (projL0' S e') : S.E) = 0`
(line 506, `hx1`) splits via the Lagrangian conditions:

**Key fact (need a helper):** `Cdual S (CST Sₕ) v ∈ S.L1` for any
`v : S.V0`.

Why: `CST Sₕ = S.Vplus.subtype ∘ₗ Sₕ ∘ₗ projL1'` zeros on `L0'` (since
`projL1'` lands in `L1'`, and `projL1'` of an `L0'` element is 0). For
any `e' ∈ L0'`, `(CST Sₕ) e' = 0`. By `Cdual_pairing_eq`,
`λ(Cdual S (CST Sₕ) v, e') = -formV0 v ((CST Sₕ) e') = 0`. So
`Cdual S (CST Sₕ) v ∈ (L0')^⊥` (where `⊥` is w.r.t. `λ`). The
Lagrangian condition `S.L1_isotropic_L0'` says `λ(L1, L0') = 0`, i.e.
`L1 ⊆ (L0')^⊥`. By the perfect-pairing dimension count (`L1 ↔ L1'`
and `L0 ↔ L0'` both perfect, `L1 ⊕ L0 = E`, `L1' ⊕ L0' = E'`),
`(L0')^⊥ = L1`. So `Cdual S (CST Sₕ) v ∈ L1`.

(Alternatively, prove `(L0')^⊥ = L1` directly using
`L1_paired.injective_left` + dimension; or prove `Cdual S (CST Sₕ) v ∈ L1`
without going through `(L0')^⊥` at all by using
`Submodule.IsCompl.eq_of_le_of_finrank_eq` style reasoning.)

**Proof outline for the two sorries:**

```lean
  -- Continuing after `hv_in_kerX0` at line 530:

  -- (Sₕ injective ⇒ projL1' e' = 0 in L1')
  have hproj_e' : (projL1' S e' : S.L1') = 0 := Sₕ.injective <| by
    -- Sₕ (projL1' e') = 0 in Vplus follows from `hSh_zero`
    -- combined with Vplus.subtype injectivity.
    have : (Sₕ (projL1' S e') : S.Vplus) = 0 := by
      apply Submodule.coe_injective_of_subtype_injective
        S.Vplus.injective_subtype.mp
      simpa using hSh_zero
    rw [map_zero]
    exact_mod_cast this  -- coerce L1'.subtype injectivity through

  -- Wait — Sₕ is `S.L1' ≃ₗ[F] S.Vplus`, so `Sₕ x = 0 ⇔ x = 0`.
  -- The cleaner path:
  have hproj_e'_zero : projL1' S e' = (0 : S.L1') := by
    apply Sₕ.injective
    rw [map_zero]
    -- Reduce `(Sₕ (projL1' e') : S.V0) = 0` to `Sₕ (projL1' e') = 0`
    -- via `S.Vplus.subtype.injective`.
    exact Subtype.ext hSh_zero  -- or similar coerce step

  -- Now `e' ∈ L0'` because projL1' e' = 0 in E':
  have he'_in_L0' : (e' : S.E') = (projL0' S e' : S.E') := by
    have hsum := projL1'_add_projL0'_eq S e'  -- helper from Orbits.lean!
    -- ↑(projL1' e') + ↑(projL0' e') = e'
    -- With ↑(projL1' e') = 0 (subtype-coerce hproj_e'_zero):
    have : ((projL1' S e' : S.L1') : S.E') = 0 := by
      rw [hproj_e'_zero]; rfl
    linarith  -- no, in F-vector space need linear_combination or ring
    -- Actually: rw [← hsum, this, zero_add]

  -- ((Sub-helper for `Cdual (CST Sₕ) v ∈ L1`)) — extract as new private lemma:
  have h_Cdual_in_L1 : Cdual S (CST S Sₕ) v ∈ S.L1 := by
    -- Use perfect pairing's `bijective_right` on L0 ↔ L0' to get L1 = (L0')^⊥
    -- (or build a more direct argument). See sketch below.
    sorry  -- to be expanded

  -- Now `hx1 : Cdual S (CST Sₕ) v + (T (projL0' S e') : S.E) = 0`.
  -- LHS first summand in L1, second summand in L0 (since T : L0' → L0).
  -- IsCompl L1 L0 ⇒ both summands are 0.
  have h_disj : Disjoint S.L1 S.L0 := S.isComplL.disjoint
  have h_first_zero : Cdual S (CST S Sₕ) v = 0 := by
    -- ... use h_Cdual_in_L1, hT_in_L0, hx1, h_disj.
    sorry
  have h_second_zero : (T (projL0' S e') : S.E) = 0 := by
    have := hx1
    rw [h_first_zero, zero_add] at this
    exact this

  -- v = 0: from `h_first_zero`, `hv_in_kerX0`, and Cdual restricted to ker X0
  -- being injective via `sDual_restrict_ker_isIso`.
  have hv_zero : v = 0 := by
    -- Build a `DualTransposeData` for (S, S.lambda, S.L1, S.L1', Sₕ).
    -- Tdual := Cdual (S.Vplus.subtype ∘ₗ Sₕ.toLinearMap) -- no, just Cdual (CST Sₕ).
    -- pairing_eq follows from Cdual_pairing_eq.
    -- range_le_L1 follows from `h_Cdual_in_L1` (range Cdual ⊆ L1).
    -- finrank_L1_eq follows from `S.L1_paired` + perfect pairing.
    -- Then sDual_restrict_ker_isIso gives ker X0 ≃ L1 via `Cdual ∘ subtype`.
    -- Injectivity of that map on ker X0 forces v = 0 from h_first_zero.
    sorry

  -- Now close the two structural sorries:
  refine ⟨trivial, ?_, ?_⟩
  · -- Goal: v ∈ ⊥
    rw [hv_zero]; exact Submodule.zero_mem _
  · -- Goal: e' ∈ map L0'.subtype (ker T)
    rw [Submodule.mem_map]
    refine ⟨projL0' S e', ?_, ?_⟩
    · -- projL0' e' ∈ ker T
      rw [LinearMap.mem_ker]
      apply Submodule.coe_injective_of_subtype S.L0  -- or similar coerce
      -- (T (projL0' e') : E) = 0 by h_second_zero
      simpa using h_second_zero
    · -- L0'.subtype (projL0' e') = e'
      exact he'_in_L0'.symm
```

(The above is a *sketch*. The prover should pick the cleanest formulation
— in particular, the `h_Cdual_in_L1` lemma and `hv_zero` step both want a
genuine `DualTransposeData` instance. See "Helper to extract" below.)

**Helper to extract (private, near `kerXST_submod_le_ker`):**

```lean
/-- For any `v : S.V0`, the Cdual of `CST Sₕ` lands in `L1`. This is the
content of the cross-isotropy `S.L1_isotropic_L0'`: `Cdual (CST Sₕ) v`
pairs to zero with every `L0'` element (because `CST Sₕ` zeros on `L0'`),
hence lies in `(L0')^⊥ = L1` (where the equality uses the perfect
pairings `L1 ↔ L1'` / `L0 ↔ L0'` and the cross-isotropy). -/
private lemma Cdual_CST_mem_L1 (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (v : S.V0) :
    Cdual S (CST S Sₕ) v ∈ S.L1 := by
  sorry
```

The cleanest way to prove `(L0')^⊥_λ = L1` may be via a custom small lemma
"if `λ(x, l') = 0` for all `l' ∈ L0'`, then `x ∈ L1`", proved directly
from `L1 ⊕ L0 = E` and `L0 ↔ L0'` perfect (so any `l ∈ L0` with
`λ(l, l') = 0` for all `l' ∈ L0'` must be 0). The decomposition gives
`x = x_L1 + x_L0`, and pairing both sides with `l' ∈ L0'`:
`λ(x_L1, l') + λ(x_L0, l') = 0`. By `L1_isotropic_L0'`, `λ(x_L1, l') = 0`
for all `l'`. So `λ(x_L0, l') = 0` for all `l' ∈ L0'`, and `L0_paired`'s
left injectivity gives `x_L0 = 0`. Hence `x = x_L1 ∈ L1`.

**Helper to extract (`DualTransposeData` instance):**

```lean
/-- The `DualTransposeData` for `S.lambda`, `S.L1`, `S.L1'` with
`Tdual := Cdual S (CST S Sₕ)`, witnessed by an iso `Sₕ : L1' ≃ Vplus`
and the in-place Lagrangian conditions. -/
private noncomputable def kernelImage_DTD (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) :
    DualTransposeData S.toX0Setup S.lambda S.L1 S.L1'
      ((S.Vplus.subtype ∘ₗ (Sₕ : S.L1' →ₗ[F] S.Vplus)).comp
        S.L1'.subtype) := by  -- check the exact T-shape needed
  sorry
```

Then `sDual_restrict_ker_isIso S.toX0Setup hNondeg S.lambda
S.lambda_isPerfPair S.L1 S.L1' (?finrank-condition) Sₕ kernelImage_DTD`
gives the iso `ker X0 ≃ L1` whose `Tdual` is the dual transpose of `Sₕ`.

Note the finite-rank condition `Module.finrank F L1' = c S` (the third
argument to `sDual_restrict_ker_isIso`): this follows from
`L1_paired.injective_right.finrank_eq` + `c_eq_finrank_quotient` + the
identification `Vplus ≃ V0 / range X0`. Worth packaging as a small
helper.

#### 1c. Close `kernelImage_im` (line 595)

**Target:** `kernelImage_im` (line 590).

**Statement** (already uses `Sₕ : LinearEquiv`):
```lean
theorem kernelImage_im
    (_hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.range (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) =
      imXST_submod S (Sₕ : S.L1' →ₗ[F] S.Vplus) T := by
  sorry
```

Need both directions:

##### `imXST_submod ⊆ range XST` (constructive forward direction)

Given `(a, b, 0) ∈ imXST_submod` with:
- `a ∈ S.L1 ⊔ (LinearMap.range T).map S.L0.subtype`,
- `b ∈ ⊤` (i.e. `b : S.V0`).

Construct a preimage `(e, v, e') ∈ S.V` with `XST(e, v, e') = (a, b, 0)`.

By `Submodule.mem_sup`, write `a = a_L1 + a_T` with `a_L1 ∈ L1` and
`a_T ∈ map L0.subtype (range T)`. Pick `l ∈ L0'` with `T l = a_T`'s
preimage (i.e. `(T l : E) = a_T`).

Use `sDual_restrict_ker_isIso` (now applicable with the helper from 1b)
to get `φ : ker X0 ≃ L1` such that `φ⁻¹(a_L1) = w_L1 ∈ ker X0`. Then:
- `v := w_L1 + Sₕ⁻¹(b - X0(...))` — actually need to think carefully.

Cleanest setup: split `b = b_Vplus + X0 v_pre` for some `v_pre : V0` via
`S.isCompl : IsCompl S.Vplus (range X0)`. Set `v_X0 := v_pre`, choose
`l1' ∈ L1'` with `Sₕ l1' = b_Vplus` (use `Sₕ.symm`). Then take `e' :=
(l1' : E') + (l : E')` (so `projL1' e' = l1'`, `projL0' e' = l`).

Take `v := w_L1 + v_X0` where `w_L1` is a preimage of `a_L1 - Cdual(CST
Sₕ)(v_X0) - …` under `Cdual S (CST Sₕ)|_{ker X0}`. Wait — this is getting
tangled. Better: choose `v` and `e'` first, then `e` is free (use `e := 0`).

Let `e' := (Sₕ.symm b_Vplus : E') + (l : E')` where `l : L0'` chosen with
`(T l : E) = a_T`. Then:
- `Sₕ (projL1' e') = b_Vplus` (V0-component of `Sₕ` part).
- `(T (projL0' e') : E) = a_T`.

Now solve `XST(e, v, e') = (a, b, 0)` for `(e, v)`:
- `Cdual (CST Sₕ) v + a_T = a_L1 + a_T`, i.e. `Cdual (CST Sₕ) v = a_L1`.
  Use `φ : ker X0 ≃ L1` to find `v ∈ ker X0` with `φ v = a_L1`, but
  `φ v = D.Tdual v = Cdual (CST Sₕ) v` if the `DualTransposeData` is set
  up right.
- `X0 v + b_Vplus = b`, i.e. `X0 v = b - b_Vplus`, but `b - b_Vplus ∈
  range X0` by the `IsCompl S.Vplus (range X0)` decomposition.

Two constraints on `v`: `Cdual (CST Sₕ) v = a_L1` and `X0 v = b -
b_Vplus`. Need a shared `v` satisfying both. The first forces
`v ∈ ker X0` (because `φ : ker X0 ≃ L1` and `a_L1 ∈ L1`)? No — `φ`
restricts `Cdual` to `ker X0`, but `Cdual (CST Sₕ) : V0 → E` is defined
on all of `V0`, not just `ker X0`. We need to verify whether `Cdual (CST
Sₕ) v` only depends on `v mod range X0`, then split.

Actually `Cdual_pairing_eq` says
`λ(Cdual (CST Sₕ) v, e') = -formV0 v ((CST Sₕ) e')`. The kernel of this
linear map (as a function of `v`) is `(image of CST Sₕ)^⊥_{formV0}`,
which is `(Vplus)^⊥_{formV0}` (since `CST Sₕ` lands in `Vplus`). By the
`vplusKerPairing_isPerfPair` (X0Geometry), `Vplus^⊥_{formV0}` modulo
something equals `range X0` (I think).

This is getting complicated. Let me instead suggest: **use the
`DualTransposeData` helper from 1b** to package the iso `ker X0 ≃ L1`,
and decompose `V0 = ker X0 ⊕ V_section` for some complement `V_section`
(pick any). On `ker X0`, `Cdual (CST Sₕ)` is the iso `φ`. Outside `ker
X0`, `Cdual (CST Sₕ)` is *not* an iso (it sends V_section to L1 or
L1?... need to check).

Hmm, `Cdual (CST Sₕ)` lands in L1 always (per helper from 1b), so it's a
map `V0 → L1`. Its restriction to `ker X0` is an iso to `L1` (by
`sDual_restrict_ker_isIso`). So `Cdual (CST Sₕ)` is *surjective* onto
`L1` (with kernel containing `range X0` — wait, the map from `V0/ker(map
to L1)` is the iso, so the kernel of `V0 → L1` is exactly `(ker X0)^⊥` in
some sense. Actually if `restriction to ker X0` is bijective onto L1,
then the *full* map factors through `V0 → V0/(some complement) → L1`
where the complement is *not* ker X0 but rather the kernel of the full
map. Bottom line: surjective `V0 ↠ L1` with kernel of dimension `dim V0
- dim L1`. Not ker X0 in general.

OK this is complicated. The prover should consult the blueprint
construction for the forward direction of `kernelImage_im` carefully. The
informal sketch is in `informal/normalform.md` (light on detail) and the
blueprint `references/blueprint_verified.md` `prop:kernel-image`.

**Simplification:** the forward direction uses `b ∈ ⊤` (so `b : V0`
arbitrary). Choose `v ∈ ker X0` such that `Cdual (CST Sₕ) v = a_L1`
(possible by `sDual_restrict_ker_isIso`). Then `X0 v = 0`. So we need
`b = Sₕ (projL1' e')`, i.e. `Sₕ (projL1' e') = b`. But `Sₕ : L1' →
Vplus`, not `L1' → V0`. So we need `b ∈ Vplus`.

**The `b ∈ ⊤` claim is too strong.** Either:
- The `imXST_submod` definition (line 548–552) has `Submodule.prod ⊤ ⊥`
  as the `(V0, E')` factor, i.e. `b : V0` is arbitrary, `e' = 0`.
  But then `(a, b, 0) = XST(e, v, e')` requires
  `X0 v + Sₕ (projL1' e') = b` with `e' = 0`, i.e. `X0 v = b`. So
  `b ∈ range X0`. But the spec says `b ∈ ⊤`. So `range X0 = V0`?
  No — `range X0 ⊕ Vplus = V0` and `Vplus` is non-trivial.

There may be a subtle issue with the `imXST_submod` definition. Look at
the blueprint description: "`Im X_{S,T} = (L1 ⊕ Im T) ⊕ V₀`". The
"`⊕ V₀`" part means the full `V0` factor *but* it gets there via `X0 v +
Sₕ(projL1' e')`. So a value `b ∈ V0` is decomposed `b = b_range + b_Vplus`
with `b_range ∈ range X0` and `b_Vplus ∈ Vplus`. Then `X0 v = b_range`
(pick `v` with `X0 v = b_range`) and `Sₕ (projL1' e') = b_Vplus` (pick
`l1' = Sₕ.symm b_Vplus`, then `(l1' : E') ∈ E'` has `projL1' = l1'`).

With both `v` (for `b_range`) and `e'` (for `b_Vplus` plus the `T` part)
determined, the V0 component of `XST(e, v, e')` is
`X0 v + (Sₕ (projL1' e') : V0) = b_range + b_Vplus = b`. ✓

For the E component: `Cdual (CST Sₕ) v + (T (projL0' e') : E) = a`. We
have a fixed `v` (chosen for the V0 component) and need `e'`'s `L0'`
part. Adjust `(T (projL0' e') : E) = a - Cdual (CST Sₕ) v`.

We need `a - Cdual (CST Sₕ) v ∈ map L0.subtype (range T) ⊆ L0`. We have
`a = a_L1 + a_T` with `a_T ∈ map L0.subtype (range T)`. And `Cdual (CST
Sₕ) v ∈ L1` (helper from 1b). So `a - Cdual (CST Sₕ) v = (a_L1 - Cdual
(CST Sₕ) v) + a_T`. The first parenthesis is in L1, the second in
`map L0.subtype (range T) ⊆ L0`. By `IsCompl L1 L0`, the L1 piece must
vanish for `a - Cdual (CST Sₕ) v` to be in `L0`.

**Forced:** `Cdual (CST Sₕ) v = a_L1`. With `v ∈ ker X0` (so `X0 v = 0`),
the iso `ker X0 ≃ L1` from `sDual_restrict_ker_isIso` gives a unique
preimage. But we already used `v` for the `b_range` part — so we need a
*different* `v`. **Re-decomposition:**

The right decomposition: `v = v_ker + v_section` with `v_ker ∈ ker X0`
(carries the L1 mass via `Cdual (CST Sₕ) v_ker = a_L1`) and `v_section`
chosen so `X0 v_section = b_range`. The full `X0 v = b_range` since
`X0 v_ker = 0`. The full `Cdual (CST Sₕ) v = Cdual (CST Sₕ) v_ker + Cdual
(CST Sₕ) v_section = a_L1 + Cdual (CST Sₕ) v_section`. We need this to
equal `a_L1`, i.e. `Cdual (CST Sₕ) v_section = 0`. But `Cdual (CST Sₕ)`
is *not* zero on `range X0` in general.

**Alternative:** absorb the `Cdual (CST Sₕ) v_section` term into `e'`'s
`L0'` part:
`(T (projL0' e') : E) = a - Cdual (CST Sₕ) v = a - (a_L1 + Cdual (CST Sₕ)
v_section) = (a_T) - Cdual (CST Sₕ) v_section`.

This needs to be in `L0`. `a_T ∈ L0`, and `Cdual (CST Sₕ) v_section ∈ L1`
(helper). Difference is `(a_T) - (Cdual (CST Sₕ) v_section) ∈ L0 + L1 =
E`, but not necessarily in `L0` alone. **Stuck again.**

The actual fix: **choose `v_section = 0`**, i.e. take `v := v_ker` so
that `X0 v = 0`, and make `Sₕ (projL1' e')` carry the *entire* `b` (not
just `b_Vplus`). But `Sₕ` lands in `Vplus`, not `V0`, so this only works
if `b ∈ Vplus`, contradicting `b ∈ ⊤`.

This suggests **the `imXST_submod` definition is wrong** (or at least
inconsistent with the construction). Ahhh — actually, look again at line
551–552:
```lean
  Submodule.prod (S.L1 ⊔ (LinearMap.range T).map S.L0.subtype)
    (Submodule.prod ⊤ ⊥)
```
The structure of `S.V = E × V0 × E'`. So `imXST_submod` is `(L1 ⊔ image
T) × ⊤ × ⊥`. The `⊤` is the full `V0`. The `⊥` is the trivial `E'`.

Re-examining: with `e' = 0`, we have `projL1' e' = 0` and `projL0' e' =
0`, so `XST(e, v, 0) = (Cdual(CST Sₕ) v, X0 v, 0)`. The image as `e, v`
range over `E × V0` is `{(Cdual(CST Sₕ) v, X0 v, 0) | v ∈ V0} +
{(e, 0, 0) | e ∈ E}` — the latter is `E × 0 × 0` ⊆ `imXST_submod`. The
former is `{(L1, V0_image, 0)}`-shaped where `V0_image := range X0`.
Adding gives `(E + L1, V0 + range X0, 0) = (E, range X0, 0)` — *not*
`(L1 ⊔ image T, ⊤, 0)`.

So for `b ∉ range X0` (i.e. `b` has a `Vplus` component), we need `e' ≠
0` to capture it via `Sₕ (projL1' e')`. But this also adds `T (projL0'
e') ∈ L0` to the E component, requiring `a` to have an `image T`
component to absorb it.

The full picture: parametrize by `(e, v, e')`, get
`XST = (Cdual(CST Sₕ) v + T(projL0' e'), X0 v + Sₕ(projL1' e'), 0)`.
Range:
- E component: `Cdual(CST Sₕ)(V0) + T(L0') = L1 + image T` (since
  `Cdual(CST Sₕ)(V0) ⊆ L1` by 1b helper, and equality holds because
  `Cdual(CST Sₕ)|ker X0` is iso to L1).
- V0 component: `X0(V0) + Sₕ(L1') = range X0 + Vplus = ⊤` (full V0 by
  `S.isCompl`).
- E' component: 0.

So **range = `(L1 + image T) × ⊤ × 0`** ⊇ `imXST_submod`. The forward
direction `imXST_submod ⊆ range`: given `(a, b, 0)` with `a ∈ L1 + image
T`, `b ∈ V0`, construct preimage:
- Decompose `b = X0 v_b + Sₕ(l1')` with `v_b ∈ V0` (any preimage; e.g.
  `v_b ∈ V_section` for some complement of `ker X0`) and `l1' ∈ L1'`.
- Decompose `a = a_L1 + a_T`. Find `v_a ∈ ker X0` with `Cdual(CST Sₕ)
  v_a = a_L1` (sDual iso). Find `l ∈ L0'` with `(T l : E) = a_T`.
- Set `v := v_a + v_b - (some adjustment)`, `e' := (l1' : E') + (l : E')`,
  `e := -Cdual(CST Sₕ)(v_b)` (to cancel the spurious `Cdual(CST Sₕ) v_b`
  term that would land in L1 via `v_b`).
  - Wait: `XST(e, v, e').1 = Cdual(CST Sₕ) v + T(projL0' e')`. There's
    no `e` contribution to component 1. `XST` ignores `e`! Looking at
    `XST_apply` again: `(Cdual (CST Sₕ) v + (T (projL0' e') : E),
    X0 v + (Sₕ (projL1' e') : V0), 0)`. Right, no `e`.
  - So `XST(e, v, e').1 = Cdual(CST Sₕ) v + T(projL0' e')` regardless of
    `e`. The `e` is "free" and absorbed into the image without affecting
    the output.
  - Wait that means `(e, v, e') ↦ XST(e, v, e')` does not see `e` at
    all. That's strange — let me re-check.

Looking at `XCB` definition (Slice.lean, line 110+):
```lean
inE ∘ₗ ((Cdual S C) ∘ₗ projV0 + B ∘ₗ projE') +
  inV0 ∘ₗ (S.X0 ∘ₗ projV0 + C ∘ₗ projE')
```
The `inE` is `LinearMap.inl F E (V0 × E')`, the `projV0` is "first of
second", the `projE'` is "second of second". Indeed there is no `projE`,
so the `e` component is dropped.

So `XST(e, v, e') = (Cdual(CST Sₕ) v + T(projL0' e'), X0 v + Sₕ(projL1' e'), 0)`
ignores `e`. The image is exactly the set described above, and the
preimage is **non-unique** in `e` (the kernel always has `e ∈ E`
free).

For the forward direction proof: pick `e := 0` (anything works), `v :=
v_a + v_b`, `e' := (l1' : E') + (l : E')`. Verify the three components.

OK so the construction is feasible — the prover just needs careful
bookkeeping. The above sketch should be enough.

##### `range XST ⊆ imXST_submod` (reverse direction)

Given `XST(e, v, e') = (a, b, c)`, show:
- `c = 0` (immediate from XST_apply, since the third component is always 0).
- `a ∈ L1 + image T` (use the `Cdual(CST Sₕ) v ∈ L1` helper from 1b plus
  `T(projL0' e') ∈ image T`).
- `b ∈ ⊤` (trivially).

This direction is direct from `XST_apply` + the helper, no new
infrastructure needed.

#### Acceptance criteria for objective 1

- `kernelImage_ker` (line 495) is sorry-free, signature uses
  `Sₕ : S.L1' ≃ₗ[F] S.Vplus`.
- `kernelImage_im` (line 590) is sorry-free.
- `kernelImage_dim` call site at line 611 updated to pass `Sₕ` directly
  (no explicit coercion to LinearMap).
- New private helper `Cdual_CST_mem_L1` (or equivalent) added.
- New private `DualTransposeData` instance (e.g. `kernelImage_DTD`)
  added.
- `lake env lean InducedOrbitToy/NormalForm.lean` produces only the 3
  remaining `sorry` warnings (lines 195, 319, 348 — Round 6 work).
- `lake build` is green at end of round.
- No new `axiom` declarations; `#print axioms kernelImage_ker` /
  `kernelImage_im` / `kernelImage_dim` shows only `[propext,
  Classical.choice, Quot.sound]`.
- `pNormalForm`, `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build`, `pNormalForm_residual_orbit_iso`,
  `IsParabolicElement` signatures and proof structures **unchanged**
  (only `kernelImage_*` and `kernelImage_dim`'s call site are touched).
- Stale comments at lines 344, 357 that reference the old
  `L0_isotropic` field can be left for Round 6 (they don't break
  anything; refresh in the `residual_levi_build` work).

#### Informal references

- Blueprint: `references/blueprint_verified.md` `prop:kernel-image`
  (lines 321–411).
- Per-file informal sketch: `.archon/informal/normalform.md`
  (light on `kernelImage_*` detail; consult the blueprint for proof
  structure).

### Files NOT assigned this round

The following files have remaining sorries but are blocked by Round 6+
work. **Do not assign provers to them this round.** If the harness
dispatches a prover anyway, the prover should:
- verify the file compiles in isolation (`lake env lean
  InducedOrbitToy/<File>.lean`),
- write a brief "no work" `task_results/<File>.md`, and
- **not edit anything**.

- `InducedOrbitToy/Basic.lean` — already done (Round 4); no work.
- `InducedOrbitToy/X0Geometry.lean` — already done (session 4); no work.
- `InducedOrbitToy/Slice.lean` — already done (Round 4); no work this
  round (Round 6 will add Levi machinery additively to this file).
- `InducedOrbitToy/LocalForms.lean` — already done; no work.
- `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion` is
  Round 7 (needs `pNormalForm_residual_orbit_iso` fully closed via
  Round 6's Levi machinery).

## Coordination notes for Round 5 (parallel-safety)

Round 5 is **single-file** (NormalForm.lean only). No cross-file cascade.
The Tier S #4 signature change to `kernelImage_ker` only affects its sole
caller `kernelImage_dim` (also in NormalForm.lean), no external file.

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
- **(NEW Round 4) `IsSkewAdjoint` closure proofs over generic `[Field
  F]`:** use `linear_combination hf + hg` (add) / `linear_combination c
  * hf` (smul). **Do not use `linarith`** — it requires `LinearOrderedField`
  and fails over generic `Field`.
- **(NEW Round 4) `Submodule.IsCompl.projection_add_projection_eq_self`**
  (not `linearProjOfIsCompl_add_…`, which leansearch suggests but
  **does not exist** in current Mathlib) combined with
  `Submodule.IsCompl.projection_apply` to bridge between the
  `IsCompl.projection` and `linearProjOfIsCompl`-coerced-subtype forms.
- **(NEW Round 4) `conv_lhs => rw [...]`** to scope a rewrite to the LHS
  only when bare `rw [← h]` would over-rewrite (e.g. rewriting `v` while
  `projL0' v` appears as a sub-expression on the RHS).
- **(NEW Round 4) Cross-file 4-tuple cascade:** when a structure or
  predicate gains a new conjunct, every `obtain ⟨...⟩` and `refine
  ⟨..., ?_⟩` site that constructs/destructs the value needs a parallel
  arity bump. Plan-agent allocated parallel provers; mid-round build
  breakage was expected and resolved at end-of-round.

## Reporting

Each prover writes `.archon/task_results/<File>.md` with:
- which sorries were closed (line numbers + theorem names);
- which statements were *changed* (definitions, hypothesis lists, etc.);
- exact Mathlib lemmas used;
- remaining subgoals and notable failed attempts (so the plan agent does
  not repeat dead ends);
- confirmation that the assigned file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`);
- confirmation that `lake build` is green **at end of round**;
- confirmation that no `axiom` was introduced
  (`#print axioms` for each public theorem in the file).
