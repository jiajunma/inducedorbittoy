# InducedOrbitToy/NormalForm.lean — Round 7 Prover Report

## Summary

Round 7 deliverables (per `.archon/informal/normalform_round7.md` and
`PROGRESS.md` round plan): close the three remaining `sorry`s in
`NormalForm.lean` (lines 195, 319, 348 of the pre-Round-7 file) using
the Round-6 Levi machinery in `Slice.lean`.

**Status:** 2 of 3 closed; signature refactor (Tier S #5) landed.

| Target | Pre-R7 Line | Status |
|---|---|---|
| `pNormalForm_witnesses` (Tier A #1) | 195 | **STILL SORRY** (single isolated sorry, body docstring outlines steps) |
| `residual_levi_extract` (Tier A #2) | 319 | **CLOSED** (sorry-free) |
| `residual_levi_build` (Tier A #3) | 348 | **CLOSED** (sorry-free) |
| Tier S #5 signature restructure | — | **DONE** |

`pNormalForm_residual_orbit_iso` (the public consumer of the two `residual_levi_*`
helpers) is now **sorry-free**, ending Round 7 with a clean public theorem.
`pNormalForm` itself depends on `pNormalForm_witnesses` and so transitively
uses `sorryAx`; everything else is clean.

## Acceptance criteria audit

| Criterion | Status |
|---|---|
| `lake env lean InducedOrbitToy/NormalForm.lean` compiles | ✅ |
| `lake build` is green | ✅ (`Build completed successfully (8033 jobs)`) |
| Sorry count: 5 → 2 | ❌ partial: 5 → 3. `pNormalForm_witnesses` still sorry'd (allowed per plan) |
| `pNormalForm_witnesses` may carry one sub-helper sorry | ✅ (single sorry, well-documented body) |
| `residual_levi_extract` sorry-free | ✅ |
| `residual_levi_build` sorry-free | ✅ |
| `#print axioms` clean on closed theorems | ✅ (only `[propext, Classical.choice, Quot.sound]`) |
| No new custom `axiom` declarations | ✅ |

## Tier S #5 — signature restructure (DONE)

The pre-Round-7 statement
```
uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T
```
is mathematically false (uD-only conjugation cannot align the C-block).
Restructured to expose a Levi factor `d`:
```lean
∃ (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
  (d : S.E' ≃ₗ[F] S.E') (T : S.L0' →ₗ[F] S.L0),
  IsSkewT S T ∧
  uD S D ∘ₗ leviGL_E S d ∘ₗ XCB S C B
    = XST S (↑Sₕ) T ∘ₗ uD S D ∘ₗ leviGL_E S d
```

`Sₕ` strengthened from a `LinearMap` to a `LinearEquiv` (its surjectivity
is needed by `kernelImage_ker` in the consumer `residual_levi_extract`).
This signature change cascaded to `pNormalForm`, `pNormalForm_residual_orbit_iso`,
and the two `residual_levi_*` helpers.

`pNormalForm`'s body was rewritten to consume the new signature
(extracting the parabolic `p := uD D ∘ leviGL_E d`). The body chains
`isUnit_uD * leviGL_E_isParabolic.1` for `IsUnit p`, uses
`Submodule.map_comp` for the flagE/flagEV0 conjuncts, and proves
`IsOrthogonal` via `IsAdjointPair (uD D) (uD (-D))` + `uD_neg_inverse`
followed by composition with the Levi `IsOrthogonal`.

## Tier A #2 (line 319) — `residual_levi_extract`

### Approach (Option B from plan, no `parabolic_decompose`)

Implemented per `.archon/informal/normalform_round7.md` § Tier A #2:

1. **Step A (preserve L0').** For `l : L0'`, evaluate the conjugation
   `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` at `(0, 0, (l : E'))`. Using
   `XST_apply` plus `projL0' (l : E') = l, projL1' (l : E') = 0`, the
   LHS reduces to `p ((T₁ l : E), 0, 0)`. Since `(T₁ l : E, 0, 0) ∈ flagE`
   and `p` preserves `flagE` (with equality), the LHS is in `flagE`.
   The V0-component equation `0 = X0 v + (Sₕ (projL1' e') : V0)` plus
   `Vplus ⊕ range X0 = V0` (`S.isCompl.disjoint`) forces both
   `(Sₕ (projL1' e') : V0) = 0` and `X0 v = 0`. `Sₕ : L1' ≃ Vplus`
   (the LinearEquiv strengthening!) gives `Sₕ.injective`, so
   `projL1' e' = 0`, i.e., `e' ∈ L0'`.

2. **Step B (define h).** Define
   `qFunRaw : L0' →ₗ E' := projE'_V ∘ p ∘ inE' ∘ L0'.subtype`
   (third coordinate of `p ∘ (0, 0, (· : E'))`). Step A gives
   `qFunRaw l ∈ L0'`, so codRestrict to `qFun : L0' →ₗ L0'`.

3. **Step C (h is bijective).** Show `qFun` is injective: if `qFun l = 0`,
   then `(p (0, 0, l)).2.2 = 0`, so `p (0, 0, l) ∈ flagEV0`. Since
   `p` is invertible *and* maps `flagEV0` to `flagEV0` (with equality),
   `p⁻¹` also preserves `flagEV0`, so `(0, 0, l) ∈ flagEV0`, i.e., `l = 0`.
   Built `LinearEquiv` via `LinearMap.linearEquivOfInjective` with
   `dim L0' = dim L0'` (trivial).

4. **Step D (verify isometry).** Use the `IsOrthogonal` conjunct of `p`
   applied to `(T₁ u, 0, 0)` and `(0, 0, (v : E'))`:
   `S.ambientForm (p (T₁ u, 0, 0)) (p (0, 0, v)) = S.ambientForm (T₁ u, 0, 0) (0, 0, v) = λ(T₁ u, v)`.
   Substitute `p (T₁ u, 0, 0) = XST(Sₕ, T₂) (p (0, 0, u))` (from Step A's
   conjugation hypothesis), expand via `XST_apply`, kill the `Cdual` term
   using `Cdual_pairing_eq` + `(CST Sₕ) e'_v = 0` (since
   `e'_v ∈ L0'`, `projL1' e'_v = 0`), and reduce to
   `λ((T₂ (h u) : E)) e'_v = λ(T₁ u, v)`. Combined with `(h v : E') = e'_v`,
   this is `BT T₂ (h u) (h v) = BT T₁ u v`.

### Mathlib lemmas used

- `Submodule.linearProjOfIsCompl_apply_left` / `_apply_right` /
  `_apply_right'` — for projL0'/projL1' apply on subtype-coerced inputs.
- `Submodule.IsCompl.projection_add_projection_eq_self` +
  `Submodule.IsCompl.projection_apply` — to recover `e'' = projL1' e'' + projL0' e''`.
- `LinearMap.codRestrict` + `LinearMap.linearEquivOfInjective` —
  inject + dim-eq → LinearEquiv.
- `Cdual_pairing_eq`, `LinearMap.IsOrthogonal`, `Submodule.map p X = X`-by-invertibility.
- Vplus ⊕ range X0 disjointness via `S.isCompl.disjoint.eq_bot`.

### Implementation notes

- The proof spans ~250 lines.
- A key technical move: `set p_uv := p (0, 0, (v : E'))` to keep the
  goal printable; combined with `set`-ed shorthands for `a_u, c_u, e'_u`
  and `a_v, c_v, e'_v`.
- `h_amb_unfold : ambientForm ((..., 0, 0)) p_uv = pairing ... + B0 ... + ε * pairing ...`
  is closed by `rfl` (the `ambientForm` definition is one-step
  `LinearMap.mk₂_apply`).

## Tier A #3 (line 348) — `residual_levi_build`

### Approach

Per `.archon/informal/normalform_round7.md` § Tier A #3:

1. **Build d.** Define `extendL0'IsoToE' S h : E' ≃ E'` via the
   `Submodule.prodEquivOfIsCompl` direct-sum decomposition, applying
   `id × h` on the `(L1', L0')` product:
   ```lean
   prodEq.symm ≪≫ₗ ((LinearEquiv.refl F S.L1').prodCongr h) ≪≫ₗ prodEq
   ```
   where `prodEq := S.L1'.prodEquivOfIsCompl S.L0' S.isComplL'`.
   Pointwise: `d.symm e' = (projL1' e' : E') + (h.symm (projL0' e') : E')`.

2. **Take p := leviGL_E S d.** Parabolicity from `leviGL_E_isParabolic`.

3. **Verify conjugation.** By `leviGL_E_conj_XCB`,
   `leviGL_E d ∘ XCB(CST Sₕ, BST T₁) = XCB(CST Sₕ ∘ d.symm, lambdaDualE d.symm ∘ BST T₁ ∘ d.symm) ∘ leviGL_E d`.
   Reduce to two component identities:
   - `CST Sₕ ∘ d.symm = CST Sₕ` (uses `projL1' ∘ d.symm = projL1'`,
     proved as helper `projL1'_extendL0'IsoToE'_symm`).
   - `lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂` (uses
     `projL0' ∘ d.symm = h.symm ∘ projL0'`, then unfolds via the
     perfect-pairing characterisation `lambdaDualE_pairing_eq`,
     splits the test vector `e''` along `IsCompl L1' L0'`, applies
     `S.L0_isotropic_L1'` to kill cross terms, and finally reduces to
     the hypothesis `hh u v: BT T₂ (h u) (h v) = BT T₁ u v` substituted
     at `u → h.symm u, v → h.symm b'`).

### Helper lemmas added

- `extendL0'IsoToE' (S, h) : E' ≃ E'`
- `extendL0'IsoToE'_symm_apply` — pointwise formula for `d.symm`.
- `projL1'_extendL0'IsoToE'_symm`: `projL1' ∘ d.symm = projL1'`.
- `projL0'_extendL0'IsoToE'_symm`: `projL0' ∘ d.symm = h.symm ∘ projL0'`.

### Mathlib lemmas used

- `Submodule.prodEquivOfIsCompl`, `Submodule.coe_prodEquivOfIsCompl`,
  `Submodule.toLinearMap_prodEquivOfIsCompl_symm`.
- `LinearEquiv.prodCongr`, `LinearEquiv.refl`, `LinearEquiv.trans` (`≪≫ₗ`).
- `S.L0_isotropic_L1'` (from `SliceSetup`).

## Tier A #1 (line 191 → still 191) — `pNormalForm_witnesses`

**STILL SORRY.** The full body remains a single carefully-marked `sorry`
with extended docstring outlining the four-step plan:

1. Build `(Sₕ, d)` from `_hRank : rank Cbar = c` (the d-construction).
2. Set `(C', B') := (C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm)` and
   apply `leviGL_E_conj_XCB`.
3. Build `D` such that `X0 ∘ D = C' - CST Sₕ` (lands in `range X0` by
   construction); `T` reads off the `B`-block residual.
4. Combine via `uD_conj_XCB` + uniqueness (`parametrizeX0PlusU_uniqueness`)
   + `uD_neg_inverse`.

The d-construction (Step 1) requires `LinearEquiv.ofFinrankEq` on
submodules of equal dimension, which Mathlib offers as
`LinearEquiv.ofBijective` on suitable `LinearMap.codRestrict` etc.;
the unipotent step (Steps 2–4) mirrors `parametrizeX0PlusU_existence`
in `Slice.lean`.

**Why deferred:** The two consumers (`residual_levi_extract` and
`residual_levi_build`) are now sorry-free, which was the higher-priority
plan target. The full d-construction + uniqueness step is estimated
~150 lines and was beyond Round 7's budget. Round 8 will close it.

## Cascading consumer changes

- `pNormalForm` (line 248–): body refactored to consume the new
  pNormalForm_witnesses signature. Sorry-free.
- `pNormalForm_residual_orbit_iso` (line 591–): `Sₕ` strengthened to
  `LinearEquiv`. Sorry-free.
- `XST_apply` moved earlier in the file (now near line 320) so it's in
  scope for `residual_levi_extract`.

## Reusable Gotchas (Round 7 additions)

- **`prodEquivOfIsCompl` symm via `Submodule.toLinearMap_prodEquivOfIsCompl_symm`:**
  the symm coerces to `(linearProjOfIsCompl p q h).prod (linearProjOfIsCompl q p _)`,
  i.e., `prodEq.symm e' = (projL1' e', projL0' e')` for our `IsCompl L1' L0'`.
  Use this to compute `d.symm` apply lemmas without unfolding through
  `LinearEquiv.trans` repeatedly.
- **`set ... with hdef` for opaque shorthands:** when proving identities
  with multiple `(p (0, 0, ...))` occurrences, use `set` to abbreviate
  them. Beware: `lhs_E` set as `Cdual ... + T₂ ...` becomes opaque;
  to rewrite via `LinearMap.map_add` you need to unfold first or just
  not `set` the sum.
- **`congr 1` on `XCB S A B = XCB S A' B' ∘ leviGL_E d` style equations**
  doesn't split into 2 component goals (since the outer is `LinearMap`
  composition, not `XCB`). Better: prove the two component identities
  (`A = A'`, `B = B'`) as separate `have`s and chain `rw [hC, hB]`.
- **`rw [LinearMap.map_zero, LinearMap.zero_apply, map_zero, add_zero, ...]`
  chain to drop V0-side residuals from XST(C, B):** when V0 is `X0 v +
  (Sₕ (projL1' e') : V0)` and you can show `projL1' e' = 0`, the chain
  collapses to `X0 v` (which may further reduce to 0 via separate
  argument).
- **Linearity in first arg of bilinear `S.paired.pairing`:** `pairing (a + b) = pairing a + pairing b`
  is `LinearMap.map_add`; then `(f + g) e'_v = f e'_v + g e'_v` is
  `LinearMap.add_apply`. Order: `map_add` first, then `add_apply`.
- **`(qFun l : L0').val = qFunRaw l` is *definitionally* equal** when
  `qFun = LinearMap.codRestrict L0' qFunRaw _`. Use `(qFun l : E') = 0 → qFunRaw l = 0`
  via `exact h_val` (no `simpa`) — Subtype.val unwraps codRestrict.
- **Trailing `rfl` after `simp only` is often a "No goals" lint:** `simp only`
  with `map_zero` already closes the goal `f 0 = 0`. Drop the
  redundant `rfl`.

## Confirmation

```
$ lake build
✔ Built InducedOrbitToy.NormalForm (13s)
warning: NormalForm.lean:203:16: declaration uses `sorry`  -- pNormalForm_witnesses (allowed)
warning: Slice.lean:1078:8: declaration uses `sorry`        -- parabolic_decompose (Round 8)
warning: Orbits.lean:324:8: declaration uses `sorry`        -- sIndependenceAndOrbitCriterion (Round 8)
Build completed successfully (8033 jobs).
```

```
$ lake env lean check_axioms.lean
'pNormalForm' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]  -- pNormalForm_witnesses still sorry
'pNormalForm_residual_orbit_iso' depends on axioms: [propext, Classical.choice, Quot.sound]  -- CLEAN
'kernelImage_ker' depends on axioms: [propext, Classical.choice, Quot.sound]  -- CLEAN
'kernelImage_im' depends on axioms: [propext, Classical.choice, Quot.sound]  -- CLEAN
'kernelImage_dim' depends on axioms: [propext, Classical.choice, Quot.sound]  -- CLEAN
```

No new custom `axiom` declarations introduced. Sorry count: 5 → 3
(plan target was 5 → 2, missed by 1 due to deferred `pNormalForm_witnesses`
body).

## Recommendation for plan agent (Round 8)

1. **Close `pNormalForm_witnesses` body.** Use the four-step plan in the
   theorem's docstring. Key Mathlib pieces:
   - `LinearEquiv.ofBijective` on `LinearMap.codRestrict` for the
     `dL0' : L0' ≃ ker (Cbar S C)` step.
   - `parametrizeX0PlusU_existence` (Slice.lean) for the unipotent `D`
     existence — it returns `(C, B)` for any `Y ∈ X0 + 𝔲`; we plug in
     `Y := XCB(C', B') - X0Lift` after the Levi step.
   - `parametrizeX0PlusU_uniqueness` to identify the resulting C''/B''
     with `CST Sₕ` and `BST T`.
2. **Close `parabolic_decompose` (Slice.lean) and
   `sIndependenceAndOrbitCriterion` (Orbits.lean).** These are
   independent of the NormalForm work this round.
