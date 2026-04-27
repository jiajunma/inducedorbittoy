# Round 7 plan for `InducedOrbitToy/NormalForm.lean`

This file specifies the work for closing the three remaining sorries in
`InducedOrbitToy/NormalForm.lean` (lines 195, 319, 348) using the Levi
machinery that Round 6 added to `Slice.lean`.

## Authoritative inputs

- Blueprint: `references/blueprint_verified.md` lines 200–319
  (`prop:p-normal-form` proof).
- Round-6 informal sketch: `.archon/informal/levi.md` (Levi machinery).
- Round-6 prover report:
  `.archon/task_results/processed/round6/InducedOrbitToy_Slice.lean.md`
  (recorded recommended Round 7 sequencing).

## Round 6 Slice.lean API now available

`Slice.lean` lines 686–1047 expose the Levi API. **All listed
declarations are sorry-free**:

- `lambdaDualE S g : S.E →ₗ[F] S.E` — dual transpose `g^∨`.
- `lambdaDualE_pairing_eq` — defining identity `λ(g^∨ e, e') = λ(e, g e')`.
- `lambdaDualE_id`, `lambdaDualE_comp` — functoriality.
- `leviGL_E S d : Module.End F S.V`, `leviGL_E_apply`, `leviGL_E_symm_inverse`.
- `leviGL_V0 S g : Module.End F S.V`, `leviGL_V0_apply`, `leviGL_V0_symm_inverse`.
- `leviGL_E_isParabolic`, `leviGL_V0_isParabolic` — 4-conjunct
  parabolicity (`IsUnit ∧ flagE preserved ∧ flagEV0 preserved ∧ IsOrthogonal`).
- `leviGL_E_conj_XCB` —
  `leviGL_E d ∘ XCB(C, B) = XCB(C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm) ∘ leviGL_E d`.
- `leviGL_V0_conj_XCB` — analogous for `V0` block under
  `g`/X0 commutation + a `g`-pairwise condition.

**One sorry left in Slice.lean:** `parabolic_decompose` (line 1078),
deferred to Round 8.

## Round 7 deliverables

Round 7 closes the three NormalForm.lean sorries. The work splits into
**one structural restructure** (Tier S #5, signature change) plus
**three closure tasks** (Tier A).

### Tier S #5 — restructure `pNormalForm_witnesses`

**Reason:** the current statement of `pNormalForm_witnesses` (line 195)
is **mathematically false as written**. The conclusion
`uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T` cannot hold for arbitrary input
`(C, B)` because `uD`-conjugation only modifies the B-block (per
`uD_conj_XCB`), leaving the C-block invariant. The goal `XST Sₕ T` has
C-block `CST Sₕ`, so we need a Levi `leviGL_E d` to align `C → CST Sₕ`
*before* applying `uD D`.

**Restructure (preferred form):** change the conclusion to expose the
Levi factor `d : E' ≃ₗ[F] E'`:

```lean
private theorem pNormalForm_witnesses (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B)
    (_hRank :
      Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' →ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
      (d : S.E' ≃ₗ[F] S.E') (T : S.L0' →ₗ[F] S.L0),
      IsSkewT S T ∧
      uD S D ∘ₗ leviGL_E S d ∘ₗ XCB S C B
        = XST S Sₕ T ∘ₗ uD S D ∘ₗ leviGL_E S d
```

This says: for any `(C, B)`, there exists a Levi+unipotent conjugator
`p := uD D ∘ leviGL_E d` realising the conjugation
`p ∘ XCB(C, B) = XST(Sₕ, T) ∘ p`. The consumer `pNormalForm` reads `p`
off directly and proves `IsParabolicElement p` from `uD_isParabolic` ∘
`leviGL_E_isParabolic`.

**Cascading update:** rewrite `pNormalForm`'s body (lines 237–301) to
consume the new signature. The body becomes (sketch):

```lean
theorem pNormalForm (...) :
    ∃ (Sₕ : ...) (T : ...), IsSkewT S T ∧
      ∃ (p : Module.End F S.V), IsParabolicElement S p ∧
        p ∘ₗ XCB S C B = XST S Sₕ T ∘ₗ p := by
  obtain ⟨Sₕ, D, d, T, hT, hConj⟩ :=
    pNormalForm_witnesses S _hNondeg _hChar C B _hB _hRank
  refine ⟨Sₕ, T, hT, uD S D ∘ₗ leviGL_E S d, ?_, hConj⟩
  -- IsParabolicElement (uD S D ∘ leviGL_E S d):
  -- compose `uD_isParabolic` (Slice) with `leviGL_E_isParabolic`
  -- componentwise (IsUnit, flag preservation, IsOrthogonal).
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- IsUnit: product of two units.
    exact ((isUnit_uD S _hNondeg _hChar D).mul
      (leviGL_E_isParabolic S d).1)
  · -- flagE: composed map of flagE = flagE.
    rw [Submodule.map_comp]
    rw [(leviGL_E_isParabolic S d).2.1]
    exact map_uD_eq_of_le S _hNondeg _hChar D S.flagE
      (uD_isParabolic S _hNondeg _hChar D).2.1
      (uD_isParabolic S _hNondeg _hChar (-D)).2.1
  · -- flagEV0: same template.
    rw [Submodule.map_comp]
    rw [(leviGL_E_isParabolic S d).2.2.1]
    exact map_uD_eq_of_le S _hNondeg _hChar D S.flagEV0
      (uD_isParabolic S _hNondeg _hChar D).2.2
      (uD_isParabolic S _hNondeg _hChar (-D)).2.2
  · -- IsOrthogonal: composition of two isometries is an isometry.
    intro u v
    -- Unfold composition; reduce one step at a time using
    -- `(leviGL_E_isParabolic S d).2.2.2` (Levi isometry)
    -- and the `IsOrthogonal` derived from `uD_isParabolic`.
    sorry  -- straightforward 5-line proof
```

**Note on `IsOrthogonal` for the composition:** `LinearMap.IsOrthogonal`
unfolds to `∀ u v, B (f u) (f v) = B u v`. For composition, use:
```
S.ambientForm ((uD S D) (leviGL_E S d u)) ((uD S D) (leviGL_E S d v))
  = S.ambientForm (leviGL_E S d u) (leviGL_E S d v)  -- by uD-isOrthogonal
  = S.ambientForm u v                                  -- by leviGL_E-isOrthogonal
```
The `uD_isOrthogonal` is the 4th conjunct of `pNormalForm`'s line-282
calc chain (already in the existing body); the prover may extract it
to a helper lemma in the file (or just inline at this site).

### Tier A #1 — `pNormalForm_witnesses` body (line 195)

**Statement** (after restructure above): construct `(Sₕ, D, d, T)` with
`uD D ∘ leviGL_E d ∘ XCB C B = XST Sₕ T ∘ uD D ∘ leviGL_E d`.

**Strategy** (blueprint lines 200–264):

1. **Levi step (build `d` and `Sₕ`).** From `_hRank : rank Cbar = c`:
   - `dim ker (Cbar S C) = dim E' - c = dim E' - dim L1' = dim L0'`.
   - Hence there exists a linear iso `dL0' : S.L0' ≃ₗ[F] ker (Cbar S C)`
     (via Mathlib's `LinearEquiv.ofFinrankEq` on submodules of equal dim).
   - Lift `dL0'` to a full `d : S.E' ≃ₗ[F] S.E'` by:
     * choosing a complement `K` of `S.L0'` in `S.E'` (exists; it's
       `S.L1'`).
     * choosing a complement `K'` of `ker (Cbar S C)` in `S.E'`.
     * combining `dL0'` (on `S.L0'`) with any iso `S.L1' ≃ₗ K'` to
       form `d`.
   - Choose the `S.L1' ≃ₗ K'` block so that
     `(Cbar S C) ∘ d.symm` factors as `0` on `S.L0'` and as the
     mkQ-projection of some chosen `Sₕ : S.L1' ≃ₗ S.Vplus` on `S.L1'`.

   The blueprint's "another Levi action on `L1'`" maps to choosing the
   `K'` block of `d` so that the resulting `Sₕ : L1' →ₗ Vplus` is the
   identity-like target. Concretely, pick any iso
   `Sₕ : S.L1' ≃ₗ[F] S.Vplus` (exists by `dim L1' = c = dim Vplus`),
   then build `d` so that `(Cbar S C) ∘ d.symm` restricted to `L1'`
   pushes through `Sₕ`. The Mathlib tools:
   - `LinearMap.exists_linearEquiv_of_finrank_eq` (when finrank match),
   - `Submodule.LinearEquiv.ofFinrankEq` for sub-equivs on subspaces,
   - `LinearEquiv.ofComplement` (or manual `Submodule.IsCompl` + sum).

   **If this construction is intractable in one round**, the prover
   may emit one carefully-named sub-helper (e.g., `levi_d_witness`)
   and isolate just that piece as `sorry`. The plan agent will pick it
   up Round 8.

2. **Set new C, B post-Levi.** Apply `leviGL_E_conj_XCB`:
   `leviGL_E S d ∘ XCB S C B = XCB S (C ∘ d.symm) (lambdaDualE S d.symm ∘ B ∘ d.symm) ∘ leviGL_E S d`.
   Let `C' := C ∘ d.symm`, `B' := lambdaDualE S d.symm ∘ B ∘ d.symm`.
   By construction of `d`, `C'|_{L0'} ⊂ range X0` and `Cbar S C'|_{L1'} = mkQ ∘ Sₕ`.

3. **Unipotent step (build `D` and `T`).** Now reduce to the case
   already handled. Define:
   - `D : E' →ₗ V0` by: on `L1'`, use the `Vplus`-section of
     `S.X0` to choose `D|_{L1'}` so `X0 (D|_{L1'} e1') = (C' - CST Sₕ) e1'`;
     on `L0'`, use any section of `X0` over `range X0` (since
     `C'|_{L0'} ⊂ range X0`).
   - `T : L0' →ₗ L0` by: `T(e0') := projL0 (B'|_{L0'} e0')` (extract the
     L0-component after applying `B'` to `L0'`).

   The conjugation `uD D ∘ XCB C' B'` post-applies the unipotent. By
   `uD_conj_XCB`, the C-block becomes `C' - X0 D = CST Sₕ` (by D's
   construction) and the B-block becomes a fresh `B''` with
   `B''|_{L0'} = T` and `B''|_{L1'} = 0`. The resulting `XCB (CST Sₕ) B''
   = XST Sₕ T` after BST identification.

4. **Skew witness (`hT`).** From `_hB : IsSkewB B`, derive
   `IsSkewB B'` (preserved under Levi by `lambdaDualE_pairing_eq` +
   ε-symmetry; analogous to `uD_isParabolic`'s 4th conjunct), then
   `IsSkewT T` from B''.

**Estimated lines:** ~80–120. The construction of `d` is the
hardest. The unipotent step largely mirrors existing
`parametrizeX0PlusU_existence` machinery in `Slice.lean`.

### Tier A #2 — `residual_levi_extract` body (line 319)

**Statement:** given parabolic `p` with `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`,
construct `Bilinear.AreIsometric (BT S T₁) (BT S T₂)`, i.e., extract
`h : L0' ≃ₗ L0'` with `BT T₂ (h u) (h v) = BT T₁ u v`.

**Strategy (Option B, recommended by Round-6 prover):** skip
`parabolic_decompose`. Work directly via the `flagE` / `flagEV0`
preservation conjuncts of `IsParabolicElement` plus the
`IsOrthogonal` conjunct:

1. **Restrict `p` to `L0'`-residue.** Since `p` preserves `flagEV0 = E ⊕ V0`,
   the action on `V / flagEV0 ≃ E'` descends to a linear iso
   `p_E' : S.E' ≃ₗ S.E'` (the quotient action). Extract
   `h := p_E'|_{L0'}` — this requires `p_E'` to preserve `L0'`, which
   follows from `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` and the fact that
   `XST` has `ker XST = E ⊕ ker T` (from `kernelImage_ker`). The
   conjugation `p ∘ XST(...) = XST(...) ∘ p` implies `p` preserves
   `ker XST`, hence preserves `L0'` modulo flagEV0.

   **Practical implementation:** use `Submodule.quotientEquivOfIsCompl`
   on `flagEV0 ⊕ E' = V` (this requires building an `IsCompl flagEV0 E'.subtype`,
   which is the standard direct-sum decomposition of `V`).

2. **Verify isometry.** `BT T₂ (h u) (h v) = BT T₁ u v` follows from the
   `IsOrthogonal` conjunct of `p` plus the conjugation
   `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`:
   - `BT T u v := S.lambda (T u : E) (v : E')`.
   - The C-block of `XST(Sₕ, T)` carries the `T u`-information (via
     `Cdual (CST Sₕ) v + T u` under the unfolding).
   - Algebraic chase using `IsOrthogonal S.ambientForm p` and
     `lambdaDualE_pairing_eq`.

**Estimated lines:** ~40.

**Fallback:** if Step 1 (extracting `h` from quotient action) is
intractable, fall back to `parabolic_decompose` (currently sorry'd in
Slice.lean) and use it via Option A. This leaves
`residual_levi_extract` itself sorry-free but adds dependence on the
deferred `parabolic_decompose`. The Round 7 prover should attempt
Option B first; if blocked >30% into the round budget, switch to
Option A and document it.

### Tier A #3 — `residual_levi_build` body (line 348)

**Statement:** given iso `h : S.L0' ≃ₗ[F] S.L0'` with
`BT T₂ (h u) (h v) = BT T₁ u v`, construct parabolic `p` with
`p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`.

**Strategy:**

1. **Extend `h` to `d : S.E' ≃ₗ[F] S.E'`.** Define `d` as
   `h` on `S.L0'` and `id` on `S.L1'` (using `IsCompl L1' L0'`).
   - Mathlib: `LinearEquiv.ofTwoSubspaces` if available, else
     manual construction via the explicit decomposition
     `e' = projL1' e' + projL0' e'` (uses
     `Submodule.IsCompl.projection_add_projection_eq_self` from Round 4).
   - Concretely:
     ```lean
     let d : S.E' ≃ₗ[F] S.E' :=
       LinearEquiv.ofBijective
         ((LinearMap.id ∘ₗ S.L1'.subtype ∘ₗ projL1' S) +
          (S.L0'.subtype ∘ₗ h.toLinearMap ∘ₗ projL0' S))
         (by ...)
     ```
2. **Set `p := leviGL_E S d`.** Parabolicity follows from
   `leviGL_E_isParabolic`.
3. **Verify the conjugation:**
   `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`. This unfolds via
   `XST` definition (`XCB S (CST Sₕ) (BST T)`) plus
   `leviGL_E_conj_XCB` to a calculation:
   `leviGL_E d ∘ XCB(CST Sₕ, BST T₁) = XCB(CST Sₕ ∘ d.symm, ...) ∘ leviGL_E d`.
   Show that `CST Sₕ ∘ d.symm = CST Sₕ` (since `d.symm` is `id` on
   `L1'` and `h.symm` on `L0'`, and `CST Sₕ` only depends on `L1'`-projection).
   The B-block transformation
   `lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂` is the residue of
   the isometry condition `BT T₂ (h u) (h v) = BT T₁ u v`, after
   reduction via `lambdaDualE_pairing_eq` and the `BT`/`BST` definitions.
4. **Refresh stale comments at lines 344, 357** (no longer relevant).

**Estimated lines:** ~40–60.

## Files NOT assigned this round

- `InducedOrbitToy/Basic.lean` — done.
- `InducedOrbitToy/X0Geometry.lean` — done (modulo pre-existing
  `hlambda` lint at line 221 — preserved as part of the autoformalised
  statement).
- `InducedOrbitToy/LocalForms.lean` — done.
- `InducedOrbitToy/Slice.lean` — `parabolic_decompose` (line 1078)
  deferred to Round 8.
- `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion`
  (line 324) deferred to Round 8.

## Acceptance criteria for Round 7

- `lake env lean InducedOrbitToy/NormalForm.lean` compiles.
- `lake build` is green.
- Sorry count: 5 → 2 (NormalForm 3 → 0; Slice unchanged at 1; Orbits
  unchanged at 1).
- `pNormalForm_witnesses` may either be fully closed OR carry one
  sub-helper sorry isolating the `d`-construction; the rest of
  `pNormalForm_witnesses` and all of `pNormalForm` must compile.
- `residual_levi_extract` and `residual_levi_build` must be
  sorry-free.
- `#print axioms` on every newly-closed declaration shows only
  `[propext, Classical.choice, Quot.sound]`.
- No new custom `axiom` declarations.

## Stop conditions

- If the Tier S #5 restructure proves intractable (signature change
  cascades break elsewhere): stop and report. Plan agent re-evaluates.
- If the `d`-construction in Tier A #1 proves intractable: emit a
  one-helper sorry, close everything else.
- If Tier A #2 Option B blocks: switch to Option A
  (`parabolic_decompose`), but coordinate via task report — Round 8 is
  then forced to close `parabolic_decompose` first.

## Lessons carry-forward (Round 6 → Round 7)

- **`d.symm.symm = d` is `rfl`** — used twice in Round 6, will recur
  for Levi unfolding. Rely on it.
- **LinearEquiv FunLike vs LinearMap FunLike coercion mismatch in `rw`**
  patterns. State isometry-style hypotheses in
  LinearMap-coerced form `(g : V →ₗ V) v` to match
  `LinearMap.comp_apply`-output goals.
- **`show` to convert composed form to nested form** before
  `rw`-ing perfect-pairing equations.
- **Block-matrix proofs via `Prod.mk.injEq` chains** —
  `refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩`.
- **`linear_combination` is scalar-only** over generic Modules; for
  vector identities use `rw` chains + `abel`.
- **`#print axioms` via Bash + `/tmp/check_axioms.lean`** for closure
  audits.
