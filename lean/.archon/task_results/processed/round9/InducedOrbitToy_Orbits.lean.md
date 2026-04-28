# InducedOrbitToy/Orbits.lean — Round 9

## Summary

**Net sorry change in this file: 2 → 2 (restructured, not closed).**

The two scoped sorries in `isParabolicElement_ringInverse_of_orbit_witness`
(originally lines 453, 456) are **not closed**, but the proof structure
has been substantially refactored:

- A **conjugation-rearrangement helper** (`orbit_conj_rearr`) extracts
  the dual symmetric forms of `_hyeq` algebraically (sorry-free, ~20 lines).
- A **`flagE ⊆ ker XST`** helper (`flagE_le_ker_XST`) is proven
  unconditionally (sorry-free, ~20 lines).
- A **kernel-identification helper** (`ker_XST_eq_flagE_of_injective`)
  closes `ker XST T = flagE` *under the hypothesis* `LinearMap.ker T = ⊥`,
  using `kernelImage_ker` from `NormalForm.lean` (sorry-free, ~10 lines).
- The main helper body now extracts the kernel containments
  `(Ring.inverse g)(flagE) ⊆ ker XST T₂` and `g(flagE) ⊆ ker XST T₁`
  fully constructively (~40 lines).
- The **flagE conjunct closes fully** *conditional on*
  `ker XST T₁ = flagE ∧ ker XST T₂ = flagE` (the `obtain ⟨hkerT1, hkerT2⟩`
  destructure feeds the closing argument).
- The **single remaining sorry for the flagE half** is the
  kernel-identification, packaged as one term-mode sorry (line 563
  in the new layout).
- The **flagEV0 conjunct** retains its sorry; the kernel approach does
  not directly apply (V0-action is non-trivial).

`lake env lean InducedOrbitToy/Orbits.lean` ✅ (single declaration-use
sorry warning at line 524, in `isParabolicElement_ringInverse_of_orbit_witness`).
`lake build` of NormalForm.lean errors are from the parallel prover's
in-progress edits to that file — out of scope for Orbits.lean.

## isParabolicElement_ringInverse_of_orbit_witness (line ~524)

### Round 9 progress: structural refactor

#### Attempt 1 (RESTRUCTURED, not closed)

**Approach:** Refactor the body to expose the precise mathematical gap,
extracting partial progress into smaller private helpers.

1. Use `orbit_conj_rearr` to derive both conjugation forms.
2. Use `flagE_le_ker_XST` to establish `flagE ⊆ ker XST T_i`.
3. Show `(Ring.inverse g)(flagE) ⊆ ker XST T₂` via:
   - `flagE ⊆ ker XST T₁` (Step 2).
   - `XST T₂ ∘ Ring.inverse g = Ring.inverse g ∘ XST T₁` (`hConj_inv`).
   - For `x ∈ flagE`: `XST T₂ (Ring.inverse g x) = Ring.inverse g (XST T₁ x) = 0`.
4. Show `g(flagE) ⊆ ker XST T₁` symmetrically via `hConj_dual`.
5. **Sub-claim (sorry):** `ker XST T₁ = flagE ∧ ker XST T₂ = flagE`.
6. Given the sub-claim, close `Submodule.map (Ring.inverse g) flagE = flagE`
   constructively:
   - ⊆: For `y = Ring.inverse g x` with `x ∈ flagE`, use `h_inv_in_kerT2`
     and the kernel-equality.
   - ⊇: For `y ∈ flagE`, witness via `g y` (which lies in `flagE` by
     Step 4 + kernel-equality), then `Ring.inverse g (g y) = y` via
     `hg_cancel_left`.

**Result:** The flagE conjunct is **fully constructive modulo the
kernel identification**. The remaining sorry isolates a precise
mathematical sub-claim.

**Mathematical gap (case analysis):**
- ε = -1: `MaximalRank = dim L0'`, T injective ⇒ ker XST = flagE ✓
- ε = +1, l even: `MaximalRank = dim L0'`, T injective ⇒ ker XST = flagE ✓
- ε = +1, l odd: `MaximalRank = dim L0' - 1`, T has 1-dim kernel ⇒
  ker XST ⊋ flagE ✗

In case 3, the helper's claim is **mis-stated**: there exist conjugating
g's that do NOT preserve flagE. The blueprint argument (lines 658–676)
handles case 3 differently (uniqueness of alternating forms), without
asserting g ∈ P. Closing case 3 requires either restructuring the
caller (case-split on ε) or generalising via a Bruhat-decomposition
argument (out of scope).

### Sub-helpers added

1. **`orbit_conj_rearr`** (private, line ~421): given the conjugation
   `XST T₁ = g · XST T₂ · Ring.inverse g`, derive both
   `Ring.inverse g · XST T₁ = XST T₂ · Ring.inverse g` and
   `g · XST T₂ = XST T₁ · g`. Algebraic, sorry-free.
   Uses `Ring.inverse_mul_cancel`, `mul_assoc`.

2. **`flagE_le_ker_XST`** (private, line ~445): always
   `flagE ⊆ ker XST Sₕ T`. By `XST(e, 0, 0) = 0`. Sorry-free.

3. **`ker_XST_eq_flagE_of_injective`** (private, line ~431): if
   `ker T = ⊥`, then `ker XST = flagE`. Uses `kernelImage_ker`
   (NormalForm.lean) + `Submodule.map_bot`. Sorry-free.

### Why I didn't fully close

The helper's signature (preserved from Round 8) takes `IsSkewT` only,
not `Tset_circ` membership. To derive `ker T = ⊥`, we need
`finrank (range T) = MaximalRank` AND `MaximalRank = dim L0'`. The
latter requires `¬ (eps = 1 ∧ Odd l)`, which is decidable but absent
from the helper's hypotheses.

**Two ways forward (Round 10):**

(a) **Tighten helper signature.** Replace `_hT₁ : IsSkewT T₁` with
    `hT₁ : T₁ ∈ S.Tset_circ`, similarly for T₂. Then in the helper:
    ```
    by_cases h_easy : ¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))
    · -- Easy case: derive ker T_i = ⊥, close fully.
      have hMR : S.MaximalRank = Module.finrank F S.L0' := by
        unfold SliceSetup.MaximalRank; rw [if_neg h_easy]
      have hker1 : LinearMap.ker T₁ = ⊥ := by
        rw [← LinearMap.ker_eq_bot]
        ... (rank-nullity from hT₁.2 + hMR)
      ... apply ker_XST_eq_flagE_of_injective
    · -- Hard case: ε = +1, l odd. Sorry (genuinely needs restructuring).
      sorry
    ```
    This closes 2 of 3 cases; only case 3 remains sorry'd. Update
    `sIndependenceAndOrbitCriterion` call site to pass `hT₁` instead
    of `hT₁.1`.

(b) **Restructure `sIndependenceAndOrbitCriterion`.** Split the
    forward-direction proof on `S.eps = 1 ∧ Odd (...)`. In cases 1-2,
    use the kernel argument (route through `pNormalForm_residual_orbit_iso`
    with helper). In case 3, prove the bilinear isometry directly via
    uniqueness of alternating forms (currently no scaffold for this in
    `Slice.lean`/`NormalForm.lean`).

Option (a) is the smaller fix; option (b) is mathematically cleaner.
Plan agent should decide.

### flagEV0 conjunct (line ~624)

**Status: still sorry.** The kernel-based argument used for flagE does
NOT apply, because `flagEV0 ⊄ ker XST` in general. XST acts non-trivially
on the V0 component.

**Sketch of proper argument** (Bruhat decomposition):
- `range XST ⊆ flagEV0` (third component of `XST(e,v,e')` is always 0).
- A G-conjugacy preserving the slice `O₀ + 𝔲` must factor through the
  Levi+unipotent decomposition of P.
- The Levi factor preserves `flagEV0` automatically (it acts
  block-diagonally on `E ⊕ V0 ⊕ E'`).
- The unipotent factor is in `P` by definition.

This argument is what `Slice.lean :: parabolic_decompose` is meant to
provide (Tier S #6). That lemma is *also* deferred due to a documented
mathematical gap (residual `B'` parameter).

**Recommended Round 10 approach:** wait for `parabolic_decompose`
infrastructure to land in polish stage, then apply it directly here.

## Sorry count

- Old (Round 8): 2 (flagE + flagEV0).
- New (Round 9): 2 (kernel-identification + flagEV0).

The kernel-identification sorry is **mathematically more focused** than
the original flagE sorry. It is a single propositional conjunction
about kernel equality, which is clearly true in 2 of 3 cases and clearly
false in case 3 (when the helper itself is mis-stated).

## Mathlib lemmas used (notable)

- `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`: core inverse identities.
- `Module.End.mul_apply`: `(g₁ * g₂) v = g₁ (g₂ v)`.
- `Submodule.map_bot`: `Submodule.map f ⊥ = ⊥`.
- `kernelImage_ker` (project-internal, NormalForm.lean): the closed form
  for `ker XST = ⊤ ×ˢ ⊥ ×ˢ (ker T).map L0'.subtype`.
- `Submodule.mem_prod`, `Submodule.mem_bot`: standard.

## Cross-file impact

- **None.** Orbits.lean modifications are file-local. The new helpers
  use `kernelImage_ker` from NormalForm.lean (a stable public API).

## Confirmation

- `lake env lean InducedOrbitToy/Orbits.lean` ✅ (single declaration-use
  sorry warning at line 524).
- **`lake build` is NOT green** — but the failure is in `NormalForm.lean`
  (lines 289–305) due to the parallel prover's in-progress edits to
  `pNormalForm_witnesses_aux`. Out of scope for Orbits.lean.
- `#print axioms InducedOrbitToy.sIndependenceAndOrbitCriterion`:
  `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx via the
  helper's kernel-identification sorry; same as Round 8).
- `#print axioms InducedOrbitToy.main`: same as above.
- `#print axioms InducedOrbitToy.inducedOrbits`,
  `multiplicityNonDeg`, `multiplicityOddCase`:
  `[propext, Classical.choice, Quot.sound]` (clean, no sorryAx).
- **No custom axioms introduced.**

## Next steps (Round 10 candidates)

1. **Close cases 1-2 via signature tightening** (option (a) above):
   Replace `IsSkewT` hypotheses with `Tset_circ` memberships, derive
   `ker T = ⊥` via rank-nullity + `MaximalRank = dim L0'`, and apply
   `ker_XST_eq_flagE_of_injective`. Updates required:
   - Helper signature (`isParabolicElement_ringInverse_of_orbit_witness`)
   - Call site in `sIndependenceAndOrbitCriterion` (pass `hT₁`, `hT₂`
     instead of `hT₁.1`, `hT₂.1`).
   - Add by_cases on `S.eps = 1 ∧ Odd ...`; only case 3 remains sorry.

2. **Close case 3 via bilinear-isometry uniqueness** (option (b) above):
   Split `sIndependenceAndOrbitCriterion` forward-direction on
   `S.eps = 1 ∧ Odd ...`. In case 3, prove `IsometryRel S T₁ T₂` directly
   from the abstract uniqueness of alternating forms of fixed rank
   (requires new infrastructure — could use `ClassifyBilinearForms`
   typeclass).

3. **Close `flagEV0` conjunct** via `parabolic_decompose` (Slice.lean)
   once that lemma's statement is fixed (Tier S #6 polish work).

## Reusable insights

- **`Ring.inverse_mul_cancel _ hgU` / `Ring.mul_inverse_cancel _ hgU`**:
  the standard cancellations for unit-conjugation on `Module.End F V`.
- **Conjugation rearrangement**: `XST T₁ = g · XST T₂ · g⁻¹`
  ⟺ `g⁻¹ · XST T₁ = XST T₂ · g⁻¹` ⟺ `g · XST T₂ = XST T₁ · g`. Both
  symmetric forms are useful for kernel-containment chases.
- **`Submodule.map_bot`** simplifies the kernel form when `T` injective.
- **Body-sorry → conjunction-sorry refactor pattern**: when two related
  scoped sorries reduce to a common sub-claim (here, `ker XST = flagE`
  for two indices), bundle them into one term-mode sorry on the
  conjunction. Cleaner than repeated case work.
