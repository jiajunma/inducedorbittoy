# InducedOrbitToy/Orbits.lean — Round 8 (session 10)

## Summary

**Net sorry change in this file: 2 → 1 (private helper).**
**Public consequence: `sIndependenceAndOrbitCriterion`'s body is now sorry-free**;
the only surviving sorry has been pushed down into a focused private helper
(`isParabolicElement_ringInverse_of_orbit_witness`) carrying the slice-
transversality argument for the forward direction.

`lake env lean InducedOrbitToy/Orbits.lean` ✅ (single sorry warning at
line 438). `lake build` ✅. `#print axioms` on every public theorem
returns `[propext, Classical.choice, Quot.sound]` (plus transitive
`sorryAx` on `sIndependenceAndOrbitCriterion` and `main` only — through
the new private helper).

## sIndependenceAndOrbitCriterion (line ~509)

### Signature change (option (a) + option (i) per Round 8 plan)

- Replaced `(Sₕ₁ Sₕ₂ : S.L1' ≃ₗ[F] S.Vplus)` with single
  `(Sₕ : S.L1' ≃ₗ[F] S.Vplus)` (option (i)).
- Added explicit hypotheses `(hNondeg : S.formV0.Nondegenerate)` and
  `(hChar : (2 : F) ≠ 0)` (option (a)). These thread to
  `pNormalForm_residual_orbit_iso`.
- Renamed `_hT₁`, `_hT₂` to `hT₁`, `hT₂` (now actually used).
- Renamed `_hChar → hChar` in `main` (now actually threaded into
  `sIndependenceAndOrbitCriterion`).
- `main` updated: `sIndependenceAndOrbitCriterion S Sₕ Sₕ T₁ T₂ hT₁ hT₂`
  → `sIndependenceAndOrbitCriterion S hNondeg hChar Sₕ T₁ T₂ hT₁ hT₂`.

### Reverse direction (line 376 → ~559) — RESOLVED, sorry-free

#### Attempt 1
- **Approach:** Apply `pNormalForm_residual_orbit_iso` (←) to lift the
  bilinear isometry to a `P`-element `p` with
  `p ∘ XST T₁ = XST T₂ ∘ p`. From `IsParabolicElement S p`, extract the
  1st conjunct (`IsUnit p`) and 4th conjunct
  (`IsOrthogonal S.ambientForm p`); flag-stability conjuncts are
  *not* needed for orbit equality. Use new helper
  `GOrbit_eq_of_isometry_conj` to conclude.
- **Result:** RESOLVED. Two-line proof:
  ```lean
  obtain ⟨p, hP, hConj⟩ :=
    (S.pNormalForm_residual_orbit_iso hNondeg hChar Sₕ T₁ T₂
        hT₁.1 hT₂.1).mpr hiso
  exact GOrbit_eq_of_isometry_conj S hP.1 hP.2.2.2 hConj
  ```
- **Key insight:** the parabolic flag-stability is *not* needed for orbit
  equality — only the unit/orthogonal data of `p` matters. The helper
  `GOrbit_eq_of_isometry_conj` exposes exactly this weakened hypothesis.

### Forward direction (line 358 → ~519) — RESOLVED via helper, helper carries sorry

#### Attempt 1
- **Approach:** Four-step plan from Round 8 plan (option Route B style):
  1. Extract orbit witness `g` via
     `XST S Sₕ T₁ ∈ GOrbit (XST S Sₕ T₁)` + `rw [horbit]`.
  2. Lift `g` to `IsParabolicElement (Ring.inverse g)` via private helper
     `isParabolicElement_ringInverse_of_orbit_witness`. *(Helper carries
     the slice-stability sorry.)*
  3. Algebraically derive
     `Ring.inverse g ∘ XST T₁ = XST T₂ ∘ Ring.inverse g` from `hyeq`.
  4. Apply `pNormalForm_residual_orbit_iso` (→) with `p := Ring.inverse g`.
- **Result:** RESOLVED *modulo helper sorry*. The body proof is fully
  constructive; the only `sorry` is in the slice-transversality helper.
- **Key calc step (Step 3):** Pre-composing `hyeq` with `Ring.inverse g`
  cancels the leading `g` via `Ring.inverse_mul_cancel`:
  ```lean
  show Ring.inverse g * XST Sₕ T₁ = XST Sₕ T₂ * Ring.inverse g
  rw [hyeq, ← mul_assoc, ← mul_assoc,
      Ring.inverse_mul_cancel _ hgU, one_mul]
  ```

## isParabolicElement_ringInverse_of_orbit_witness (private, line 438)

### Status: 2 scoped sorries on flag-stability conjuncts

The helper extracts an `IsParabolicElement S (Ring.inverse g)` witness
from an `IsometryEnd S g` plus a slice conjugation hypothesis.

**Sorry-free conjuncts:**
- `IsUnit (Ring.inverse g)` ✓ via `IsUnit.ringInverse`.
- `IsOrthogonal S.ambientForm (Ring.inverse g)` ✓ via new helper
  `IsOrthogonal_ringInverse`.

**Sorry'd conjuncts (Gap):**
- `Submodule.map (Ring.inverse g) S.flagE = S.flagE`
- `Submodule.map (Ring.inverse g) S.flagEV0 = S.flagEV0`

These two flag-stability conjuncts require a slice-transversality
argument: every `g ∈ G` that conjugates `XST T₂` to `XST T₁` (both
elements of the slice `O₀ + 𝔲`) must already lie in `P`. The classical
proof uses Bruhat decomposition + uniqueness of the unipotent
factorisation (via `parametrizeX0PlusU_uniqueness` from Slice.lean).
Concretely, one would:

1. Compute the kernel and image of `Ring.inverse g` restricted to
   `flagEV0` using the conjugation equation.
2. Use `range XST ⊆ flagEV0` (true for both `T₁`, `T₂`) to constrain
   the action of `g` on `flagEV0`.
3. Use the uniqueness of the parametrization
   (`parametrizeX0PlusU_uniqueness`) to descend to flag preservation.

Step 3 needs `parabolic_decompose` (Slice.lean line 1109 — also
deferred), or its equivalent direct decomposition argument. Both are
out of Round 8 scope per stop conditions.

## New helper lemmas added (private, line 292–456)

1. **`IsOrthogonal_mul`** (line ~294): composition of orthogonal
   endomorphisms is orthogonal. Uses `Module.End.mul_apply`.
2. **`IsOrthogonal_ringInverse`** (line ~306): `Ring.inverse` of an
   invertible orthogonal endomorphism is orthogonal. Uses
   `Ring.mul_inverse_cancel` to derive `p (Ring.inverse p w) = w`.
3. **`GOrbit_eq_of_isometry_conj`** (line ~329): orbit equality from a
   single conjugating isometry. The parabolic flag-stability is *not*
   needed; only the unit/orthogonal data matters. Both inclusions follow
   the same pattern: take orbit witness `g ↦ g * Ring.inverse p` (or
   `g ↦ g * p`), prove the resulting endomorphism is an isometry via
   `IsOrthogonal_mul` + `IsOrthogonal_ringInverse`, and reduce the
   conjugation identity using a manually-derived
   `Ring.inverse (a * b) = ...` via the canonical
   `Ring.inverse_mul_cancel`-uniqueness argument.

   Key lemma proven inline: for units `g, p`,
   `Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g`. Derived via
   `(g * Ring.inverse p) * (p * Ring.inverse g) = 1` (using
   `Ring.inverse_mul_cancel _ hpU` and `Ring.mul_inverse_cancel _ hgU`),
   then `Ring.inverse h = Ring.inverse h * (h * (p * Ring.inverse g))`
   collapses to `p * Ring.inverse g`. The associativity wrangling closes
   with `noncomm_ring` after substitution.
4. **`isParabolicElement_ringInverse_of_orbit_witness`** (line ~438):
   slice-transversality helper for the forward direction. Two scoped
   sorries on flag-stability (see above).

## Mathlib lemmas used (notable)

- `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`: core identities
  on `Ring.inverse` for units in a `MonoidWithZero` (and
  `Module.End F V` is one).
- `IsUnit.ringInverse`: inverse of a unit is a unit.
- `IsUnit.mul`: product of units is a unit.
- `Module.End.mul_apply`: `(g₁ * g₂) v = g₁ (g₂ v)`.
- `noncomm_ring`: closes module-endomorphism associativity goals where
  `ring` (commutative-only) cannot.

## Cross-file impact

- **None.** `Orbits.lean` is downstream; no other file modified.
- The signature change to `sIndependenceAndOrbitCriterion` is
  in-file-cascaded to `main` (line ~621). Both compile.
- No change to NormalForm.lean or Slice.lean.

## Confirmation

- `lake env lean InducedOrbitToy/Orbits.lean` ✅ (single sorry warning at
  line 438, in private helper).
- `lake build` ✅ (3 sorry warnings total: NormalForm.lean:197 + Slice.lean:1109
  + Orbits.lean:438; only Orbits one is mine, others unchanged).
- `#print axioms InducedOrbitToy.sIndependenceAndOrbitCriterion`:
  `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx via the
  new private helper, expected per stop conditions).
- `#print axioms InducedOrbitToy.main`: same as above.
- `#print axioms InducedOrbitToy.inducedOrbits`,
  `multiplicityNonDeg`, `multiplicityOddCase`:
  `[propext, Classical.choice, Quot.sound]` (no sorryAx).
- **No custom axioms introduced.**

## Next steps (Round 9 candidates)

1. Close the two flag-stability sorries in
   `isParabolicElement_ringInverse_of_orbit_witness` via either:
   - **Route A:** depend on `parabolic_decompose` once landed
     (Slice.lean line 1109).
   - **Route B:** direct slice-transversality argument using
     `parametrizeX0PlusU_uniqueness` + the structure of `range XST`.

   Once those land, `sIndependenceAndOrbitCriterion` (and `main`) become
   fully sorry-free with axioms `[propext, Classical.choice, Quot.sound]`.

2. The `noncomm_ring` tactic is essential here. Future provers in this
   file should prefer it over manual `mul_assoc` chains for any
   associativity rearrangement on `Module.End F V`.
