# Session 10 — Prover Round 8 (parallel three-file dispatch)

## Metadata

- **Session:** 10 (stage `prover`, Round 8 — parallel three-file dispatch on `NormalForm.lean` + `Orbits.lean` + `Slice.lean`).
- **Sorry count (declaration-use warnings) before round:** 3
  - `NormalForm.lean`: 1 (`pNormalForm_witnesses` line 203, body sorry at line 216).
  - `Slice.lean`: 1 (`parabolic_decompose` line 1078, body sorry around line 1089).
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` line 324, two scoped sorries at lines 358 + 376).
- **Sorry count (declaration-use warnings) after round:** **3** (no net change).
  - `NormalForm.lean`: 1 (`pNormalForm_witnesses_aux` line 197 — NEW private helper holding the original sorry; body of `pNormalForm_witnesses` itself is now sorry-free).
  - `Slice.lean`: 1 (`parabolic_decompose` line 1109 — body has substantial new constructive content but final assembly still sorry'd at line 1572; **mathematical gap identified — statement may be missing a `B'` parameter**).
  - `Orbits.lean`: 1 (`isParabolicElement_ringInverse_of_orbit_witness` line 438 — NEW private helper carrying 2 scoped sorries on flag-stability; bodies of `sIndependenceAndOrbitCriterion` reverse direction is sorry-free, forward direction passes through the helper).
- **Net change:** 3 → 3 declaration warnings (0 net). Plan target was 3 → 0 (close all three sorries). Achieved structural reorganisation but no net closure: every public theorem body is now thinner and pushes through a single private helper carrying the residual sorry.
- **Custom axioms introduced:** 0. `#print axioms` audit (verified):
  - `inducedOrbits`, `multiplicityNonDeg`, `multiplicityOddCase`, `pNormalForm_residual_orbit_iso`, `kernelImage_*`: `[propext, Classical.choice, Quot.sound]` — CLEAN.
  - `sIndependenceAndOrbitCriterion`, `main`, `pNormalForm`: depend transitively on `sorryAx` via the new private helpers — expected.
- **Build status:** `lake build` green at end of round (8033 jobs). 3 declaration-use sorry warnings + 1 pre-existing unused-variable lint at `X0Geometry.lean:221`.
- **Pre-processed log:** 187 events total (1 summary line + 186 events), **16 edits across 3 files** (`NormalForm.lean`, `Orbits.lean`, `Slice.lean`), 1 explicit `lean_goal` check, 6 diagnostic checks, 26 lemma searches.

## Process observation

Plan agent dispatched **three parallel objectives** (Option B from session 9 recommendations). All three provers ran concurrently with no source-level edit overlap:
- NormalForm prover edited lines ~190–230 (added `pNormalForm_witnesses_aux` helper, refactored `pNormalForm_witnesses` body to a one-liner).
- Orbits prover edited lines ~292–630 (added `IsOrthogonal_mul`, `IsOrthogonal_ringInverse`, `GOrbit_eq_of_isometry_conj`, `isParabolicElement_ringInverse_of_orbit_witness` helpers; signature change to `sIndependenceAndOrbitCriterion`; cascaded into `main`).
- Slice prover edited lines ~1065–1574 (substantial new constructive content for `parabolic_decompose` body; identified mathematical gap in the statement).

Mid-round build breakage was observed (NormalForm prover noted that the Slice prover's edits had transient type errors), but end-of-round merge yielded green build.

**No net sorry closure**, but **structural improvement** in all three files: each remaining sorry is now isolated to a single private helper with a documented Gap, enabling Round 9 to focus narrowly. The Slice prover's mathematical analysis (statement of `parabolic_decompose` is too narrow) is the most actionable finding from this round.

## Target — `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` ⏸️ DEFERRED via helper

### Approach

Per PROGRESS.md acceptance fallback: "Acceptable to introduce one isolated helper `private def` with its own sorry if Step 1 (d-construction) is intractable; in that case the helper sorry must be documented with a `Gap:` comment block."

The prover concluded that the full four-step construction (Sₕ, D, d, T + skewness + conjugation) is approximately 200–300 lines and out of single-round scope. They:

1. **Added `pNormalForm_witnesses_aux` (line 197)** — single isolated private helper carrying the residual sorry.
2. **Comprehensive Gap docstring (lines 152–196)** walking through all four steps of the blueprint proof.
3. **Refactored `pNormalForm_witnesses` body to a one-liner** — `exact pNormalForm_witnesses_aux S _hNondeg _hChar C B _hB _hRank`. The body is now sorry-free.

### Net effect

- `pNormalForm_witnesses` body: `sorry` → `exact pNormalForm_witnesses_aux ...` (sorry-free).
- New `pNormalForm_witnesses_aux`: 1 declaration-use sorry.
- **Net declaration count unchanged** (1 → 1).

### Key finding flagged for Round 9

`dim L1' = c` is needed for `Sₕ : L1' ≃ Vplus` and is **not enforceable from `SliceSetup` alone**. Counterexamples: `L1' = E', L0' = 0`. The Round-9 prover may need to either:
- (a) add a hypothesis `(_hL1' : Module.finrank F S.L1' = c S.toX0Setup)` to the helper signature, or
- (b) identify a hidden derivation from `_hRank` + the slice constraints.

If (a), the hypothesis would cascade through `pNormalForm`, `pNormalForm_residual_orbit_iso`, and downstream consumers — non-trivial signature work.

## Target — `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` 🟡 PARTIAL

### Signature change (option (a) + option (i) per PROGRESS.md)

- Replaced `(Sₕ₁ Sₕ₂ : S.L1' ≃ₗ[F] S.Vplus)` with single `(Sₕ : S.L1' ≃ₗ[F] S.Vplus)` (option (i)).
- Added explicit hypotheses `(hNondeg : S.formV0.Nondegenerate)` and `(hChar : (2 : F) ≠ 0)` (option (a)).
- Renamed `_hT₁`, `_hT₂` to `hT₁`, `hT₂` (now actually used).
- `main` updated: `sIndependenceAndOrbitCriterion S hNondeg hChar Sₕ T₁ T₂ hT₁ hT₂` (was `S Sₕ Sₕ T₁ T₂ hT₁ hT₂`).

### Reverse direction (line 376 → 559) — RESOLVED, sorry-free

```lean
obtain ⟨p, hP, hConj⟩ :=
  (S.pNormalForm_residual_orbit_iso hNondeg hChar Sₕ T₁ T₂
      hT₁.1 hT₂.1).mpr hiso
exact GOrbit_eq_of_isometry_conj S hP.1 hP.2.2.2 hConj
```

**Key insight:** Parabolic flag-stability is *not* needed for orbit equality — only the unit/orthogonal data of `p`. The new helper `GOrbit_eq_of_isometry_conj` exposes exactly this weakened hypothesis.

### Forward direction (line 358 → 519) — RESOLVED in body, helper carries sorry

Four-step plan:
1. Extract orbit witness `g` via `XST S Sₕ T₁ ∈ GOrbit (XST S Sₕ T₁)` + `rw [horbit]`.
2. Lift `g` to `IsParabolicElement (Ring.inverse g)` via private helper.
3. Algebraically derive `Ring.inverse g ∘ XST T₁ = XST T₂ ∘ Ring.inverse g` from `hyeq`.
4. Apply `pNormalForm_residual_orbit_iso` (→) with `p := Ring.inverse g`.

Step 3 key calc:
```lean
show Ring.inverse g * XST Sₕ T₁ = XST Sₕ T₂ * Ring.inverse g
rw [hyeq', ← mul_assoc, ← mul_assoc,
    Ring.inverse_mul_cancel _ hgU, one_mul]
```

### New helper `isParabolicElement_ringInverse_of_orbit_witness` (line 438)

Carries 2 scoped sorries on flag-stability conjuncts:
- `Submodule.map (Ring.inverse g) S.flagE = S.flagE` — sorry.
- `Submodule.map (Ring.inverse g) S.flagEV0 = S.flagEV0` — sorry.

Sorry-free conjuncts:
- `IsUnit (Ring.inverse g)` ✓ via `IsUnit.ringInverse`.
- `IsOrthogonal S.ambientForm (Ring.inverse g)` ✓ via new helper `IsOrthogonal_ringInverse`.

### New helper lemmas added

1. **`IsOrthogonal_mul`** — composition of orthogonal endomorphisms is orthogonal. Uses `Module.End.mul_apply`.
2. **`IsOrthogonal_ringInverse`** — `Ring.inverse` of an invertible orthogonal endomorphism is orthogonal. Uses `Ring.mul_inverse_cancel` to derive `p (Ring.inverse p w) = w`.
3. **`GOrbit_eq_of_isometry_conj`** — orbit equality from a single conjugating isometry; flag-stability not needed. Both inclusions follow `g ↦ g * Ring.inverse p` (or `g ↦ g * p`); proves the resulting endomorphism is an isometry via `IsOrthogonal_mul` + `IsOrthogonal_ringInverse`.

   Key inline lemma: for units `g, p`, `Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g`. Derived via `(g * Ring.inverse p) * (p * Ring.inverse g) = 1`. Associativity wrangling closes with `noncomm_ring`.
4. **`isParabolicElement_ringInverse_of_orbit_witness`** — slice-transversality helper. 2 scoped sorries.

### Net effect

- `sIndependenceAndOrbitCriterion` body: 2 `sorry` → 0 (sorry-free).
- New `isParabolicElement_ringInverse_of_orbit_witness`: 2 sorries (1 declaration-use warning).
- **Net declaration warning count unchanged** (1 → 1).

## Target — `InducedOrbitToy/Slice.lean :: parabolic_decompose` 🟡 PARTIAL with mathematical finding

### What landed (sorry-free, inside the proof body, ~460 new lines)

1. **Inverse extraction:**
   - `pinv := _hpUnit.unit.inv : Module.End F S.V`.
   - `hpinv_left`, `hpinv_right` via `Module.End.isUnit_inv_apply_apply_of_isUnit` and dual.

2. **Flag-preservation transfer to `pinv`:**
   - `hpinv_flagE : Submodule.map pinv S.flagE = S.flagE`.
   - `hpinv_flagEV0 : Submodule.map pinv S.flagEV0 = S.flagEV0`.

3. **Diagonal-block linear maps (sorry-free):**
   - `pE_fn : S.E →ₗ[F] S.E` with `pE_fn_eq`.
   - `pV0_fn : S.V0 →ₗ[F] S.V0` with `pV0_fn_E'_eq`.
   - `pE'_fn : S.E' →ₗ[F] S.E'`.
   - Plus parallel maps `pE_inv`, `pV0_inv`, `pE'_inv` from `pinv`.

4. **Bijectivity (round-trip identities) — all sorry-free:**
   - `pE_round_left/right` via 3-step calc chain.
   - `pV0_round_left/right` using linearity decomposition.
   - `pE'_round_left/right` analogous.

5. **`LinearEquiv` packaging:**
   - `pE_equiv`, `pV0_equiv`, `pE'_equiv` via `{ pE_fn with invFun := pE_inv, ... }` anonymous-constructor pattern.

6. **V0-isometry property:**
   - `pV0_iso : ∀ u v, S.formV0 (pV0_fn u) (pV0_fn v) = S.formV0 u v` from `_hpIso` at V0-pairs.

7. **Cross-pairing key identity:**
   - `hkey : ∀ e e', S.lambda (pE_fn e) (pE'_fn e') = S.lambda e e'` from `_hpIso`.

### Mathematical observation (NEW, important)

A direct attempt to close the final assembly reveals that the statement of `parabolic_decompose` as written is **strictly narrower than the full Levi decomposition**.

Setting `d := pE'_equiv`, `g := pV0_equiv`, `D e' := (p (0, 0, d.symm e')).2.1`:
- V0-component matches by definition of `D`.
- E'-component matches by construction of `d`.
- E-component requires:
  ```
  (p (0, v, 0)).1 = Cdual D (pV0_fn v)             ← follows from _hpIso + Cdual_pairing
  (p (0, 0, e')).1 = ½ Cdual D (D (pE'_fn e'))      ← does NOT follow from _hpIso
  ```

The isometry only forces (with `f e' := (p (0, 0, e')).1 - ½ Cdual D (D (pE'_fn e'))`):
```
λ(f e₁', pE'_fn e₂') + ε λ(f e₂', pE'_fn e₁') = 0  for all e₁', e₂'
```

This is the `IsSkewB`-shape of a residual skew `B'`, hence `f` is in general nonzero. A general parabolic isometry decomposes as
```
(uD D + B') ∘ leviGL_E d ∘ leviGL_V0 g
```
where `uD D` only captures the `B' = 0` case.

### Recommendation for Round 9 / polish stage

**Two options:**

(a) **Mathematically correct route (preferred):** generalise `uD` (or add a sister `uD_B`) to accept a residual skew `B' : E' →ₗ[F] E` satisfying `IsSkewB S B'`, and update `parabolic_decompose` to expose `(D, B', d, g)`.

(b) **Narrowing route:** keep the current signature and add a hypothesis that the residual `B'` vanishes.

Round 7 consumers (`residual_levi_extract`, `residual_levi_build`) already sidestepped `parabolic_decompose` via Option B in NormalForm.lean, so this signature change is **non-blocking** for the public theorems.

## Target — `InducedOrbitToy/Basic.lean`, `LocalForms.lean`, `X0Geometry.lean` ✅ NO WORK

All three "files NOT assigned this round" provers correctly verified isolation, wrote brief "no work" reports, and made no edits. Build remains green.

## Key findings / proof patterns discovered (Round 8)

1. **`noncomm_ring` for module-endomorphism associativity.** Where commutative `ring` fails, `noncomm_ring` closes any associativity goal on `Module.End F V`. Essential pattern. Future provers in this file should prefer it over manual `mul_assoc` chains.

2. **`Ring.inverse` for orbit/conjugation reasoning.** Pattern:
   - `Ring.inverse_mul_cancel _ hgU` (LHS cancel).
   - `Ring.mul_inverse_cancel _ hgU` (RHS cancel).
   - `IsUnit.ringInverse` (unit preservation).
   - `Ring.inverse (g * Ring.inverse p) = p * Ring.inverse g` via uniqueness from `(g * Ring.inverse p) * (p * Ring.inverse g) = 1`.

3. **`Ring.inverse` is the right packaging for "best-effort inverse" in orbit predicates** — no division-ring needed. Already in the gotchas list (Round 7 carry-forward).

4. **Orbit equality via single conjugating isometry — flag-stability NOT needed.** New `GOrbit_eq_of_isometry_conj` helper exposes this weakened hypothesis. Both inclusions transit through `g ↦ g * Ring.inverse p` (or dual).

5. **Diagonal-block extraction from `_hpUnit.unit.inv`.** When `p` preserves a flag, build the inverse maps `pE_inv`, `pV0_inv`, `pE'_inv` from `pinv := _hpUnit.unit.inv` and prove bijectivity via round-trip identities. Each round-trip uses a 3-step calc chain `target = p (pinv target) = p (block_inv ...) = (block_fn (block_inv ...), 0, 0)` reversed appropriately.

6. **`LinearEquiv` from `LinearMap` + inverse via anonymous-constructor.** `{ pE_fn with invFun := pE_inv, left_inv, right_inv }` packages a `LinearMap` + bijectivity proofs into a `LinearEquiv`. Cleaner than `LinearEquiv.ofBijective`.

7. **Mathematical gap discovery for `parabolic_decompose`.** The current statement is missing a `B'` parameter. This kind of finding — a *statement-level* gap rather than a *proof-level* one — is rare and very valuable. Documents the gap analysis in the file's docstring (lines 1088–1107) so future provers don't re-discover it.

8. **Cross-file parallel dispatch with no edit overlap.** Three provers worked simultaneously; mid-round build breakage was transient. End-of-round merge was clean. The plan agent's careful line-range partitioning (NormalForm 190–230, Orbits 292–630, Slice 1065–1574) made this possible.

## Recommendations for next session (Round 9)

See `recommendations.md` in this folder.

## Cumulative reduction (sessions 1–10)

22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → 4 (end of session 7) → 5 (end of session 8) → 3 (end of session 9) → **3 (end of session 10)**.

**Round 8 net: 0 declaration warnings.** Plan target was 3 → 0; achieved a structural reorganisation with no net closure but each remaining sorry now isolated to a focused helper. Round 9 has a clean 3-helper attack surface plus a flagged statement-level gap on `parabolic_decompose`.
