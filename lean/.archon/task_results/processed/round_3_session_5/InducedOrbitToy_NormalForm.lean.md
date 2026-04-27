# InducedOrbitToy/NormalForm.lean — Round 3 (Tier S #1, half 2)

## Summary

Implemented the assigned Tier S #1 fix for `NormalForm.lean`:

1. **Statement edit** — `IsParabolicElement`'s 4th conjunct changed from
   `LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p`
   (self-adjoint, false in general) to
   `LinearMap.IsOrthogonal S.ambientForm p` (the genuine isometry
   condition; matches `IsometryEnd` already used in `Orbits.lean`).
2. **Sorry closed** — `pNormalForm`'s line-272 inheritance sorry (now at
   ~line 270) replaced with a proof that chains the (sister-prover's
   corrected) `uD_isParabolic` first conjunct
   `IsAdjointPair (uD D) (uD (-D))` with `uD_neg_inverse` to evaluate
   `uD (-D) ∘ uD D = id`.
3. **Docstring updates** — both `IsParabolicElement` and the now-stale
   "Tier D blocker" reference in `residual_levi_build`.

**Sorry count:** 6 → 5 ✅ (per acceptance criteria).

## Statements changed

### `IsParabolicElement` (lines 85–88)

Changed 4th conjunct:
```diff
- LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p
+ LinearMap.IsOrthogonal S.ambientForm p
```

Updated docstring to reflect the new (correct) semantics: "p is an
isometry of the ambient form (`LinearMap.IsOrthogonal S.ambientForm p`)",
matching the `IsometryEnd` shape already used in `Orbits.lean:34`.

### `residual_levi_build` (lines 348–362)

Body unchanged (still bare `sorry`). Inline comment updated to remove the
now-stale "Tier D inheritance" remark: after this round, the
`IsParabolicElement` 4th conjunct is genuinely correct, so the only
residual blocker for `residual_levi_build` is the perfect-pairing dual
machinery (Tier S #3, deferred to Round 4 / 5).

## Per-target detail

### `pNormalForm` IsOrthogonal conjunct (was line 272 sorry, now lines 266–284)

#### Approach
- **RESOLVED.** Used the strategy from `PROGRESS.md`: chain
  `uD_isParabolic`'s 1st conjunct (after Slice prover lands the
  Tier S #1 fix) with `uD_neg_inverse` via `congrArg`.

#### Proof body
```lean
· -- LinearMap.IsOrthogonal S.ambientForm (uD S D)
  intro u v
  have hAdj :
      LinearMap.IsAdjointPair S.ambientForm S.ambientForm
          (uD S D) (uD S (-D)) :=
    (uD_isParabolic S _hNondeg _hChar D).1
  have hinv : uD S (-D) ∘ₗ uD S D = LinearMap.id := by
    have := uD_neg_inverse S _hNondeg _hChar (-D)
    simpa [neg_neg] using this
  have hinv_apply : ∀ w, uD S (-D) (uD S D w) = w := by
    intro w
    have := congrArg (fun f : Module.End F S.V => f w) hinv
    simpa using this
  calc S.ambientForm (uD S D u) (uD S D v)
      = S.ambientForm u (uD S (-D) (uD S D v)) := hAdj u (uD S D v)
    _ = S.ambientForm u v := by rw [hinv_apply]
```

#### Mathlib lemmas / facts used
- `LinearMap.IsAdjointPair B B' f g` unfolds to
  `∀ x y, B' (f x) y = B x (g y)` — verified via `lean_run_code` round-trip.
- `LinearMap.IsOrthogonal B f` unfolds to `∀ x y, B (f x) (f y) = B x y`
  — verified via `lean_run_code` (`rfl` round-trip).
- `uD_neg_inverse S _hNondeg _hChar (-D)` gives `uD S (-D) ∘ₗ uD S D = id`
  after `neg_neg` rewriting.

#### Verification of proof structure (independent of Slice prover)

Ran a self-contained `lean_run_code` snippet matching the proof shape:

```lean
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (f g : Module.End R M)
    (hAdj : LinearMap.IsAdjointPair B B f g)
    (hinv_apply : ∀ w, g (f w) = w) :
    LinearMap.IsOrthogonal B f := by
  intro u v
  calc B (f u) (f v)
      = B u (g (f v)) := hAdj u (f v)
    _ = B u v := by rw [hinv_apply]
```

Result: ✅ no diagnostics — the proof structure is sound.

## Cross-file dependency status (mid-round, expected)

`lake env lean InducedOrbitToy/NormalForm.lean` currently reports **one
error** at line 274:

```
Type mismatch
  (uD_isParabolic S _hNondeg _hChar D).left
has type
  IsAdjointPair S.ambientForm S.ambientForm ⇑(uD S D) ⇑(uD S D)
but is expected to have type
  IsAdjointPair S.ambientForm S.ambientForm ⇑(uD S D) ⇑(uD S (-D))
```

This is **expected per `PROGRESS.md` "Coordination notes for Round 3
(parallel-safety)"**: my IsOrthogonal proof depends on the sister
prover's update to `Slice.lean :: uD_isParabolic` (also Round 3 / Tier S
#1) which changes the first conjunct of `uD_isParabolic` from
`IsAdjointPair (uD D) (uD D)` to `IsAdjointPair (uD D) (uD (-D))`.

The error will resolve automatically when the sister prover lands its
half. End-of-round `lake build` will be green.

All other diagnostics in `NormalForm.lean` are 5 declaration-use `sorry`
warnings (line numbers shifted by ~7 lines because the proof body
expanded from `sorry` to the calc chain):

- line 195: `pNormalForm_witnesses` (Tier A — Round 4) — untouched
- line 319: `residual_levi_extract` (Tier A — Round 4) — untouched
- line 348: `residual_levi_build` (Tier A + S #3 — Round 4 / 5) —
  comment updated, body untouched
- line 495: `kernelImage_ker` (Tier C — Round 4 / 5) — untouched
- line 590: `kernelImage_im` (Tier C — Round 4 / 5) — untouched

No new sorries introduced.

## Untouched declarations (per round assignment)

The following sorries were explicitly listed as **not to be touched**
this round:

- `pNormalForm_witnesses` (line 195, Tier A) ✅ untouched
- `residual_levi_extract` (line 319, Tier A) ✅ untouched
- `residual_levi_build` (line 348, Tier A + S #3) ✅ body untouched
  (only inline comment about now-resolved Tier D blocker updated)
- `kernelImage_ker` (line 495, Tier C) ✅ untouched
- `kernelImage_im` (line 590, Tier C) ✅ untouched

The signatures, helper lemmas (`isUnit_uD`, `map_uD_eq_of_le`,
`XST_apply`, `kerXST_submod_le_ker`, `submoduleProdEquiv`,
`finrank_submodule_prod`), and all working proofs are also unchanged.

## Side-effect review of other `IsParabolicElement` consumers

After the definition change, every site that *consumes* the predicate
needed verification:

- `pNormalForm` (line 236) — produces `IsParabolicElement`; the new
  IsOrthogonal conjunct is discharged in the body (above).
- `residual_levi_extract` (line 321) — consumes `IsParabolicElement S p`
  as a hypothesis (`_hP`), body is whole-statement `sorry`. **No change
  needed**; underscore-prefixed binding doesn't care about which
  predicate field is which.
- `residual_levi_build` (line 348) — produces `IsParabolicElement S p`
  in its existential conclusion; body is whole-statement `sorry`. **No
  change needed**; the `sorry` discharges the entire conclusion.
- `pNormalForm_residual_orbit_iso` (line 388) — uses
  `IsParabolicElement` only in the iff statement; body delegates to
  `residual_levi_extract` / `residual_levi_build`. **No change needed**.

## Negative results / things tried

- Considered using `LinearEquiv.isAdjointPair_symm_iff`
  (`IsAdjointPair B B f f.symm ↔ IsOrthogonal B f`) to convert
  symmetrically. Rejected: requires `uD S D` packaged as a `LinearEquiv`,
  which would entail extra plumbing via `isUnit_uD` and `Units` to extract
  the inverse as `LinearEquiv.symm`. The direct calc chain is shorter
  and avoids the LinearEquiv wrapping.
- Tried using just `(uD_isParabolic …).1 u (uD S D v)` directly in
  the calc step without the intermediate `hAdj` binding — possible but
  less readable; the explicit `hAdj` makes the type-correction
  dependency on Slice's Tier S #1 update clearer to future agents.

## Acceptance criteria checklist

- ✅ `IsParabolicElement` 4th conjunct uses `LinearMap.IsOrthogonal`.
- ✅ `pNormalForm` line-272 sorry closed (replaced with calc chain).
- ✅ All other sorries unchanged (lines 195, 319, 348, 495, 590).
- ✅ Sorry count: 6 → 5 (one closed).
- ⏳ File compiles in isolation: 1 cross-file type-mismatch error at
  line 274, expected per parallel-safety notes; resolves when sister
  prover (Slice.lean) lands the corrected `uD_isParabolic` signature.
- ⏳ `lake build` is green: depends on sister prover landing.
- ✅ No new `axiom` declarations introduced (no `axiom` keyword used;
  only added a calc chain and updated a definition + docstring).
- ✅ Helpers `isUnit_uD`, `map_uD_eq_of_le`, `XST_apply`,
  `kerXST_submod_le_ker`, `submoduleProdEquiv`, `finrank_submodule_prod`
  unchanged.

## Reusable gotchas (for next round)

- **`LinearMap.IsAdjointPair B B' f g` direction**: unfolds to
  `∀ x y, B' (f x) y = B x (g y)` (the `B'`-applied side is on the
  *function-image* side). With `B = B'`, this reads
  `B (f x) y = B (x) (g y)`.
- **`LinearMap.IsOrthogonal B f` is `rfl`-equal to
  `∀ x y, B (f x) (f y) = B x y`** — `intro u v` works directly without
  `unfold IsOrthogonal`.
- **Cross-file Tier S coupling**: when a definition change in file X
  forces a calc-chain change in file Y, the `lean_run_code` MCP tool can
  verify the proof structure independently with hypothetical inputs of
  the correct shape. Useful for sanity-checking before the sister file
  lands.
