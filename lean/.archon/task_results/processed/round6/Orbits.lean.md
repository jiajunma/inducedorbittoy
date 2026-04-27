# InducedOrbitToy/Orbits.lean

## Round 6 status: NO WORK

Per `PROGRESS.md` (Round 6 plan), `Orbits.lean` is **NOT assigned** this
round. The remaining sorry at line 324
(`sIndependenceAndOrbitCriterion`) is deferred to Round 8 because it
depends on `pNormalForm_residual_orbit_iso` being fully closed via
Round 7's `NormalForm.lean` work, plus parabolic-decomposition machinery
that Round 6 is just now adding to `Slice.lean`.

Following the harness fallback protocol for unassigned files, I:
- Verified the file compiles in isolation:
  `lake env lean InducedOrbitToy/Orbits.lean` produces only the single
  expected warning
  `InducedOrbitToy/Orbits.lean:324:8: warning: declaration uses 'sorry'`.
- Did **not** edit `Orbits.lean` or any other file.
- Did **not** introduce any `axiom`.

## Remaining sorry

- Line 324 — `sIndependenceAndOrbitCriterion` (Tier A, deferred to
  Round 8). The forward direction needs (a) a parabolic-decomposition
  argument proving any `g ∈ G` conjugating `XST T₁` to `XST T₂` is a
  `P`-element (Round 6's new Levi machinery in `Slice.lean` will supply
  this), and (b) `pNormalForm_residual_orbit_iso` fully closed (Round 7
  in `NormalForm.lean`). The current statement also lacks
  `S.formV0.Nondegenerate` and `(2 : F) ≠ 0`, which the plan agent has
  flagged as required additions before Round 8 can succeed.

## Next step (for the planning of Round 8, not for this round)

After Rounds 6 and 7 land:
- Confirm `Slice.lean` exposes `parabolic_decompose` (Round 6 helper 8)
  in usable form.
- Confirm `NormalForm.lean :: pNormalForm_residual_orbit_iso` is
  sorry-free (Round 7).
- Augment the statement of `sIndependenceAndOrbitCriterion` with
  `(hNondeg : S.formV0.Nondegenerate)` and `(hChar : (2 : F) ≠ 0)` (and
  resolve the `Sₕ₁ vs Sₕ₂` mismatch flagged in the in-file comment) —
  this is a statement-shape change and must be proposed by the plan
  agent, not by the prover.
- Then close the iff in two parts: forward via `parabolic_decompose` +
  `pNormalForm_residual_orbit_iso`; backward via the explicit conjugator
  built from the bilinear isometry.
