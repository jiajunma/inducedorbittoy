# InducedOrbitToy/Orbits.lean

## Status (Round 6): NO WORK — file deferred to Round 8

Per `PROGRESS.md` Round 6 plan, `Orbits.lean` is in the
"Files NOT assigned this round" list. The single remaining
`sorry` (declaration-use warning at line 324, with the two
inner `sorry` term lines at 358 and 376) is on
`sIndependenceAndOrbitCriterion`, whose closure depends on
`pNormalForm_residual_orbit_iso` in `NormalForm.lean` being
fully closed first. That work is itself blocked behind the
Round 7 closure of `pNormalForm_witnesses`,
`residual_levi_extract`, and `residual_levi_build`, which in
turn consumes the Levi-action machinery being added to
`Slice.lean` this round.

Per the prover-prover prompt and the explicit Round-6
instructions, I:
- did NOT edit `InducedOrbitToy/Orbits.lean` (or any other file);
- verified the file compiles in isolation;
- verified the project still builds green;
- recorded this no-op report.

## Verification

- `lake env lean InducedOrbitToy/Orbits.lean` → one warning:
  `InducedOrbitToy/Orbits.lean:324:8: declaration uses `sorry``
  (matches Round-5 baseline; line numbers unchanged).
- `lake build` → `Build completed successfully (8033 jobs).`
  Total declaration-use `sorry` warnings: 4 (3 in
  `NormalForm.lean` lines 195/319/348, 1 in `Orbits.lean`
  line 324) — exactly the Round-5 baseline. Plus one new
  warning in `Slice.lean:1078` from this round's Levi
  additions, which is acceptable per the Round 6 acceptance
  criteria (`parabolic_decompose` may carry an extra `sorry`).

## Next session note

Once Round 7 closes the three NormalForm sorries and
`pNormalForm_residual_orbit_iso` is sorry-free with the
right hypothesis list (`S.formV0.Nondegenerate` + `(2 : F) ≠ 0`,
plus a parabolic-decomposition argument linking
`g ∈ G` conjugating `XST T₁` to `XST T₂` to a `P`-element),
Round 8 will:

1. Forward direction (line 358 sorry):
   - From `_hg : IsometryEnd S _g` and the conjugation
     equation `_hyeq`, show `_g ∈ P` (i.e. `IsParabolicElement
     S _g`). This is the parabolic-decomposition step; it
     consumes `parabolic_decompose` from Slice.lean once that
     is sorry-free, plus the slice-stability argument
     requiring `Nondegenerate`/`(2 : F) ≠ 0`.
   - Apply `pNormalForm_residual_orbit_iso` to get the
     bilinear isometry `h : L0' ≃ₗ[F] L0'` matching `BT T₁`
     and `BT T₂`.
   - Repackage as `IsometryRel S T₁ T₂`.

2. Reverse direction (line 376 sorry):
   - Apply `pNormalForm_residual_orbit_iso` to lift
     `_h : L0' ≃ₗ[F] L0'` (from `IsometryRel`) to a
     `P`-element `p` with `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p`.
   - Use `IsParabolicElement → IsometryEnd` (parabolic ⊂
     isometry group) to membership-witness `p` for `GOrbit`.
   - Mutual inclusion of orbits.

Both directions need the missing hypotheses
(`Nondegenerate`, `(2 : F) ≠ 0`, `Sₕ₁ = Sₕ₂`) added to the
theorem statement, OR a strengthening of
`pNormalForm_residual_orbit_iso` to absorb them. The plan
agent should decide whether to (a) add hypotheses to
`sIndependenceAndOrbitCriterion` directly, or (b) restate
`pNormalForm_residual_orbit_iso` to fold them in. Option (b)
is preferable because it keeps the public statement of
`sIndependenceAndOrbitCriterion` clean.

## Files touched this round

None. No edits to `Orbits.lean` or any other file.

## Axioms

`#print axioms` not re-checked this round (no new
declarations closed). Round-5 baseline holds: every
sorry-free public theorem in this file uses only
`[propext, Classical.choice, Quot.sound]`.
