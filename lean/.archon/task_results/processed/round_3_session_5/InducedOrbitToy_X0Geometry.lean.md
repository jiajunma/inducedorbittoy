# InducedOrbitToy/X0Geometry.lean

## Round 3 — no work

This file was **not** assigned this round. PROGRESS.md (round 3, lines
274–292) lists `X0Geometry.lean` under "Files NOT assigned this round"
and notes it was closed in session 4. The harness dispatched a prover
anyway; per the round-3 protocol the prover must verify isolation
compilation, write a brief "no work" report, and **not edit anything**.

### Verification (no edits)

- `lake env lean InducedOrbitToy/X0Geometry.lean` (run from the
  project root): compiles cleanly. Only output is the pre-existing
  unused-variable lint:

  ```
  InducedOrbitToy/X0Geometry.lean:221:35: warning: unused variable `hlambda`
  ```

  PROGRESS.md (lines 24–28) says this lint is expected — `hlambda` is
  part of the autoformalised statement of `sDual_restrict_ker_isIso`,
  so it is left in the signature on purpose. **Do not remove.**

- `grep -n "sorry" InducedOrbitToy/X0Geometry.lean` finds exactly one
  match, at line 28, inside the file's docstring (legacy comment from
  the autoformalisation stage):

  ```
  All proof obligations are left as `sorry` for the prover stage.
  ```

  No `sorry` term-mode placeholder remains in any declaration body.

### Sorries

None. The five public theorems / definitions in this file —
`ker_le_orthogonal_range`, `orthogonal_range_eq_ker`,
`finrank_quotient_range_eq_finrank_ker`, `finrank_Vplus_eq_c`,
`VplusEquivQuotientRange`, `vplusKerPairing`,
`vplusKerPairing_isPerfPair`, `sDual_restrict_ker_isIso`,
`x0Geometry`, plus the `DualTransposeData` structure — are all fully
proved and were closed in earlier rounds (most recently session 4).

### Axioms

No new axioms introduced (no edits). PROGRESS.md (line 30) confirms
`#print axioms` on every public theorem in this file lists only
`[propext, Classical.choice, Quot.sound]`.

### Files modified this turn

None. The only filesystem write performed by this prover was this
report file.

### Hand-off

Nothing to hand off. Round 3's two assigned files are
`InducedOrbitToy/Slice.lean` (Tier S #1, half 1) and
`InducedOrbitToy/NormalForm.lean` (Tier S #1, half 2); see
PROGRESS.md sections "Current Objectives (Round 3)" #1 and #2 for the
active work.
