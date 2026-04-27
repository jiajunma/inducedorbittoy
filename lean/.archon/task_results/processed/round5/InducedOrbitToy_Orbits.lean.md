# InducedOrbitToy/Orbits.lean

## Status (Round 5): NO WORK ASSIGNED

Per `PROGRESS.md` (Round 5 plan), `Orbits.lean` is **not assigned** this
round. The single remaining sorry — `sIndependenceAndOrbitCriterion`
(line 324) — is Tier A and explicitly deferred to **Round 7**, blocked
on `pNormalForm_residual_orbit_iso` being fully closed (which itself
depends on the Levi machinery scheduled for Round 6).

PROGRESS.md, "Files NOT assigned this round", line 570:

> `InducedOrbitToy/Orbits.lean` — `sIndependenceAndOrbitCriterion` is
> Round 7 (needs `pNormalForm_residual_orbit_iso` fully closed via
> Round 6's Levi machinery).

## Verification (no edits made)

- `lake env lean InducedOrbitToy/Orbits.lean` → 1 warning, the expected
  `Orbits.lean:324:8: warning: declaration uses 'sorry'`. No errors. No
  new warnings beyond the single tracked sorry.
- File contents unchanged this round.

## Why no edits

The prover-prover prompt in `PROGRESS.md` ("Files NOT assigned this
round") instructs that if the harness dispatches a prover to a
non-assigned file, the prover should:
1. verify the file compiles in isolation,
2. write a brief "no work" report,
3. **not edit anything**.

All three followed.

## Carry-forward note for Round 7

When `pNormalForm_residual_orbit_iso` lands (after Round 6's Levi
machinery), the `sIndependenceAndOrbitCriterion` proof at line 324 will
need:
- `Nondegenerate` and `(2 : F) ≠ 0` hypotheses likely added to the
  statement (per `task_pending.md` Tier A note);
- a reduction of the two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s
  existence half.

These are statement-level adjustments and should be flagged to the plan
agent before the Round 7 prover starts editing.
