# InducedOrbitToy/Slice.lean — Round 9

## Status: NO WORK (verify-only per PROGRESS.md directive)

PROGRESS.md (Round 9) and `.archon/task_pending.md` lines 182–199 both
explicitly instruct the Slice prover this round to perform a verify-only
report and **not edit anything**.  Quoting PROGRESS.md:

> **Do NOT attempt to close `parabolic_decompose` with the current
> signature** — Round 8 analysis shows the statement is provable only
> when the residual `B' = 0`, which is not automatic for a general
> parabolic isometry.  The proper fix is a signature change (option
> (a): generalise `uD` with `B'` parameter; option (b): narrow the
> hypothesis), deferred to polish stage.  If a prover is dispatched:
> verify-only, "no work" report.

## Sorry inventory

`grep -n "sorry" InducedOrbitToy/Slice.lean` finds only one
declaration-use sorry in the file body:

| Line | Theorem | Status |
|------|---------|--------|
| 1572 (body of `parabolic_decompose` declared at line 1109) | `parabolic_decompose` | Deferred (Tier S #6); documented mathematical gap, not a plumbing issue. |

All other matches for `sorry` are inside docstrings/comments, not
declaration bodies.

## Compilation check

`lake env lean InducedOrbitToy/Slice.lean` succeeds with the single
expected warning:

```
InducedOrbitToy/Slice.lean:1109:8: warning: declaration uses `sorry`
```

No other warnings, no errors.  The file is in the same state as the end
of Round 8.

## Edits performed

None.  Per the directive, no `.lean` source was modified.

## Carry-forward (unchanged from Round 8)

The Round 8 Slice prover documented the gap in detail at lines 1062–1108
of the file (the long Gap docstring above `parabolic_decompose`) and in
`.archon/task_results/processed/round8/InducedOrbitToy_Slice.lean.md`
(archived).  The recommended fix for the polish stage is to generalise
`uD` (or add a sister `uD_B`) to accept a residual skew
`B' : E' →ₗ[F] E`, then update `parabolic_decompose` to expose
`(D, B', d, g)` as the decomposition data.

`parabolic_decompose` has zero internal consumers in the project
(verified by grep in prior rounds — Round 7's `residual_levi_extract`
and `residual_levi_build` sidestep it via Option B), so leaving the
sorry in place does not block public-theorem axiom hygiene for
`pNormalForm_residual_orbit_iso`, `inducedOrbits`, or the
`multiplicity*` theorems.

## Axioms

No axioms introduced (no edits this round).  Public-theorem axiom
audit per PROGRESS.md remains:

- `pNormalForm_residual_orbit_iso`, `inducedOrbits`,
  `multiplicityNonDeg`, `multiplicityOddCase`,
  `multiplicityEvenSymmCase` — clean
  (`[propext, Classical.choice, Quot.sound]`).
