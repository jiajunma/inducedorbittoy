# InducedOrbitToy/Slice.lean — Round 10 (no work, verify-only)

## Status

**No code edits made this round.** Per `PROGRESS.md` Round 10 explicit
instruction:

> `InducedOrbitToy/Slice.lean` — `parabolic_decompose` (line 1109)
> carries a documented mathematical gap (Tier S #6, deferred).
> **Do NOT attempt to close `parabolic_decompose` with the current
> signature.** If a prover is dispatched: verify-only, "no work"
> report.

The Round 8 Slice prover identified a genuine mathematical gap: the
unipotent factor in the blueprint's `p = u_D · m` decomposition must
include a residual skew `B' : E' →ₗ E` term, but the current `uD D`
definition zero-sets this component. Plan-agent decision is to defer
the fix to the polish stage (option (a) generalise `uD`, or option (b)
narrow the hypothesis). `parabolic_decompose` has zero in-project
consumers, so the deferral is non-blocking for public theorem closure.

## Verification

- `lake env lean InducedOrbitToy/Slice.lean` runs cleanly with a single
  declaration-use warning:

  ```
  InducedOrbitToy/Slice.lean:1109:8: warning: declaration uses `sorry`
  ```

  The sorry is at line 1572 inside `parabolic_decompose`, exactly the
  deferred gap.

- Total `sorry` occurrences in the file body: **1** (line 1572 inside
  `parabolic_decompose`). All other `sorry` mentions in the file are
  inside docstring comments documenting the gap.

- No `/- USER: ... -/` comments present.

- No new `axiom` declarations introduced (none can be — the file was
  not edited).

## File-level inventory (carried forward, unchanged from Round 9)

The Slice.lean file in its current state contains the following
sorry-free Round 6 / Round 7 / Round 8 deliverables that NormalForm.lean
(Round 10 primary objective) depends on:

- Round 6 Levi machinery: `lambdaDualE`, `lambdaDualE_pairing_eq`,
  `leviGL_E`, `leviGL_E_apply`, `leviGL_E_isParabolic`,
  `leviGL_E_conj_XCB`, `leviGL_E_symm_inverse`.
- Unipotent half: `parametrizeX0PlusU_existence`,
  `parametrizeX0PlusU_uniqueness`, `uD`, `uD_apply`, `uD_neg_inverse`,
  `uD_conj_XCB`, `uD_isParabolic`.

These are stable and consumed by `NormalForm.lean :: pNormalForm_witnesses_aux`
(currently Round 10 primary). No changes required this round.

## Outstanding work for polish stage

The Tier S #6 signature change for `parabolic_decompose` is documented
in detail in:

- `task_pending.md` Tier S #6 section.
- The in-file docstring at lines 1062–1108 of `Slice.lean`.

Polish-stage prover should pick option (a) (generalise `uD` to take an
extra `B'` parameter) or option (b) (add a hypothesis that the residual
`B'` is zero), then close the line 1572 sorry under the new statement.

## Confirmation

- `lake env lean InducedOrbitToy/Slice.lean` ⇒ compiles, single
  declaration-use sorry warning at line 1109 (inside theorem body at
  1572).
- File untouched this round.
- No regressions introduced.
