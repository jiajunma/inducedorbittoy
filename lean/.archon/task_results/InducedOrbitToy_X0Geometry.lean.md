# InducedOrbitToy/X0Geometry.lean

## Status (Round 5): NO WORK

PROGRESS.md (Round 5) lists this file under "Files NOT assigned this
round": already done since session 4. Per the harness instructions for
unassigned dispatch, I verified the file in isolation and made no edits.

## Verification

- `lake env lean InducedOrbitToy/X0Geometry.lean` — succeeds; only
  output is the pre-existing unused-variable lint:
  ```
  InducedOrbitToy/X0Geometry.lean:221:35: warning: unused variable `hlambda`
  ```
  This is the expected, documented warning on `sDual_restrict_ker_isIso`
  (the `hlambda` hypothesis is part of the autoformalised statement and
  must not be removed — see PROGRESS.md "Verified State").
- `grep sorry` finds only one occurrence — line 28, inside the file's
  module docstring ("All proof obligations are left as `sorry` for the
  prover stage."). No `sorry` tactic remains in any declaration body.
- No edits made to `InducedOrbitToy/X0Geometry.lean`.

## Files unchanged

- `InducedOrbitToy/X0Geometry.lean` — untouched.

## Next steps

None for this round. Round 5's only objective is in
`InducedOrbitToy/NormalForm.lean` (Tier S #4 + close `kernelImage_ker`
+ `kernelImage_im`), which is owned by another prover.
