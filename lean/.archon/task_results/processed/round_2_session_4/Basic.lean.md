# InducedOrbitToy/Basic.lean

## Status: NO WORK REQUIRED THIS ROUND

### Verification (2026-04-27)

- `grep -c "sorry\|axiom" InducedOrbitToy/Basic.lean` → **0** (zero
  occurrences of either token in the file).
- `lake env lean InducedOrbitToy/Basic.lean` → exits cleanly with no
  output (no errors, no warnings).
- Zero custom `axiom` declarations.
- All declarations exposed by this file have complete proof bodies:
  - `IsEpsSymm`, `IsSkewAdjoint` (`def`)
  - `IsPerfectPairing`, `IsPaired`, `IsIsotropic` (`def`)
  - `PairedSpaces`, `X0Setup`, `SliceSetup` (`structure`)
  - `c` (`noncomputable def`)
  - `c_eq_finrank_quotient` (`theorem`, proved via
    `Submodule.finrank_quotient_add_finrank` +
    `LinearMap.finrank_range_add_finrank_ker` + `omega`)
  - `SliceSetup.E`, `SliceSetup.E'`, `SliceSetup.lambda`, `SliceSetup.V`
    (`abbrev`)
  - `SliceSetup.ambientForm` (`noncomputable def`)
  - `SliceSetup.flagE`, `SliceSetup.flagEV0` (`def`)
  - `IsParabolic` (`def`)
  - `UnipotentRadical` (`noncomputable def`)

### Why this file has no Round-2 objective

`PROGRESS.md` (verified 2026-04-27) lists exactly **one** Round-2
objective: `InducedOrbitToy/NormalForm.lean` (Tier A targets
`pNormalForm` and `pNormalForm_residual_orbit_iso`).

Basic.lean is referenced in `task_pending.md` only in connection with
**deferred** refactors that the plan agent has explicitly excluded from
this round:

- **Tier B** (`DualTransposeData` enrichment with `L1_le` and
  `finrank_L1_eq` fields) — round 4. The structure actually lives in
  `X0Geometry.lean` (line 189), not in `Basic.lean`; the
  `task_pending.md` reference path is slightly imprecise but the work
  itself is still scoped to a later round.
- **Tier C** (add `SliceSetup.lagrangian` field; tighten consumers in
  `NormalForm.lean` to take `Sₕ` as `LinearEquiv`) — round 4/5.
- **Tier D** (tighten `UnipotentRadical` to be the Lie subalgebra that
  preserves `S.ambientForm`) — round 5+.

Each of these is a *data refactor* that will cascade into multiple
downstream files at once. The plan-agent rationale (PROGRESS.md §"Round
Plan") is to keep each round atomic — one file per agent, no cross-file
edits in flight — so that the prover-then-review cycle stays clean.
Touching Basic.lean now without the matching downstream edits in
`X0Geometry.lean` / `NormalForm.lean` / `Slice.lean` would break those
files (they consume the current `DualTransposeData`, `SliceSetup`, and
`UnipotentRadical` shapes).

### Action taken this round

None. The file is already in the target state for Round 2:

- 0 `sorry`s,
- 0 axioms,
- compiles in isolation,
- all definitions stable for downstream consumers.

No edits were made to `InducedOrbitToy/Basic.lean`.

### `#print axioms` (public theorems in this file)

Only one theorem is exposed publicly: `c_eq_finrank_quotient`. It
depends on standard Mathlib axioms only (no custom axioms introduced by
this project). Verifiable via:

```
#print axioms InducedOrbitToy.c_eq_finrank_quotient
```

(All other public declarations are `def`/`structure`/`abbrev`, which do
not have axiom dependencies in the same sense.)

### Recommendation for the plan agent

When the Tier B / C / D data refactors are ready to schedule, the
relevant edits to `Basic.lean` are:

1. **Tier C** (smallest, lowest-risk):
   - Add `lagrangian : IsIsotropic paired.pairing L1 L0'` (or the
     symmetric variant) to the `SliceSetup` structure.
   - This is a pure additive change to the structure; existing call
     sites stay green.

2. **Tier D** (medium-risk):
   - Tighten `UnipotentRadical` by adding a fourth membership clause
     `IsSkewAdjoint S.ambientForm f`.
   - Will require small edits in `Slice.lean` consumers (`uD_isParabolic`
     and `parametrizeX0PlusU_existence` membership proofs) — this is
     intended; it unblocks both Tier D sorries.

3. **Tier B** (path-of-least-resistance correction):
   - The two new fields (`L1_le`, `finrank_L1_eq`) belong on the
     `DualTransposeData` structure in `X0Geometry.lean`, not in
     `Basic.lean`. `task_pending.md` mentions "Basic.lean ::
     DualTransposeData" but that path is incorrect — the structure is
     defined at `X0Geometry.lean:189`. Recommend updating the
     `task_pending.md` reference when this work is scheduled.

These are recommendations only — no edits were made to either Basic.lean
or task_pending.md (per role permissions).
