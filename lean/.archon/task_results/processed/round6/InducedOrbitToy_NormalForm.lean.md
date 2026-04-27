# InducedOrbitToy/NormalForm.lean — Round 6 (no-work)

## Status: NO WORK THIS ROUND

`PROGRESS.md` (Round 6) explicitly lists `NormalForm.lean` under
"Files NOT assigned this round":

> `InducedOrbitToy/NormalForm.lean` — 3 sorries deferred to Round 7. Do
> NOT edit this file in Round 6 (the proofs depend on `Slice.lean`'s
> Levi machinery being finalised first).

The harness still dispatched a prover here, so per protocol I:
1. verified the file compiles in isolation,
2. did not edit anything,
3. wrote this brief report.

## Verification (2026-04-28)

Ran `lake env lean InducedOrbitToy/NormalForm.lean`. Output:

```
InducedOrbitToy/NormalForm.lean:195:16: warning: declaration uses `sorry`
InducedOrbitToy/NormalForm.lean:319:16: warning: declaration uses `sorry`
InducedOrbitToy/NormalForm.lean:348:16: warning: declaration uses `sorry`
```

No errors. Exactly the 3 declaration-use `sorry` warnings expected at
end of Round 5 (`pNormalForm_witnesses`, `residual_levi_extract`,
`residual_levi_build`). Counts and locations unchanged.

## Why deferred

All three remaining sorries depend on Levi machinery that Round 6 is
adding to `Slice.lean`:

- `pNormalForm_witnesses` (line 195) needs `leviGL_E` / `leviGL_V0` /
  `levi_conj_XCB` to choose the `d ∈ GL(E')` block normalising
  `Cbar|_{L1'} = Sₕ` and `d(L0') = ker Cbar`.
- `residual_levi_extract` (line 319) needs `parabolic_decompose` to
  destruct an arbitrary parabolic `p` into `uD D ∘ leviGL_E d ∘ leviGL_V0 g₀`.
- `residual_levi_build` (line 348) needs `leviGL_E` and the perfect-pairing
  dual transpose `(h⁻¹)^∨` (which `lambdaDualE` from `levi.md` provides).

Running these proofs in Round 6 would race against an unfinalised Slice
API — the plan agent already documented this race in `PROGRESS.md` lines
60–66 as the deliberate justification for the one-round split.

## Next round (Round 7)

Round 7 should:
1. consume the finalised Slice Levi API (`lambdaDualE`, `leviGL_E`,
   `leviGL_V0`, `parabolic_decompose`),
2. close `pNormalForm_witnesses` per the plan in `task_pending.md`
   lines 49–70,
3. close `residual_levi_extract` per `task_pending.md` lines 72–82,
4. close `residual_levi_build` per `task_pending.md` lines 84–98,
5. refresh stale comments at NormalForm lines 344, 357 (noted in
   `task_pending.md` line 98).

## No file changes this round.
