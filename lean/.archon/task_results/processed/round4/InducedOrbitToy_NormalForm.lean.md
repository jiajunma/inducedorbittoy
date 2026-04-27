# InducedOrbitToy/NormalForm.lean

## Status: NO WORK THIS ROUND (Round 4)

Per `PROGRESS.md` (Round 4 plan, lines 56–66 and 488–507): `NormalForm.lean`
is **not assigned** this round. Round 4's three objectives are restricted to
`Basic.lean` (Tier S #2 + Tier S #3), `Slice.lean`
(`parametrizeX0PlusU_existence`), and `Orbits.lean` (cascade for the
tightened `UnipotentRadical`). All 5 remaining sorries in this file are
blocked on later rounds:

| Theorem (line) | Tier | Blocker | Round |
|---|---|---|---|
| `pNormalForm_witnesses` (195) | A | Levi-action machinery (additive in `Slice.lean`) | 6 |
| `residual_levi_extract` (319/330) | A | Levi/unipotent decomposition lemma `parabolic_decompose` | 6 |
| `residual_levi_build` (348/363) | A + S #3 | Lagrangian fields (S #3) + Levi machinery | 6 |
| `kernelImage_ker` (495, 2 internal sorries lines 537/543) | C + S #3 + S #4 | `Sₕ : LinearEquiv` retype (S #4) + `λ(L1, L0') = 0` (S #3) | 5 |
| `kernelImage_im` (590) | C + S #3 | `λ(L1, L0') = 0` (S #3) + `sDual_restrict_ker_isIso` (already done) | 5 |

The Round 4 changes that touch `Basic.lean`'s `SliceSetup` are described
as "purely additive" (Tier S #3, `task_pending.md` lines 71–73): new
fields `L0_paired`, `L1_isotropic_L0'`, `L0_isotropic_L1'` are added but
no field that `NormalForm.lean` currently consumes is removed or
retyped. The `UnipotentRadical` tightening (Tier S #2) is consumed only
by `Slice.lean :: parametrizeX0PlusU_existence` and
`Orbits.lean :: XCB_sub_X0Lift_mem_unipotent` /
`XST_sub_X0Lift_mem_unipotent`; `NormalForm.lean` does not construct or
destructure any `UnipotentRadical` members in the current code, so it
should be insulated from that cascade as well.

## Verification

- Ran `grep -n "sorry" InducedOrbitToy/NormalForm.lean`: confirmed 5
  declaration-use `sorry`s at lines 210, 330, 363, 537/543 (counting as
  one `theorem`-level sorry each at 495), and 595, matching
  `PROGRESS.md` lines 41–44.
- File line count: 630 lines, unchanged from start of round.
- **No edits made** to `InducedOrbitToy/NormalForm.lean` this round.

## Cross-file build expectations

Mid-round build breakage is expected per `PROGRESS.md` lines 522–540:
the `Basic.lean` / `Slice.lean` / `Orbits.lean` triad will go through a
3-tuple-vs-4-tuple `obtain` mismatch window before all three sister
provers land. `NormalForm.lean` does not depend on the
`UnipotentRadical` 4-tuple destructure or on the `XCB_sub_X0Lift_mem_unipotent`
helper, and its imports flow only from `InducedOrbitToy.Slice`. If
`Slice.lean` is mid-flight, `NormalForm.lean` may transitively fail to
import; this is expected and resolves at end of round.

## Next session prep (Round 5 — when `NormalForm.lean` re-enters scope)

The Round 5 objective per `PROGRESS.md` line 60 is **Tier S #4 + close
`kernelImage_ker`, `kernelImage_im`**. When that round begins:

1. **First:** retype `kernelImage_ker`'s `Sₕ` from
   `S.L1' →ₗ[F] S.Vplus` to `S.L1' ≃ₗ[F] S.Vplus` (mirroring
   `kernelImage_im` at line 592).
2. **Audit caller:** check `Orbits.lean` for any callers of
   `kernelImage_ker` and adjust to pass a `LinearEquiv`.
3. **Close lines 537/543:** with `Sₕ` an iso, `Sₕ.injective` gives
   `projL1' e' = 0` from `hSh_zero` (lines 526–529). Then
   `e' = projL0' e'` (decomposition `E' = L1' ⊕ L0'`), and the equation
   `Cdual (CST Sₕ) v + (T (projL0' e') : E) = 0` (line 506) splits via
   the Lagrangian condition `λ(L1, L0') = 0` (the new
   `S.L1_isotropic_L0'` field): `Cdual (CST Sₕ) v ∈ L1` because
   `Cdual` lands in the perp of `L0'` w.r.t. `λ`, and `(T x : E) ∈ L0`,
   so by `IsCompl L1 L0` both summands are 0 individually, giving
   `v = 0` (via `sDual_restrict_ker_isIso` applied to `Cdual (CST Sₕ)`)
   and `T (projL0' e') = 0`.
4. **Close line 595 (`kernelImage_im`):** the constructive direction
   builds preimages using `sDual_restrict_ker_isIso` (already closed in
   session 4 per `task_done.md`); the reverse direction uses
   `λ(L1, L0') = 0` to confine `Cdual (CST Sₕ) v` to `L1`.

## Notes

- Confirmed via `lean_local_search` etc. is unnecessary at this stage —
  no edits to verify.
- No new `axiom` introduced (no edits).
- File unchanged: `git status` should show no diff for
  `InducedOrbitToy/NormalForm.lean`.
