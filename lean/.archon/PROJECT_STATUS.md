# Project Status

## Overall Progress

- **Stage:** prover (round 2 complete; 9 declaration-use sorries remain).
- **Build state:** `lake build` succeeds (green, end of session 4).
- **Custom axiom declarations:** 0. All public theorems depend only on
  `[propext, Classical.choice, Quot.sound]` (`sorryAx` appears only on
  declarations that still embed an explicit `sorry`).
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4).
  Net session 4: +1 declaration count, but with one Tier-B target resolved
  (X0Geometry) and two Tier-A targets restructured into focused helpers
  (NormalForm), shrinking the genuinely missing surface area.

## Solved this session (session 4)

- `X0Geometry.lean :: sDual_restrict_ker_isIso` — resolved by enriching
  `DualTransposeData` (in this file, not `Basic.lean` as previously
  thought) with two new fields `range_le_L1` and `finrank_L1_eq`.
- `NormalForm.lean :: isUnit_uD` (helper) — `IsUnit (uD S D)` via
  `Units.mkOfMulEqOne` (avoiding the deprecated `LinearMap.mul_eq_one_of_mul_eq_one`).
- `NormalForm.lean :: map_uD_eq_of_le` (helper) — `Submodule.map (uD D) F = F`
  from inclusions both ways.
- Two flag-preservation conjuncts of `Slice.lean :: uD_isParabolic`
  (lines ≈462, ≈468) — newly proven this session.
- V₀ and E' Prod components of `Slice.lean :: parametrizeX0PlusU_existence`
  — newly closed (only the false E component remains as sorry).
- Forward and reverse witness extraction in `Orbits.lean :: sIndependenceAndOrbitCriterion`
  — both directions now have explicit `obtain` lines extracting the
  conjugating isometry / bilinear isometry from the hypothesis.

## Solved earlier (sessions 1–3, carry-forward)

(See `proof-journal/sessions/session_3/summary.md` for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- `NormalForm.lean :: kernelImage_dim` (rank-nullity).
- `Orbits.lean :: inducedOrbits`, `main` (block-matrix point lemmas).
- 7 of 9 sorries in `Slice.lean` (`Cdual`, `Cdual_pairing_eq`, `parametrizeX0PlusU_mem`, `parametrizeX0PlusU_uniqueness`, `uD`, `uD_neg_inverse`, `uD_conj_XCB`).
- `X0Geometry.lean :: vplusKerPairing_isPerfPair`.

## Remaining sorries (9 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `Slice.lean` | 232 | `parametrizeX0PlusU_existence` | D | **DO NOT RETRY** — needs `Basic.lean :: UnipotentRadical` tightened to enforce skew-adjointness |
| `Slice.lean` | 442 | `uD_isParabolic` | D | **DO NOT RETRY** — needs IsAdjointPair conjunct changed from `(uD D, uD D)` to `(uD D, uD (-D))` |
| `NormalForm.lean` | 196 | `pNormalForm_witnesses` (private helper) | A | needs Levi-action machinery added to `Slice.lean` |
| `NormalForm.lean` | 237 | `pNormalForm` (IsAdjointPair conjunct only, internal sorry) | D inheritance | unblocked when `uD_isParabolic` IsAdjointPair statement is fixed |
| `NormalForm.lean` | 307 | `residual_levi_extract` (private helper) | A | needs Levi-decomposition lemma + Levi machinery |
| `NormalForm.lean` | 336 | `residual_levi_build` (private helper) | A | needs Lagrangian condition `λ(L0, L0') = 0` added to `SliceSetup` |
| `NormalForm.lean` | 482 | `kernelImage_ker` | C | needs Lagrangian + `Sₕ` typed as `LinearEquiv` |
| `NormalForm.lean` | 577 | `kernelImage_im` | C | same blocker as `kernelImage_ker` |
| `Orbits.lean` | 242 | `sIndependenceAndOrbitCriterion` | A (deferred) | unblocked once `pNormalForm_residual_orbit_iso` is sorry-free |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 3 list.)

- **Polymorphic typeclass over multi-universe structures:** declare with
  explicit `class C.{u, v, w, x} ...`; `Type*` placeholders in class fields
  do not unify across uses.
- **`change` for `omega` across `abbrev` boundaries.**
- **Block-matrix pointwise lemmas:** `XCB_apply ... := rfl` fails on
  multi-`let` definitions; insert a `show` with the fully unfolded RHS first.
- **Dual transpose via `toPerfPair`.**
- **`Ring.inverse` for endomorphism orbits.**
- **`(2 : F)⁻¹ + (2 : F)⁻¹ = 1`:** use `rw [← two_mul, mul_inv_cancel₀ hChar]`.
- **`Submodule.prod p q ≃ₗ ↥p × ↥q`** (helper — not in Mathlib).
- **(NEW session 4) `Units.mkOfMulEqOne` for `IsUnit` from one-sided inverse:**
  `(Units.mkOfMulEqOne _ _ h).isUnit`. Replaces the deprecated chain;
  works because `Module.End F V` is `IsDedekindFiniteMonoid` for finite-dim V.
- **(NEW session 4) Helper-lemma decomposition** for "cannot fully close,
  but can articulate the obligation precisely": extract missing
  infrastructure as a focused helper with a targeted signature, sorry it,
  use it from the public theorem. Increases raw sorry count short-term but
  lets the next prover round attack a named lemma.
- **(NEW session 4) Avoid `obtain` from existentials when downstream needs
  `let`-bound contents.** `obtain` makes destructured fields opaque,
  breaking later `show` patterns that reference let-bound values. Package
  the equation directly in the helper's conclusion.

### Known blockers

#### Tier S — Plan-agent-only (statement corrections required)

- `Slice.lean :: uD_isParabolic` IsAdjointPair conjunct — change `(uD D, uD D)` to `(uD D, uD (-D))`.
- `Basic.lean :: UnipotentRadical` — tighten to enforce skew-adjointness w.r.t. `S.ambientForm`.
- `SliceSetup` (in `Slice.lean`) — add Lagrangian condition `L0_paired : IsPaired paired.pairing L0 L0'`.
- `NormalForm.lean :: kernelImage_ker` signature — re-type `Sₕ` from `LinearMap` to `LinearEquiv`.

#### Soft blockers (awaiting infrastructure additions, not statement fixes)

- All of `pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build`
  — need Levi-action machinery (`leviGL_E`, `leviGL_V0`, `levi_conj_XCB`)
  added to `Slice.lean`. Mechanical, ~60–100 lines.

### Inter-target dependency graph

```
[Tier S statement fixes]
    │
    ├──► uD_isParabolic ────┐
    ├──► UnipotentRadical ──┼──► parametrizeX0PlusU_existence
    │                       └──► (cleared) Tier-D inheritance in pNormalForm
    │
    ├──► SliceSetup Lagrangian ──┬──► kernelImage_ker
    │                            ├──► kernelImage_im
    │                            └──► residual_levi_build
    │
    └──► Sₕ as LinearEquiv  ─────► kernelImage_ker

[Levi-action machinery in Slice.lean (new code)]
    │
    ├──► pNormalForm_witnesses ──► pNormalForm
    │
    └──► residual_levi_extract ──┬
                                 ├──► pNormalForm_residual_orbit_iso ──► sIndependenceAndOrbitCriterion
        residual_levi_build ─────┘
```

## Notes

- Session 4 dispatched **6 parallel provers** despite PROGRESS.md only
  assigning 1 file. The harness's broader dispatch turned out net-positive:
  X0Geometry's Tier B target was unlocked early (via intra-file refactor
  the plan agent had not anticipated). NormalForm took two attempts to
  recover from a mid-round `show`-pattern build break introduced by
  parallel ordering.
- The two top-priority next-round actions are **plan-agent statement
  fixes** (Tier S) and **Levi-action machinery in `Slice.lean`**. After
  both land, six of the nine remaining sorries close mechanically.
- Build is green, but the `pNormalForm` body's `show` patterns are
  fragile under parallel-prover ordering. Future Levi-machinery additions
  to `Slice.lean` should be **strictly additive**.

## Last Updated

2026-04-27T15:10:00Z
