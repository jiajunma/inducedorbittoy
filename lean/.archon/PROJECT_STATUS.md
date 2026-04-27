# Project Status

## Overall Progress

- **Stage:** prover (round 1 complete).
- **Build state:** `lake build` succeeds.
- **Custom axiom declarations:** 0. All public theorems depend only on
  `[propext, Classical.choice, Quot.sound]` (`sorryAx` appears only on
  declarations that still embed an explicit `sorry`).
- **Remaining declaration-use `sorry` warnings:** 8 (down from 22 at session
  start; ≈63% reduction this session).

## Solved this session (session 3)

- `LocalForms.lean :: localFormClasses_finite` (typeclass projection)
- `LocalForms.lean :: localFormClasses_open` (typeclass projection)
- `LocalForms.lean :: localFormClasses` (composition)
- `NormalForm.lean :: kernelImage_dim` (rank-nullity + `submoduleProdEquiv` helper)
- `Orbits.lean :: inducedOrbits` (block-matrix point lemmas + `Ring.inverse`)
- `Orbits.lean :: main` (composition of the four sub-claims)
- `Slice.lean :: Cdual` (term-mode, via `lambda.toPerfPair.symm`)
- `Slice.lean :: Cdual_pairing_eq` (via `apply_symm_toPerfPair_self`)
- `Slice.lean :: parametrizeX0PlusU_mem` (block-matrix lift)
- `Slice.lean :: parametrizeX0PlusU_uniqueness` (probe at `(0, 0, e')`)
- `Slice.lean :: uD` (term-mode, explicit block-matrix with `½ • Cdual D (D e')`)
- `Slice.lean :: uD_neg_inverse` (`½ + ½ = 1` + `linear_combination`)
- `Slice.lean :: uD_conj_XCB` (block-matrix expansion + 4 helper lemmas)
- `X0Geometry.lean :: vplusKerPairing_isPerfPair` (`IsRefl` + orthogonal eq)

## Remaining sorries (8 declaration warnings)

| File | Line | Theorem | Status |
|---|---|---|---|
| `X0Geometry.lean` | 206 | `sDual_restrict_ker_isIso` | partial — 2 scoped sorries; needs `Basic.lean :: DualTransposeData` refactor |
| `Slice.lean` | 232 | `parametrizeX0PlusU_existence` | **DO NOT RETRY** — statement is mathematically false in current generality |
| `Slice.lean` | 391 | `uD_isParabolic` | **DO NOT RETRY** — autoformalization statement bug |
| `NormalForm.lean` | 167 | `pNormalForm` | provable now; deferred |
| `NormalForm.lean` | 199 | `pNormalForm_residual_orbit_iso` | provable now; deferred |
| `NormalForm.lean` | 302 | `kernelImage_ker` | needs SliceSetup Lagrangian refactor |
| `NormalForm.lean` | 397 | `kernelImage_im` | needs SliceSetup Lagrangian refactor |
| `Orbits.lean` | 242 | `sIndependenceAndOrbitCriterion` | partial — unblocked by `pNormalForm_residual_orbit_iso` |

## Knowledge Base

### Proof patterns (reusable across targets)

- **Polymorphic typeclass over multi-universe structures:** declare with
  explicit `class C.{u, v, w, x} ...`; `Type*` placeholders in class fields
  do not unify across uses.
- **`change` for `omega` across `abbrev` boundaries:** insert
  `change Module.finrank F S.paired.E + _ = Module.finrank F S.paired.E + _`
  before `omega` when `S.E := S.paired.E` is an `abbrev`.
- **Block-matrix pointwise lemmas:** `XCB_apply ... := rfl` fails on
  multi-`let` definitions; insert a `show` with the fully unfolded RHS first.
- **Dual transpose via `toPerfPair`:** the canonical "transpose along a
  perfect pairing" pattern uses `lambda.toPerfPair.symm.toLinearMap.comp` plus
  `(-C.dualMap.comp formV0)`. Pairing equation follows from
  `LinearMap.apply_symm_toPerfPair_self`.
- **`Ring.inverse` for endomorphism orbits:** dodges the need for a
  division-ring structure on `Module.End`.
- **`(2 : F)⁻¹ + (2 : F)⁻¹ = 1`:** use `rw [← two_mul, mul_inv_cancel₀ hChar]`
  (do *not* use `field_simp` — leaves residual `1 + 1 = 2`).
- **`Submodule.prod p q ≃ₗ ↥p × ↥q`:** not in Mathlib; helper written this
  session (`NormalForm.lean :: submoduleProdEquiv`); worth upstreaming.

### Known blockers (do not retry — statement-level bugs)

- `Slice.lean :: parametrizeX0PlusU_existence` — needs `Basic.lean :: UnipotentRadical` tightened to the Lie subalgebra that preserves `ambientForm`.
- `Slice.lean :: uD_isParabolic` — needs the `IsAdjointPair` conjunct changed from `(uD D, uD D)` to `(uD D, uD (-D))`.

### Soft blockers (need upstream data refactor before reassignment)

- `NormalForm.lean :: kernelImage_ker` and `kernelImage_im` — need `SliceSetup` to expose a Lagrangian condition `λ(L1, L0') = 0` plus `Sₕ` typed as `LinearEquiv` not `LinearMap`.
- `X0Geometry.lean :: sDual_restrict_ker_isIso` — need `DualTransposeData` to expose `range(Tdual) ⊆ L1` and `finrank L1 = finrank ker S.X0`.

## Notes

- The two top-priority next-round targets are `pNormalForm` and
  `pNormalForm_residual_orbit_iso` — both provable now without upstream
  changes; both unblock additional sorries (`sIndependenceAndOrbitCriterion`).
- All session 3 work landed without breaking the build. `Slice.lean` ended
  the session with one transient build break (mid-round), self-corrected
  before round end.
- Session 2 produced no `sorryAx`-free theorems; session 3 produced 14.

## Last Updated

2026-04-27T09:30:00Z
