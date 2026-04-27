# Project Status

## Overall Progress

- **Stage:** prover (round 3 complete; **7** declaration-use sorries remain).
- **Build state:** `lake build` succeeds (green, end of session 5).
- **Custom axiom declarations:** 0. All public theorems depend only on
  `[propext, Classical.choice, Quot.sound]` (`sorryAx` appears only on
  declarations that still embed an explicit `sorry`). `lean_verify
  InducedOrbitToy.Slice.uD_isParabolic` re-confirmed this round.
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → **7 (end of session 5)**.
  Net session 5: **−2** declaration sorries via the Tier S #1 statement
  correction. Both `Slice.lean :: uD_isParabolic` and the
  Tier-D-inheritance scoped sorry inside `NormalForm.lean :: pNormalForm`
  closed in tandem (one statement edit per file plus the corresponding
  proof discharge).

## Solved this session (session 5)

- `Slice.lean :: uD_isParabolic` — statement corrected (4th conjunct
  `IsAdjointPair B B (uD D) (uD D)` → `IsAdjointPair B B (uD D) (uD (-D))`,
  i.e. self-adjoint → isometry); proof discharged via `Cdual_pairing_eq`
  + ε-symmetry (`epsSymm`, `epsValid`) + `linear_combination`. Two
  flag-preservation conjuncts unchanged.
- `NormalForm.lean :: IsParabolicElement` (definition) — 4th conjunct
  changed from `IsAdjointPair p p` (false self-adjoint) to
  `LinearMap.IsOrthogonal p` (true isometry, matching `IsometryEnd` in
  `Orbits.lean`). Docstring updated.
- `NormalForm.lean :: pNormalForm` — IsOrthogonal conjunct (formerly the
  Tier-D-inheritance scoped sorry at line 272) closed via 16-line calc
  chain: `(uD_isParabolic …).1` (now `IsAdjointPair (uD D) (uD (-D))`)
  chained with `uD_neg_inverse` (giving `uD (-D) ∘ uD D = id`) yields
  `B (uD D u) (uD D v) = B u (uD (-D) (uD D v)) = B u v`.
- `NormalForm.lean :: residual_levi_build` — comment-only edit removing
  the now-stale Tier-D inheritance reference. Body unchanged (still
  bare sorry, blocked on Tier S #3 + Levi machinery).

## Solved earlier (sessions 1–4, carry-forward)

(See `proof-journal/sessions/session_4/summary.md` and earlier sessions
for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4 by enriching
  `DualTransposeData` with `range_le_L1` and `finrank_L1_eq` fields).
- `NormalForm.lean :: kernelImage_dim` (rank-nullity, session 3).
- `NormalForm.lean :: isUnit_uD`, `map_uD_eq_of_le` helpers (session 4).
- `Orbits.lean :: inducedOrbits`, `main` (block-matrix point lemmas,
  session 3).
- 7 of 9 sorries in `Slice.lean` (`Cdual`, `Cdual_pairing_eq`,
  `parametrizeX0PlusU_mem`, `parametrizeX0PlusU_uniqueness`, `uD`,
  `uD_neg_inverse`, `uD_conj_XCB`, sessions 3 / 4).
- Two flag-preservation conjuncts of `Slice.lean :: uD_isParabolic`
  (session 4); IsAdjointPair conjunct closed this round.

## Remaining sorries (7 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `Slice.lean` | 232 | `parametrizeX0PlusU_existence` | D | **DO NOT RETRY** — needs `Basic.lean :: UnipotentRadical` tightened to enforce skew-adjointness (Tier S #2) |
| `NormalForm.lean` | 210 | `pNormalForm_witnesses` (private helper) | A | needs Levi-action machinery added to `Slice.lean` (additive, ≈60–100 lines) |
| `NormalForm.lean` | 330 | `residual_levi_extract` (private helper) | A | needs Levi-action machinery + Levi-decomposition lemma `parabolic_decompose` |
| `NormalForm.lean` | 363 | `residual_levi_build` (private helper) | A | needs Lagrangian condition `λ(L0, L0') = 0` added (Tier S #3) + Levi machinery |
| `NormalForm.lean` | 537+543 | `kernelImage_ker` (2 internal scoped sorries) | C | needs Lagrangian (Tier S #3) + `Sₕ` typed as `LinearEquiv` (Tier S #4) |
| `NormalForm.lean` | 595 | `kernelImage_im` | C | same Lagrangian blocker as `kernelImage_ker` |
| `Orbits.lean` | 242 | `sIndependenceAndOrbitCriterion` (2 internal scoped sorries) | A (deferred) | unblocked once `pNormalForm_residual_orbit_iso` is sorry-free; also needs added hypotheses (`Nondegenerate`, `(2 : F) ≠ 0`) and Sₕ-equality refactor |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 4 list.)

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
- **`Units.mkOfMulEqOne` for `IsUnit` from one-sided inverse:**
  `(Units.mkOfMulEqOne _ _ h).isUnit`. Replaces the deprecated
  `LinearMap.mul_eq_one_of_mul_eq_one`.
- **Helper-lemma decomposition** for "cannot fully close, but can
  articulate the obligation precisely": extract missing infrastructure
  as a focused helper with a targeted signature, sorry it, use it from
  the public theorem.
- **Avoid `obtain` from existentials when downstream needs `let`-bound
  contents.** Package the equation directly in the helper's conclusion.
- **(NEW session 5) Adjoint-pair → orthogonal via paired inverse:**
  given `IsAdjointPair B B f g` and `g ∘ f = id`,
  ```lean
  intro u v
  calc B (f u) (f v)
      = B u (g (f v)) := hAdj u (f v)
    _ = B u v := by rw [hinv_apply]
  ```
  where `hinv_apply : ∀ w, g (f w) = w` is reached via
  `congrArg (· w) hinv` + `simpa`.
- **(NEW session 5) Bilinear-form identities via block-decomposition +
  `linear_combination`:** destruct vectors as `(e, v, e')`, apply
  `*_apply` lemmas, use the standard `simp only` set
  (`SliceSetup.ambientForm`, `LinearMap.mk₂_apply`, distributivity /
  smul / neg lemmas), apply pairing-eq lemmas to all `λ(F ·, ·)` atoms,
  then close with `linear_combination` using ε-symmetry-derived
  hypotheses (`hε`, `hε2`, point-specific instantiations). Converges in
  ~5 `lean_multi_attempt` iterations on the right coefficient set.
- **(NEW session 5) Cross-file proof structure validation via
  `lean_run_code`:** when a proof depends on a sister-prover's signature
  change that hasn't landed yet, validate the local proof shape with
  hypothetical inputs of the correct shape via a standalone `example`.
  Eliminates uncertainty about whether the local proof is sound vs.
  waiting on the cross-file dependency.

### Known blockers

#### Tier S — Plan-agent-only (statement corrections required)

(Tier S #1 — `uD_isParabolic` IsAdjointPair conjunct + `IsParabolicElement`
4th conjunct — was **resolved this round**.)

- **Tier S #2:** `Basic.lean :: UnipotentRadical` — tighten to enforce
  skew-adjointness w.r.t. `S.ambientForm`. Unblocks
  `parametrizeX0PlusU_existence`.
- **Tier S #3:** `SliceSetup` (or a derived structure) — add Lagrangian
  condition `L0_paired : IsPaired paired.pairing L0 L0'`. Unblocks
  `kernelImage_ker`, `kernelImage_im`, `residual_levi_build`.
- **Tier S #4:** `NormalForm.lean :: kernelImage_ker` signature — re-type
  `Sₕ` from `LinearMap` to `LinearEquiv`.

#### Soft blockers (awaiting infrastructure additions, not statement fixes)

- All of `pNormalForm_witnesses`, `residual_levi_extract`,
  `residual_levi_build` — need Levi-action machinery (`leviGL_E`,
  `leviGL_V0`, `levi_conj_XCB`) added to `Slice.lean`. Strictly
  additive, ~60–100 lines. **Do not modify existing `_apply`
  signatures**: they are load-bearing for `pNormalForm`'s assembly.

### Inter-target dependency graph

```
[Tier S statement fixes still pending]
    │
    ├──► UnipotentRadical (S #2) ──► parametrizeX0PlusU_existence
    │
    ├──► SliceSetup Lagrangian (S #3) ──┬──► kernelImage_ker
    │                                   ├──► kernelImage_im
    │                                   └──► residual_levi_build
    │
    └──► Sₕ as LinearEquiv (S #4) ──────► kernelImage_ker

[Levi-action machinery in Slice.lean (additive)]
    │
    ├──► pNormalForm_witnesses ──► (already-closed pNormalForm body)
    │
    └──► residual_levi_extract ──┬
                                 ├──► pNormalForm_residual_orbit_iso ──► sIndependenceAndOrbitCriterion
        residual_levi_build ─────┘
```

(Tier S #1 paths — `uD_isParabolic`, `IsParabolicElement`, the
`pNormalForm` IsOrthogonal conjunct — are **all resolved this round**
and removed from the diagram.)

## Notes

- Session 5 dispatched **6 parallel provers** despite PROGRESS.md only
  assigning 2 files (Slice + NormalForm). The four non-objective provers
  (Basic, LocalForms, X0Geometry, Orbits) all correctly identified that
  no work was assigned and wrote brief "no work" reports per protocol.
  No incidental edits.
- Mid-round cross-file build break in `NormalForm.lean` (NormalForm
  using corrected `uD_isParabolic` shape before Slice landed) was
  expected per PROGRESS.md "Coordination notes for Round 3
  (parallel-safety)" and resolved automatically when the sister prover
  finished. End-of-round build is green.
- `lean_run_code` proved valuable for pre-validating cross-file proof
  structure. The NormalForm prover validated the calc-chain shape with
  hypothetical `IsAdjointPair` + inverse inputs *before* the Slice
  prover's statement change landed, eliminating uncertainty about
  whether the local proof was sound.
- The two top-priority next-round actions are **plan-agent statement
  fixes** (Tier S #2 + #3 + #4) and **Levi-action machinery in
  `Slice.lean`** (additive). After both land, 5 of the remaining 7
  sorries close mechanically; only `Orbits.lean ::
  sIndependenceAndOrbitCriterion` remains for Round 5.
- Build is green and `pNormalForm` is now sorry-free. The session-4 risk
  note about `pNormalForm`'s `show`-pattern fragility is still latent;
  reaffirm the additivity discipline for Round 4's Levi-machinery work.

## Last Updated

2026-04-28T00:50:00Z
