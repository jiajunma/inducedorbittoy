# Project Status

## Overall Progress

- **Stage:** prover (Round 5 complete; **4** declaration-use sorries remain).
- **Build state:** `lake build` succeeds (green, end of session 7 / Round 5).
- **Custom axiom declarations:** 0. All sorry-free public theorems depend
  only on `[propext, Classical.choice, Quot.sound]`. `sorryAx` appears
  only on declarations that still embed an explicit `sorry` (or
  transitively call one — currently `main` via `sIndependenceAndOrbitCriterion`).
- **Cumulative reduction:** 22 (start of session 3) → 8 (end of session 3) → 9 (end of session 4) → 7 (end of session 5) → 6 (end of session 6) → **4 (end of session 7)**.
  Net session 7: **−2** declaration sorries — Tier S #4 cascade closed
  `kernelImage_ker` (formerly 2 internal scoped sorries inside one
  declaration) and `kernelImage_im`.

## Solved this session (session 7 / Round 5)

- **`NormalForm.lean :: kernelImage_ker`** — Tier S #4 retyping landed.
  `Sₕ` switched from `S.L1' →ₗ[F] S.Vplus` to `S.L1' ≃ₗ[F] S.Vplus`.
  Underscore-prefixed `_hNondeg`/`_hT` replaced with `hNondeg`/`hT`
  (now used). Reverse-inclusion proof rewritten using three new private
  helpers (`Cdual_CST_mem_L1`, `kernelImage_DTD`, `lambda_isPerfPair_local`)
  + `sDual_restrict_ker_isIso` + `Submodule.IsCompl.projection_*` API.
- **`NormalForm.lean :: kernelImage_im`** — full proof body landed.
  Forward via `XST_apply` + `Cdual_CST_mem_L1` + `Submodule.mem_sup_*`.
  Reverse via constructive preimage: decompose `a` and `b` via
  `Submodule.mem_sup` and `IsCompl Vplus (range X0)`, set
  `l1' := Sₕ.symm ⟨b_V, hb_V⟩`, build `φ : ker X0 ≃ L1` via
  `sDual_restrict_ker_isIso`, take `w_a := φ.symm target`. Verify
  components via `XST_apply` + `map_add` + an explicit `abel` step.
- **`NormalForm.lean :: kernelImage_dim`** — call site updated to drop
  the explicit `LinearMap` coercion (line 783–784). Lean inserts the
  coercion automatically once `kernelImage_ker` takes a `LinearEquiv`.

## Solved earlier (sessions 1–6, carry-forward)

(See `proof-journal/sessions/session_6/summary.md` and earlier sessions
for full detail.)

- All of `LocalForms.lean` (3 theorems via `ClassifyBilinearForms` typeclass).
- All of `X0Geometry.lean` (closed in session 4).
- `NormalForm.lean :: kernelImage_dim`, `isUnit_uD`, `map_uD_eq_of_le`,
  `pNormalForm` (sessions 3–5).
- `Basic.lean :: SliceSetup`, `UnipotentRadical` (Tier S #2, #3 — session 6).
- `Slice.lean :: parametrizeX0PlusU_existence`, `parametrizeX0PlusU_mem`,
  `uD_isParabolic` (sessions 5–6).
- `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent`,
  `XST_sub_X0Lift_mem_unipotent`, `XST_mem_O0PlusU`, `inducedOrbits`,
  `main` (sessions 3 + 6).

## Remaining sorries (4 declaration warnings)

| File | Line | Theorem | Tier | Status |
|---|---|---|---|---|
| `NormalForm.lean` | 195 | `pNormalForm_witnesses` (private helper) | A | Tier S #4 dependency now satisfied; remaining blocker is **Levi machinery** (~60–100 additive lines in `Slice.lean`) — Round 6 |
| `NormalForm.lean` | 319 | `residual_levi_extract` (private helper) | A | needs Levi machinery + Levi-decomposition lemma `parabolic_decompose` — Round 6 |
| `NormalForm.lean` | 348 | `residual_levi_build` (private helper) | A | Tier S #3 + #4 dependencies satisfied; remaining blocker is Levi machinery — Round 6. Stale comments at lines 344, 357 reference removed `L0_isotropic` field; refresh as part of Round 6 edit. |
| `Orbits.lean` | 358 + 376 | `sIndependenceAndOrbitCriterion` (2 internal scoped sorries, 1 declaration) | A (deferred) | unblocks once `pNormalForm_residual_orbit_iso` is sorry-free; also needs added hypotheses (`Nondegenerate`, `(2 : F) ≠ 0`) and `Sₕ`-equality refactor — Round 7 |

## Knowledge Base

### Proof patterns (reusable across targets)

(Augments session 6 list.)

- **(NEW session 7) `linear_combination` is scalar-only over generic Modules.**
  It synthesises `CommSemiring`/`CommRing` on the target type. `S.E` is
  `AddCommGroup F + Module F` — not a `CommRing`. Vector identities over
  modules cannot be discharged with `linear_combination`; only **scalar**
  identities qualify. For module identities, drop to `rw` chains + `abel`.
  This is a refinement of session 6's "linear_combination over generic
  Field F" pattern — confirms the boundary.
- **(NEW session 7) `kerSDualEquiv` Subtype-wrapping anti-pattern.**
  Packaging "iso + property" as `{φ : … // ∀ w, …}` inside a `noncomputable
  def` fails when the proof needs `cases` on `IsCompl.codisjoint`
  (`Exists.casesOn` Prop-eliminator restriction: cannot eliminate a `Prop`
  into a `Type`). Solution: **inline the `obtain` inside each `Prop`-conclusion
  call site** rather than packaging as a `Subtype`.
- **(NEW session 7) `Submodule.IsCompl.projection_apply` + `projection_add_projection_eq_self`
  bridge.** Convert between the `IsCompl.projection`-as-`E`-valued form and
  the `linearProjOfIsCompl`-as-`L_i`-valued form via `projection_apply`.
  Pattern is reusable for any `IsCompl L1 L0` decomposition where we must
  combine the two API surfaces.
- **(NEW session 7) Drop explicit `LinearMap` coercions in `rw` arguments
  once a callee's signature switches from `LinearMap` to `LinearEquiv`** —
  Lean inserts the coercion automatically; explicit annotations cause an
  `Application type mismatch`.
- **(NEW session 7) `lean_leansearch` natural-language > `lean_loogle`
  patterns** for projection / `IsCompl.projection_*` API discovery.
  `lean_loogle` returned `No results found` for several legitimate queries
  this round (`Submodule.linearProjOfIsCompl_apply` and variants).
- **(NEW session 7) `let w := ⟨v, hv⟩` impedes `simpa` reduction.** Working
  with the inline anonymous-constructor term `⟨v, hv⟩` directly +
  `congrArg (fun w => (w : S.V0))` + `simpa` resolves it.
- **(NEW session 7) Drop redundant `rfl` after `rw` that already closes
  the goal** — leads to `No goals to be solved`. Symptom of `rw` doing
  more work than expected (e.g., when the rewrite makes LHS and RHS
  definitionally equal).
- **(NEW session 7) Two `Sₕ`-application forms in `LinearEquiv` proofs.**
  `Sₕ x` (CoeFun) and `(Sₕ : … →ₗ …) x` (LinearMap-coerced) elaborate
  differently. For `simp [LinearEquiv.apply_symm_apply]` to fire on
  `Sₕ (Sₕ.symm _) = _`, may need `show` to specify the LinearMap-coerced
  target form first.
- **(NEW session 7) `#print axioms` via `Bash` + `/tmp/check_axioms.lean`.**
  Pattern for closure-checking custom-axiom hygiene when `lean_verify` is
  not directly available: write a tiny one-off `.lean` file that imports
  the project module and `#print axioms` each newly closed theorem; run
  it via `lake env lean`.

(Earlier patterns from sessions 1–6 unchanged; see
`proof-journal/sessions/session_6/summary.md` for the complete list.)

### Known Blockers (do not retry)

- **Round 6 work** (Levi machinery, plus `pNormalForm_witnesses` /
  `residual_levi_extract` / `residual_levi_build`): blocked on
  Levi-action infrastructure (~60–100 lines additive in `Slice.lean`).
  Do not retry until Round 6 is dispatched.
- **Round 7 work** (`sIndependenceAndOrbitCriterion`): blocked on
  Round 6's `pNormalForm_residual_orbit_iso` plus added hypotheses
  (`Nondegenerate`, `(2 : F) ≠ 0`) and `Sₕ`-equality refactor.

### Stale comment hygiene

- `NormalForm.lean` lines 344, 357 still contain comment refs to the
  now-removed `L0_isotropic` field (replaced by Lagrangian quartet in
  session 6). They compile cleanly (inside docstrings/comments) but
  should be refreshed as part of the Round 6 `residual_levi_build` edit
  pass.

## Last Updated

2026-04-27T18:30:00Z (end of session 7 / Round 5)
