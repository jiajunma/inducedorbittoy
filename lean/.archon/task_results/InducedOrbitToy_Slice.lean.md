# InducedOrbitToy/Slice.lean

## Round 6 status: COMPLETE — no further work needed this round

The file already satisfies every Round 6 acceptance criterion (PROGRESS.md
lines 115–131, `informal/levi.md` § "Acceptance criteria for Round 6").
Verified at the start of this dispatch:

- `lake env lean InducedOrbitToy/Slice.lean` compiles. Only diagnostic:
  `Slice.lean:1078:8: warning: declaration uses 'sorry'` (the deferred
  `parabolic_decompose`, expected per plan).
- `lake build` is green. 5 declaration-use `sorry` warnings total —
  matches the expected end-of-Round-6 count: 1 in Slice (the additive
  `parabolic_decompose`) + 3 in NormalForm + 1 in Orbits.
- Helpers 1–7 of `informal/levi.md` § "Machinery to add" are all
  sorry-free, plus the bonus private helpers `lambdaDualE_symm_comp`,
  `lambdaDualE_comp_symm`, `lambdaDualE_Cdual` that the proofs needed.
- Helper 8 (`parabolic_decompose`) carries one bare `sorry` with a
  documented `Gap:` comment block immediately above (lines 1067–1077),
  exactly as the Round 6 plan permitted.
- All newly closed declarations show
  `[propext, Classical.choice, Quot.sound]` only — no custom axioms.
  Verified via `#print axioms` on `lambdaDualE_pairing_eq`,
  `lambdaDualE_id`, `lambdaDualE_comp`, `leviGL_E_apply`,
  `leviGL_V0_apply`, `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse`,
  `leviGL_E_isParabolic`, `leviGL_V0_isParabolic`,
  `leviGL_E_conj_XCB`, `leviGL_V0_conj_XCB`.
- All existing declarations through `uD_conj_XCB` (line 564) are
  byte-for-byte unchanged. Levi machinery is a pure additive append
  starting at line 679.

## What is in Slice.lean (Round 6 inventory, lines 679–1090)

### § 6.1 — Dual transpose on `E`

- `lambdaDualE` (def, line 695) — `(d : E' →ₗ E') ↦ (d^∨ : E →ₗ E)` via
  `S.lambda.toPerfPair.symm ∘ d.dualMap ∘ S.lambda`. **sorry-free.**
- `lambdaDualE_pairing_eq` (line 701) — defining identity
  `λ(g^∨ e, e') = λ(e, g e')`. Closed via
  `S.lambda.apply_symm_toPerfPair_self`. **sorry-free.**
- `lambdaDualE_id` (line 712) — `lambdaDualE id = id`. **sorry-free.**
- `lambdaDualE_comp` (line 723) — contravariant in composition.
  **sorry-free.**
- `lambdaDualE_symm_comp` (line 739, private) — `d.symm^∨ ∘ d^∨ = id`.
  **sorry-free.**
- `lambdaDualE_comp_symm` (line 751, private) — `d^∨ ∘ d.symm^∨ = id`.
  **sorry-free.**

### § 6.2 — Levi block embeddings

- `leviGL_E` (def, line 766) — block-diagonal action
  `((d⁻¹)^∨, id_{V0}, d)`. **sorry-free.**
- `leviGL_V0` (def, line 784) — block-diagonal action
  `(id_E, g, id_{E'})`. **sorry-free.**
- `leviGL_E_apply` (line 798), `leviGL_V0_apply` (line 806) —
  pointwise formulas; closed by `unfold; simp`. **sorry-free.**

### § 6.3 — Inverses

- `leviGL_E_symm_inverse` (line 815), `leviGL_V0_symm_inverse`
  (line 835) — both **sorry-free.**

### § 6.4 — Parabolicity

- `leviGL_E_isParabolic` (line 849) — proves the unbundled
  4-conjunct `IsParabolicElement` (`IsUnit ∧ flagE ∧ flagEV0 ∧
  IsOrthogonal`). The proof opens the conjunction with
  `refine ⟨?_, ?_, ?_, ?_⟩` and discharges each with
  `Units.mkOfMulEqOne` (unit), `le_antisymm` + `lambdaDualE_symm_comp`
  / `lambdaDualE_comp_symm` (flag preservation), and a single
  `simp; rw [lambdaDualE_pairing_eq]; simp` (orthogonality).
  **sorry-free.**
- `leviGL_V0_isParabolic` (line 911) — analogous, using the
  isometry hypothesis `hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v`
  on the V0 block. **sorry-free.**

### § 6.5 — Conjugation transformation of `XCB`

- `lambdaDualE_Cdual` (line 967, private) — compatibility:
  `lambdaDualE g (Cdual C v) = Cdual (C ∘ g) v`. Proved via
  `Cdual_pairing_eq + lambdaDualE_pairing_eq + perfect-pairing
  injectivity`. **sorry-free.**
- `leviGL_E_conj_XCB` (line 978) — block formula
  `leviGL_E d ∘ XCB(C, B) = XCB(C ∘ d⁻¹, (d⁻¹)^∨ ∘ B ∘ d⁻¹) ∘ leviGL_E d`.
  Proved by component-wise calculation on `(e, v, e')` using
  `XCB_apply`, `leviGL_E_apply`, `lambdaDualE_Cdual`. **sorry-free.**
- `leviGL_V0_conj_XCB` (line 1012) — block formula on V0 with
  hypotheses `hgX` (g commutes with X0) and `hgC` (g preserves
  pairwise V0-form on C-image). **sorry-free.** This is a slight
  generalisation of the spec in `informal/levi.md` § 6.5, which
  acknowledged the `g`-isometry-only version may need conditional
  hypotheses; the implementation makes both `hgX` and `hgC` explicit.

### § 6.6 — Levi/unipotent decomposition (deferred to Round 8)

- `parabolic_decompose` (line 1078) — **carries the single Round 6
  additive `sorry`.** Documented `Gap:` block at lines 1067–1077
  outlines the 3-step proof:
  1. **Step A** (g₀ extraction): action of `p` on `flagEV0/flagE ≃ V0`.
  2. **Step B** (`(d⁻¹)^∨` extraction): action of `p` on `flagE = E`.
  3. **Step C** (residual `D`): apply `parametrizeX0PlusU_uniqueness`
     to `p ∘ leviGL_E d.symm ∘ leviGL_V0 g₀.symm`.
  The plan in PROGRESS.md (Round Plan table, line 56) and
  `task_pending.md` lines 101–113 schedule this for Round 8.

## Why no further partial proof attempt for `parabolic_decompose` this round

I evaluated whether to add structural sub-`sorry`s inside
`parabolic_decompose`'s body (e.g. via `refine ⟨?D, ?d, ?g, ?hg, ?_⟩`
with separate `case D` ... blocks) to expose the substeps in the proof
script. Reasons against:

1. The Round 6 acceptance criterion forbids changing the `sorry` count
   beyond the one additive warning for `parabolic_decompose` itself
   (PROGRESS.md line 124). Internal `sorry`s coalesce into one
   declaration-use warning, but adding helper *declarations* with their
   own sorries (the natural way to expose substeps for the next prover)
   would violate this. The current state is the strictly cleanest
   form: one `theorem`, one `sorry`, gap fully documented.
2. The existing `Gap:` comment block (lines 1067–1077) already
   describes the 3-step proof at the same granularity that an internal
   `refine` skeleton would expose, without adding any code that the
   Round 8 prover would need to delete or restructure.
3. Round 8's prover will most likely refactor the body to its own
   layout — writing speculative skeleton code now risks creating
   churn at no benefit.

## Mathlib / project lemmas used (Round 6 reference list, for
audit/handoff)

- **From X0Geometry.lean / earlier in Slice.lean:**
  `S.paired.isPerfect.1` (left-injectivity of perfect pairing — used
  to reduce E-side equalities to functional equalities),
  `lambda_isPerfPair` (private, line 46),
  `S.lambda.toPerfPair`, `.toPerfPair.symm`,
  `S.lambda.apply_symm_toPerfPair_self`,
  `S.lambda.toPerfPair_apply`,
  `Cdual_pairing` / `Cdual_pairing_eq` (line 78),
  `Cdual_neg`, `Cdual_X0_apply`,
  `XCB_apply` (line 168), `X0Lift_apply` (line 177),
  `uD_apply` (line 405).
- **From Mathlib (LinearMap / Submodule):**
  `LinearMap.dualMap_apply`,
  `LinearMap.IsPerfPair`, `LinearMap.toPerfPair`,
  `LinearMap.IsOrthogonal` unfolds to
  `∀ x y, B (g x) (g y) = B x y`,
  `LinearMap.inl`, `LinearMap.inr`, `LinearMap.fst`,
  `LinearMap.snd` (block matrix idiom on `S.E × S.V0 × S.E'`),
  `LinearMap.ext`, `LinearMap.comp_apply`, `LinearMap.add_apply`,
  `LinearMap.sub_apply`, `LinearMap.map_add`,
  `Submodule.map`, `Submodule.subtype`, `Submodule.mem_bot`,
  `Submodule.mem_top`,
  `Units.mkOfMulEqOne` (used to build `IsUnit` from a one-sided
  inverse on `Module.End F V`).
- **Tactics:** `simp` (after `unfold`), `simpa`, `apply LinearMap.ext`,
  `refine Prod.mk.injEq .. |>.mpr ⟨?_, ...⟩` (component-wise on the
  `E × V0 × E'` triple), `rfl` for definitional equalities,
  `congrArg (fun f => f x)` to evaluate `LinearMap` equalities at a
  point. **No** use of `linear_combination` in Levi machinery (the
  perfect-pairing identity rewrites are clean enough that
  `simp + rw` closes everything).

## Compilation evidence (this dispatch)

```
$ lake env lean InducedOrbitToy/Slice.lean
InducedOrbitToy/Slice.lean:1078:8: warning: declaration uses `sorry`

$ lake build  (full project)
warning: InducedOrbitToy/X0Geometry.lean:221:35: unused variable `hlambda`
warning: InducedOrbitToy/Slice.lean:1078:8: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:195:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:319:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:348:16: declaration uses `sorry`
warning: InducedOrbitToy/Orbits.lean:324:8: declaration uses `sorry`
Build completed successfully (8033 jobs).
```

5 declaration-use warnings, exactly matching the end-of-Round-6
expectation in `task_pending.md` lines 4–16.

## Next steps (handoff to plan agent / Round 7 dispatch)

- **Round 7** consumers in `NormalForm.lean` will reference
  `lambdaDualE`, `lambdaDualE_pairing_eq`, `leviGL_E`, `leviGL_E_apply`,
  `leviGL_E_isParabolic`, `leviGL_E_conj_XCB`, and
  `leviGL_E_symm_inverse` to close `pNormalForm_witnesses`,
  `residual_levi_extract`, `residual_levi_build`. All these signatures
  are now finalised and stable.
- **Round 8** will close `parabolic_decompose` (line 1078) and
  `sIndependenceAndOrbitCriterion`. The `Gap:` comment in Slice.lean
  is the entry point for the former.
- The bonus private helpers `lambdaDualE_symm_comp`,
  `lambdaDualE_comp_symm`, `lambdaDualE_Cdual` may be useful in Round 7
  / Round 8 — they are exported within the namespace.

## Dead-end warnings

- **Do not** try to subtype-wrap the `(g, hg)` pair in a single
  `Subtype` for `leviGL_V0_isParabolic`. Per the Round-5 review note in
  PROGRESS.md ("Subtype-wrapping anti-pattern for `Iso + Property`"),
  the `Prop`-eliminator restriction on `IsCompl.codisjoint`-style
  cases makes this fail. The current implementation keeps `g` and
  `hg` separate function arguments, matching the
  `informal/levi.md` § "Side notes" recommendation.
- **Do not** try to discharge `lambdaDualE_pairing_eq` by `unfold` +
  `simp` alone. The construction goes through
  `S.lambda.toPerfPair.symm`, and the cancellation requires the
  explicit lemma `S.lambda.apply_symm_toPerfPair_self`.
- **Do not** try `linear_combination` inside `parabolic_decompose`
  or the `leviGL_*_conj_XCB` proofs. The identities are clean enough
  to close by direct rewrite + `simp`; `linear_combination` would
  attempt to synthesise `CommRing` on the wrong type (per the Round 5
  note in PROGRESS.md "Reusable Gotchas").
