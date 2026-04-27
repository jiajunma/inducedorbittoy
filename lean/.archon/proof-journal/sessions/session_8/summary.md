# Session 8 — Prover Round 6 (Levi-action machinery in Slice.lean)

## Metadata

- **Session:** 8 (stage `prover`, Round 6 — single-file additive dispatch on `Slice.lean`).
- **Sorry count (declaration-use warnings) before round:** 4
  - `NormalForm.lean`: 3 (`pNormalForm_witnesses` 195, `residual_levi_extract` 319, `residual_levi_build` 348).
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` lines 358 + 376).
  - `Slice.lean`: 0.
- **Sorry count (declaration-use warnings) after round:** **5** (additive +1 — the deferred `parabolic_decompose`).
  - `NormalForm.lean`: 3 (unchanged — Round 6 acceptance criterion).
  - `Orbits.lean`: 1 (unchanged).
  - `Slice.lean`: 1 (new `parabolic_decompose` at line 1078, deferred per stop condition).
- **Net change:** +1 declaration warning (deliberate — Round 6 is purely additive infrastructure; per `PROGRESS.md` lines 122–126, up to one extra `sorry` for `parabolic_decompose` is acceptable).
- **Custom axioms introduced:** 0. `#print axioms` (via `/tmp/check_axioms_slice.lean` + `lake env lean`) for all 14 newly-added Levi declarations reports `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no custom axioms (the deferred `parabolic_decompose` is excluded from the audit since it carries an explicit `sorry`).
- **Build status:** `lake build` green at end of round (8033 jobs, only pre-existing warnings: 4 sorry declarations + 5th new sorry + the pre-existing `X0Geometry.lean:221` unused-variable lint).
- **Pre-processed log:** 60 events total (1 summary line + 59 events), 5 edits to a single file (`Slice.lean`), 0 explicit `lean_goal` checks (prover relied on `lean_diagnostic_messages`), 5 diagnostic checks, 0 `lean_build` MCP calls (lake invoked via `Bash`), 0 lemma searches recorded as `lean_local_search`/`lean_loogle`/`lean_leansearch` events (the prover used a `lean_run_code` `#check` pattern for API discovery instead — 3 invocations).

## Process observation

The plan agent assigned **one** file this round (`Slice.lean`, additive Levi machinery only). The harness still dispatched provers to `Basic.lean`, `LocalForms.lean`, `NormalForm.lean`, `Orbits.lean`, `X0Geometry.lean`; per protocol they verified isolation, wrote brief "no work" reports, and made no edits.

The single objective prover landed helpers 1–7 sorry-free (`lambdaDualE`, `lambdaDualE_pairing_eq`, `lambdaDualE_id`, `lambdaDualE_comp`, `leviGL_E`, `leviGL_V0`, `leviGL_E_apply`, `leviGL_V0_apply`, `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse`, `leviGL_E_isParabolic`, `leviGL_V0_isParabolic`, `leviGL_E_conj_XCB`, `leviGL_V0_conj_XCB`) plus two private bridge helpers (`lambdaDualE_symm_comp`, `lambdaDualE_comp_symm`, `lambdaDualE_Cdual`). Helper 8 (`parabolic_decompose`) was deferred to Round 7 with an explicit `sorry` and a 24-line documented gap explanation, in compliance with the PROGRESS.md stop condition limiting time spent on the hardest piece.

No mid-round build break (only one file edited additively after `uD_conj_XCB`).

## Target — `InducedOrbitToy/Slice.lean :: Levi-action machinery (additive)` ✅ MOSTLY RESOLVED

### Helpers 1–7 (RESOLVED)

#### `lambdaDualE` (Section 6.1, around line 696)

- **Approach:** Mirror the existing `Cdual` construction (Slice.lean line 71).
  Define `lambdaDualE S g e := S.lambda.toPerfPair.symm (g.dualMap (S.lambda e))`.
  The inner `g.dualMap (S.lambda e) : Module.Dual F S.E'` is a linear functional
  on `S.E'`; the outer perfect-pairing inverse lifts it to `S.E`.
- **Key Mathlib lemmas:** `LinearMap.dualMap`, `LinearMap.dualMap_apply`,
  `LinearMap.IsPerfPair.toPerfPair`, `LinearMap.apply_symm_toPerfPair_self`.

#### `lambdaDualE_pairing_eq` (defining identity)

- **Approach:** Same `show` + `rw [apply_symm_toPerfPair_self]` + `simp [dualMap_apply]`
  pattern as `Cdual_pairing_eq` (Slice.lean line 78).

#### `lambdaDualE_id`

- **Approach:** Pair both sides with arbitrary `e'` via `S.paired.isPerfect.1`
  (left-injectivity of perfect pairing); `lambdaDualE_pairing_eq` reduces both
  sides to `S.lambda e e'`.

#### `lambdaDualE_comp`

- **First attempt** — apply `S.paired.isPerfect.1` then `rw
  [lambdaDualE_pairing_eq]` directly. **Failed.**
  - Lean error: `Tactic rewrite failed: Did not find an occurrence of the
    pattern (S.lambda) ((lambdaDualE ?S ?g) ?e) ?e' in the target expression
    (S.lambda e) (g₁ (g₂ e')) = (S.paired.pairing ((lambdaDualE S ...))) ...`.
  - Insight: the goal's RHS had `(g₁ ∘ₗ g₂) e` in opaque composition form,
    so `rw` couldn't pattern-match `lambdaDualE_pairing_eq` until the
    composition was unfolded to `g₁ (g₂ e)` form.
- **Second attempt** — prepend `show S.lambda (lambdaDualE S (g₁ ∘ₗ g₂) e) e'
  = S.lambda ((lambdaDualE S g₂ ∘ₗ lambdaDualE S g₁) e) e'` to convert the
  composed-form goal into nested-application form, then three
  `lambdaDualE_pairing_eq` rewrites + `rfl`. **Success.**

#### `leviGL_E` and `leviGL_V0` (Section 6.2)

- **Approach:** Direct block-matrix definitions via `LinearMap.inl`,
  `LinearMap.inr`, `LinearMap.fst`, `LinearMap.snd` projections/embeddings.
  `leviGL_E d` acts as `((d⁻¹)^∨, id, d)` on `E × V0 × E'`;
  `leviGL_V0 g` as `(id, g, id)`. Definitions follow `informal/levi.md §6.2`.
- **Note:** `leviGL_V0` does NOT depend on the isometry hypothesis on `g`.
  Per `levi.md` side note, only the parabolicity proof needs it. Sidesteps
  the Round-5 subtype-wrapping anti-pattern.
- `leviGL_E_apply` / `leviGL_V0_apply`: closed via `unfold` + `simp`.

#### `leviGL_E_symm_inverse` / `leviGL_V0_symm_inverse`

- **Approach:** `LinearMap.ext` + `Prod.mk.injEq` to component-split, then
  `congrArg` on `lambdaDualE_comp_symm` for the E-block, `simp` for the rest.
- **Key insight:** `d.symm.symm = d` is `rfl` for `LinearEquiv` (via Mathlib's
  `LinearEquiv.symm_symm`), so applying `leviGL_E_symm_inverse S d.symm` gives
  the other-direction inverse for free. Used in `leviGL_E_isParabolic`'s
  `IsUnit` conjunct.

#### `leviGL_E_isParabolic`

- **Approach:** Statement unfolds `IsParabolicElement S` (defined downstream
  in NormalForm.lean — so unfolded as 4-conjunct `IsUnit ∧ Submodule.map = ∧
  Submodule.map = ∧ IsOrthogonal`).
  - **IsUnit:** `Units.mkOfMulEqOne` on the symm inverse (with `d.symm`
    twice for the other-direction inverse via `d.symm.symm = d` rfl).
  - **flagE preservation:** `le_antisymm` + `rintro` patterns; forward via
    `leviGL_E_apply` + `simp`; backward via `lambdaDualE_symm_comp`.
  - **flagEV0 preservation:** Same template.
  - **IsOrthogonal:** `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply]`
    expands the bilinear form; `lambdaDualE_pairing_eq` rewrites both `λ`
    atoms; `simp` closes via `d.symm (d _) = _`.

#### `leviGL_V0_isParabolic`

- Same template as `leviGL_E_isParabolic`. The `IsOrthogonal` conjunct uses
  the isometry hypothesis `hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v`
  via `rw [hg]`.

#### `lambdaDualE_Cdual` (private helper for §6.5)

- **Statement:** `lambdaDualE S g (Cdual S C v) = Cdual S (C ∘ₗ g) v`.
- **Approach:** Pair both sides with `e''` via `S.paired.isPerfect.1`, reduce
  LHS via `lambdaDualE_pairing_eq` then `Cdual_pairing` (no-Nondeg variant),
  reduce RHS via `Cdual_pairing` + `LinearMap.comp_apply`.

#### `leviGL_E_conj_XCB`

- **Approach:** Component-split via `Prod.mk.injEq`. E-component uses
  `lambdaDualE_Cdual` and `LinearMap.map_add`; V0-component is a direct
  `simp [comp_apply]`; E'-component is trivially `0 = 0`.

#### `leviGL_V0_conj_XCB`

- **First attempt** (around 19:01:12) — stated `hgC` symmetrically with
  `(g : S.V0 →ₗ[F] S.V0)`-FunLike on both sides:
  ```lean
  (hgC : ∀ v e'',
      S.formV0 ((g : S.V0 →ₗ[F] S.V0) v)
          ((g : S.V0 →ₗ[F] S.V0) (C e''))
        = S.formV0 v (C e''))
  ```
  **Failed.**
  - Lean error: `Tactic rewrite failed: Did not find an occurrence of the
    pattern (S.formV0 (↑g ?v)) (↑g (C ?e'')) in the target expression
    -(S.formV0 v) (C e'') = -(S.formV0 (g v)) (↑g (C e''))`.
  - Insight: `Cdual_pairing` rewrite produces `(g : V0 →ₗ V0) (C e'')`
    (LinearMap-coerced) on the *second* arg, but the *first* arg comes
    through as `g v` in the LinearEquiv's `FunLike` form. The asymmetry
    of how the two args appear after `comp_apply` rewrites cannot be
    matched by a symmetric `hgC`.
- **Second attempt** — restate `hgC` asymmetrically:
  ```lean
  (hgC : ∀ v e'',
      S.formV0 (g v)
          ((g : S.V0 →ₗ[F] S.V0) (C e''))
        = S.formV0 v (C e''))
  ```
  **Success.** Diagnostics clean.

### Helper 8 — `parabolic_decompose` (DEFERRED at line 1078)

- **Statement:** Adapted to take 4 unfolded conjuncts of `IsParabolicElement`
  (since `IsParabolicElement` lives in NormalForm.lean, downstream).
  Round 7's NormalForm consumer destructs `IsParabolicElement` and passes
  the 4 components.
- **Outline left in file (24-line `/-** Gap: ... -/` comment block above the
  theorem):** the proof requires three substantive sub-constructions per
  `levi.md §6.6`:
  - **(a) `g₀` extraction** via descent of `p` to the quotient
    `flagEV0 / flagE ≃ V0` (~30 lines: define quotient module action, show
    bijectivity, bridge through `Submodule.quotientEquivOfIsCompl`).
  - **(b) `(d⁻¹)^∨` extraction** from `Submodule.map p S.flagE = S.flagE`
    (~25 lines: restrict `p` to `flagE`, transfer through `flagE ≃ E`,
    invert `lambdaDualE` via `lambdaDualE_pairing_eq` + perfect pairing).
  - **(c) Residual `D`** via `parametrizeX0PlusU_existence` /
    `parametrizeX0PlusU_uniqueness` applied to
    `p ∘ₗ (leviGL_E d ∘ₗ leviGL_V0 g)⁻¹` (~30 lines: prove this composition
    is in `UnipotentRadical S`, apply `existence` to extract `(C, B)`,
    identify `C = D` and `B = 0` via the third (skewness) conjunct).
- **Why deferred:** Per PROGRESS.md stop condition: "If `parabolic_decompose`
  proves intractable: stop and report. Do NOT spend more than ~30% of the
  round budget on it; helpers 1–7 are the priority." The 5 successful
  helper edits + 14-declaration axiom audit consumed the bulk of the round
  budget.

### Attempt log (Slice.lean — 5 edits)

The 5 edits in `attempts_raw.jsonl` decompose as follows.

| # | Strategy | Outcome |
|---|---|---|
| 1 | First batch append (~14kb): `lambdaDualE` + `lambdaDualE_pairing_eq` + `lambdaDualE_id` + `lambdaDualE_comp` (initial form, no `show` step). | **Success at the file level** but the `lambdaDualE_comp` proof had an unfound-pattern issue that the prover caught and fixed in edit #2. |
| 2 | Second batch append (~16kb): adds `lambdaDualE_symm_comp`, `lambdaDualE_comp_symm`, `leviGL_E`, `leviGL_V0`, `_apply` lemmas, `_symm_inverse` lemmas, `_isParabolic` lemmas, `_conj_XCB` lemmas, `lambdaDualE_Cdual`, and `parabolic_decompose` skeleton with `sorry`. The first diagnostic check after this batch found the `lambdaDualE_comp` unfound-pattern error. | **Failed** with `Tactic rewrite failed: Did not find an occurrence of the pattern (S.lambda) ((lambdaDualE ?S ?g) ?e) ?e' in the target expression`. |
| 3 | Repair `lambdaDualE_comp`: prepend `show S.lambda (lambdaDualE S (g₁ ∘ₗ g₂) e) e' = S.lambda ((lambdaDualE S g₂ ∘ₗ lambdaDualE S g₁) e) e'` to convert composed-form goal into nested-application form, then `rw [lambdaDualE_pairing_eq, LinearMap.comp_apply, lambdaDualE_pairing_eq, lambdaDualE_pairing_eq]; rfl`. | **Failed** at `leviGL_V0_conj_XCB` with the symmetric `hgC` form — `Tactic rewrite failed: Did not find an occurrence of the pattern (S.formV0 (↑g ?v)) (↑g (C ?e''))`. |
| 4 | Repair `leviGL_V0_conj_XCB`: restate `hgC` asymmetrically — `S.formV0 (g v) ((g : S.V0 →ₗ[F] S.V0) (C e''))` — to match the asymmetric form produced by `Cdual_pairing` after `comp_apply` rewrites. | **Success** — all errors gone. |
| 5 | Tighten the `leviGL_V0_conj_XCB` doc-comment to mention the explicit `LinearMap`-coerced form for the second `formV0` argument. | **Success** — diagnostic confirms only 1 sorry warning remains (the deferred `parabolic_decompose` at line 1078). |

### Lemma searches (0 traditional MCP search invocations; 3 `lean_run_code` `#check`s)

The prover used `lean_run_code` with standalone `#check` snippets to verify
Mathlib API names before relying on them. Specifically:
- `#check @LinearMap.dualMap` — verified the signature for `lambdaDualE`.
- A second `lean_run_code` (no diagnostics returned, success) likely tested
  the composition pattern.
- A third `lean_run_code` similarly clean.

This pattern (`lean_run_code` `#check` over `lean_loogle`/`leansearch`) is
faster for confirming a known-name signature than a search; the prover
already knew the names from `informal/levi.md`'s `-- Hint:` comments.

## Key findings / patterns discovered

### `show` to convert composed-form goals to nested-application form before `rw`

The `lambdaDualE_comp` proof needed a `show` step to expose `g₁ (g₂ e)`
explicitly (vs. the composed `(g₁ ∘ₗ g₂) e`) before `rw [lambdaDualE_pairing_eq]`
could pattern-match. **Reusable pattern:** when `rw`-ing perfect-pairing
identities through a `comp` argument, `show ... f (g e)` first.

### LinearEquiv FunLike vs LinearMap FunLike coercion mismatch in `rw` patterns

Even though `g v = (g : V →ₗ V) v` is `rfl`, `rw` pattern-matching is
syntactic. When stating an isometry-style hypothesis used via `rw`, match
the LinearMap-coerced form that appears in the goal **after**
`LinearMap.comp_apply` rewrites. Specifically, in `leviGL_V0_conj_XCB`'s
`hgC`, the second arg comes from `(g : V →ₗ V) ∘ₗ C` after `comp_apply`,
so state the hypothesis with `(g : V →ₗ V) (C e'')` rather than `g (C e'')`.

The two FunLike instances coexist; their reflexive equality doesn't
help syntactic pattern-matching.

### Block-matrix inverse via componentwise identity proofs

The Levi proofs all use `Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr
⟨?_, ?_⟩⟩` to split into E/V0/E' components, then close each individually.
Reusable for any `Module.End F (E × V0 × E')` proofs.

### `d.symm.symm = d` for `LinearEquiv` is `rfl`

This makes `leviGL_E_symm_inverse S d.symm` directly usable as the
other-direction inverse, halving the inverse-proof work. Important for
the `IsUnit` conjunct of `_isParabolic`.

### `leviGL_V0` definition takes only `g : V0 ≃ₗ V0`, no isometry bundled

Avoids the Round-5 subtype anti-pattern (session 7's `kerSDualEquiv`).
Isometry hypothesis is passed separately at consumer sites
(`leviGL_V0_isParabolic`, `leviGL_V0_conj_XCB`).

### `lean_run_code` `#check` over `lean_loogle`/`leansearch` for known-name verification

When the informal sketch (`levi.md`) names the target Mathlib lemma in a
`-- Hint:` comment, jumping straight to `lean_run_code "import ...; #check
@LinearMap.dualMap"` is faster than running a fuzzy search. The Round 6
prover never invoked `lean_loogle` or `lean_leansearch` and still landed
14 declarations; the workflow shift was: read informal doc → `lean_run_code`
verify name → write proof.

### `#print axioms` via `Bash` + `/tmp/check_axioms_slice.lean` (continued)

Confirms the session-7 pattern as a standard prover closure-check pattern
when `lean_verify` is unavailable. Build a one-off `.lean` file that
imports the project module and `#print axioms` each newly closed theorem.
First-attempt typo: used `#print axioms @lambdaDualE` (with `@`) — fails
since `#print axioms` doesn't accept the `@` prefix. Drop `@`: `#print
axioms lambdaDualE` works.

## Reusable patterns added to knowledge base

(Augments session 7 list; flows into PROJECT_STATUS.md.)

- **(NEW session 8) `show` to expose composed-application terms before `rw`.**
  When `rw`-ing perfect-pairing identities and the goal has `(f ∘ₗ g) e`,
  prepend `show ... f (g e) = ...` to surface the nested-application form.
  Without it, `rw` cannot pattern-match the identity.
- **(NEW session 8) Asymmetric isometry-hypothesis form for `leviGL_V0_conj_XCB`-style proofs.**
  Match the form produced by `comp_apply` rewrites: if the second arg comes
  from `(g : V →ₗ V) ∘ₗ C`, state `hgC v e'' = S.formV0 (g v) ((g : V →ₗ V) (C e''))`,
  not `S.formV0 ((g : V →ₗ V) v) ((g : V →ₗ V) (C e''))`. Asymmetric statement
  matches the asymmetric form `Cdual_pairing` rewrites produce.
- **(NEW session 8) `d.symm.symm = d` `rfl` for `LinearEquiv`** halves the
  work of inverse-pair proofs: apply `leviGL_E_symm_inverse S d.symm` for
  free other-direction inverse.
- **(NEW session 8) Block-matrix component-split closure pattern.**
  `refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩`
  for any `Module.End F (E × V0 × E')` identity, then close each component
  individually.
- **(NEW session 8) `leviGL_V0` no-isometry-bundle pattern.** Isometry
  hypothesis passed at consumer sites, not bundled in the def. Sidesteps
  session-7 subtype-wrapping anti-pattern.
- **(NEW session 8) `#print axioms` syntax detail.** Drop the `@` prefix:
  `#print axioms lambdaDualE` works; `#print axioms @lambdaDualE` fails
  with `Unknown constant axioms`.
- **(NEW session 8) `lean_run_code` `#check` for known-name API verification**
  is faster than `lean_loogle` / `leansearch` when the informal doc names
  the lemma. Workflow: read informal `-- Hint:` → `#check` to verify →
  write proof.

## Recommendations for next session

See `recommendations.md` for the prioritised next-round queue. Briefly:
Round 7 (NormalForm.lean — 3 sorries) is now structurally unblocked at
the Slice.lean API level. The plan agent should consider whether to:
(a) close `parabolic_decompose` first in Slice.lean (additive, ~85 lines)
then dispatch NormalForm with full machinery; or (b) skip `parabolic_decompose`
and have the NormalForm prover work around it via direct
`parametrizeX0PlusU_uniqueness` + `leviGL_*_isParabolic` calls (~40-line
saving for `residual_levi_extract`). The session-8 prover recommended (b)
in the task_results report.
