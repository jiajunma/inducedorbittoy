# Recommendations for Next Plan Iteration (post-session 2)

## TL;DR

Round 2 of the autoformalize stage is **complete**. All five `.lean` files
build cleanly with only `sorry` warnings. The repo carries 34 sorries
distributed across six files, **0 custom axioms**, and `lake build` is
green end-to-end.

The next plan iteration should advance the project to the **prover stage**.
The bundled API in `Basic.lean` and `X0Geometry.lean` is mature enough that
provers can be dispatched per-file (or even per-theorem) without further
structural rework.

## Stage transition

`PROGRESS.md` should be updated to:

```markdown
## Current Stage
prover
```

with `autoformalize` checked off. The stage README should record:
- Total sorries to discharge: 34 (1 + 8 + 11 + 6 + 3 + 5 across the six files).
- Custom axioms: 0 (target: stay at 0).
- Build state at session boundary: `lake build` green.

## Priority 1 — Prover dispatch order (closest-to-complete first)

The X0Geometry sorries are the most self-contained and have the cleanest
Mathlib hints (carried over from session 1's recommendations). Discharging
them unblocks the `x0Geometry` aggregator, which is then citeable from
`Slice.lean`'s parametrisation lemmas.

### Tier 1 — X0Geometry chain (8 sorries; closes `lem:x0-geometry`)

| File:Line | Theorem | Mathlib lemma to use |
| --- | --- | --- |
| `Basic.lean:119` | `c_eq_finrank_quotient` | `Submodule.finrank_quotient_add_finrank` + `LinearMap.finrank_range_add_finrank_ker` |
| `X0Geometry.lean` | `ker_le_orthogonal_range` | unfold `IsSkewAdjoint`; `LinearMap.BilinForm.mem_orthogonal_iff` + `LinearMap.mem_range` |
| `X0Geometry.lean` | `orthogonal_range_eq_ker` | combine the previous lemma with `Submodule.finrank_add_finrank_orthogonal` (needs `Nondegenerate`) |
| `X0Geometry.lean` | `finrank_quotient_range_eq_finrank_ker` | same machinery as `c_eq_finrank_quotient` (factor out a helper) |
| `X0Geometry.lean` | `finrank_Vplus_eq_c` | `Submodule.finrank_sup_add_finrank_inf_eq` with the `IsCompl` hypothesis |
| `X0Geometry.lean` | `VplusEquivQuotientRange` (term-mode) | `Submodule.quotientEquivOfIsCompl` |
| `X0Geometry.lean` | `vplusKerPairing_isPerfPair` | `LinearMap.IsPerfPair.of_injective` after both injectivities |
| `X0Geometry.lean` | `sDual_restrict_ker_isIso` | compose perfect pairing with `S.lambda` and `S` |

**Recommendation:** dispatch a single prover for `Basic.lean :: c_eq_finrank_quotient`
+ the seven `X0Geometry.lean` sorries. They share machinery and the bundled `(S : X0Setup F)`
signature already lets the prover skip 4 lines of `intro` per proof.

### Tier 2 — Slice.lean (9–11 sorries)

The two term-mode `sorry`s in `Cdual` and `uD` are the primary blockers. Once
they are constructions, the seven theorem sorries fall out of direct block-matrix
calculation on `S.V = E × V0 × E'`.

Suggested order:
1. Replace `Cdual`'s term-mode `sorry` using `S.paired.isPerfect` + `LinearMap.IsPerfPair`
   (the perfect pairing inverts `flip S.lambda` in finite dimension).
2. Prove `Cdual_pairing_eq` directly from the construction.
3. Replace `uD`'s term-mode `sorry` with the explicit `(e + Cdual D v + ½ Cdual D (D e'), v + D e', e')`
   block-matrix formula. Introduce `Invertible (2 : F)` from `(2 : F) ≠ 0` for the `½` factor.
4. Discharge `parametrizeX0PlusU_mem`, `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`,
   `uD_neg_inverse`, `uD_isParabolic`, `uD_conj_XCB` by direct `Prod` calculation.

### Tier 3 — NormalForm.lean (5 theorem sorries + 1 placeholder def)

The five theorems are stated directly in terms of `S.V = E × V0 × E'` with the
`kerXST_submod` and `imXST_submod` helper definitions. Recommend the prover
introduce a clean `LinearEquiv` between `S.V` and an abstract direct sum
`E ⊕ V0 ⊕ E'` first, then phrase the kernel/image computations against the
abstract sum. This is a **refactor** that will pay off across multiple sorries.

### Tier 4 — LocalForms.lean (3 theorem sorries)

Currently `localFormClasses_finite` and `localFormClasses_open` rely on the
opaque typeclass `[ClassifyBilinearForms F]`. Two paths forward:
- **Path A (recommended):** keep the typeclass abstract; prove the finiteness/openness
  from its hypothetical content (whatever invariants are exposed). This requires
  enriching the typeclass content beyond the current vacuous `∃ _ : ℕ, True`.
- **Path B:** introduce concrete instances for `F = ℝ` and non-archimedean local
  fields. This depends on Mathlib classification infrastructure that may not be
  in place yet; verify before committing.

### Tier 5 — Orbits.lean (5 theorem sorries)

This is the riskiest module. **Three statement-level deferrals** need plan
attention before the prover stage:

1. **`inducedOrbits` is the containment form, not the maximal-orbit
   classification.** Decide whether the polish stage can lift to the
   blueprint statement, or whether to introduce a "maximal `G`-orbit"
   notion and re-state.
2. **`Multiplicity` is the constant `0` placeholder.** The honest fix is
   either (a) lift `Multiplicity` to a hypothesis on each downstream theorem
   (`(m : ℕ) (hm : Multiplicity (XST Sₕ T) = m)`), touching every call site,
   or (b) leave the placeholder and have `multiplicityNonDeg` /
   `multiplicityOddCase` become `0 = 1` / `0 = 2` (false statements!). Path
   (a) is the only viable one — please plan this refactor explicitly.
3. **Topology threading.** `IndPG` and `Multiplicity` carry
   `(_ : TopologicalSpace (Module.End F S.V))` as an explicit argument.
   Provers should consume this hypothesis cleanly; do not try to instantiate
   a default topology.

## Priority 2 — Reusable proof patterns (carry forward)

These patterns landed in this round and should be reused in subsequent provers:

1. **`open Classical in if … then … else` *inside* a definition body** for
   non-decidable conditions on field elements. Top-level `open Classical in noncomputable def …`
   is a syntax error.
2. **`haveI : Decidable _ := Classical.dec _`** as the in-body alternative
   when `open Classical in` doesn't fit.
3. **Trim `simp` arg lists.** The Mathlib lints-as-errors policy makes
   redundant `simp` arguments build-breaking. Use only what closes the goal.
4. **`LinearMap.IsAdjointPair`, not `LinearMap.BilinForm.IsAdjointPair`.**
   The latter does not exist. Sandbox-check (`lean_run_code` with `#check`)
   before committing any `IsAdjointPair`-style call.
5. **Topology as explicit hypothesis on theorems**, not as file-level `variable`
   instance binder, when the type involves a metavariable.
6. **`Submodule.linearProjOfIsCompl`** is the right Mathlib construct for
   `IsCompl`-driven decomposition projections.
7. **`Ring.inverse g`** is the right "best-effort inverse" inside orbit
   predicates (returns `0` for non-units, the genuine inverse for units;
   combine with `IsUnit g` side-condition for information-preserving use).
8. **Block-matrix embedding via `LinearMap.fst`/`snd`/`inl`/`inr` over `Prod`**
   (see `X0Lift` and `embO0`) — sorry-free, reusable for any "embed an operator
   on a summand into the whole product" construction.

## Priority 3 — Tooling notes

(carry forward from session 1 — still relevant)

- `lean_diagnostic_messages` MCP requires **absolute file paths**.
- `lean_loogle` rate-limited at 3/30s; fall back to `lean_leansearch` (10/30s).
- `Module.finrank` is `noncomputable`; any `def` invoking it must be marked
  `noncomputable`.

## Targets that are blocked / should not be retried this round

**None as Mathlib gaps.** All open work has a clear Mathlib path forward.

The only "soft" blockers are statement-level (Orbits.lean items 1–3 in Tier 5
above). The plan agent should resolve those *as a planning task* before
dispatching the Orbits prover, not retry them inside the prover stage.

## Process recommendations

1. **Sequencing held up well in parallel this round.** All five provers ran
   in parallel and the cross-file deduplication (LocalForms vs NormalForm,
   Orbits vs LocalForms+NormalForm) was managed organically. No need to gate
   the prover stage if the bundled API is stable. Continue parallel dispatch.
2. **The optional X0Geometry refactor was the right call.** Bundled signatures
   are now uniform across files; provers won't need to thread unbundled
   parameters anywhere.
3. **Plan for the Orbits.lean statement refinements** (Tier 5 above) **before**
   the prover stage starts — the placeholder `Multiplicity` definition is a
   ticking time bomb (provers will hit `0 = 1` if they try to discharge
   `multiplicityNonDeg` against the current placeholder).
