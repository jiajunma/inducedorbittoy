# Session 1 — Autoformalize (Round 1)

## Metadata

- **Session:** 1 (first session of the project, stage `autoformalize`)
- **Iteration:** `iter-001` (mode `parallel`, plan 179s, prover 679s)
- **Sorry count before:** 0 (no `.lean` content yet)
- **Sorry count after:** 8 actual `sorry` tactic calls
  - `InducedOrbitToy/Basic.lean`: 1
  - `InducedOrbitToy/X0Geometry.lean`: 7
  - (an additional `grep "sorry"` hit in `X0Geometry.lean` line 25 is inside a docstring, not a tactic)
- **Axioms introduced:** 0 (`#print axioms` confirmed only `propext`, `Classical.choice`, `Quot.sound`, plus `sorryAx` for the placeholder)
- **Targets attempted (parallel provers):**
  - `InducedOrbitToy_Basic` → `InducedOrbitToy/Basic.lean` (planned Round 1 target)
  - `InducedOrbitToy_X0Geometry` → `InducedOrbitToy/X0Geometry.lean` (planned for Round 2; dispatched out of sequence)

## Process / sequencing observation (important)

`PROGRESS.md` explicitly stated that Round 1 is *"only `InducedOrbitToy/Basic.lean`"* and that the five Round 2 modules (`X0Geometry.lean`, `Slice.lean`, `NormalForm.lean`, `LocalForms.lean`, `Orbits.lean`) must wait until `Basic.lean` exposes the shared algebra. Despite that, the harness dispatched **two provers in parallel**: one on `Basic.lean` and one on `X0Geometry.lean`. The X0Geometry prover ran while `Basic.lean` was still an empty stub, so it had to mirror the predicates locally. This is recoverable but creates duplicate names (`InducedOrbitToy.IsEpsSymm`, `InducedOrbitToy.IsSkewAdjoint`) that must be reconciled before Round 2.

## Target 1 — `InducedOrbitToy/Basic.lean`

**Status:** solved (acceptance criteria met).

The prover wrote the entire foundational module in **a single `Write` call** — no iterative editing was needed. The pre-processed event log shows zero `code_change` events for this file (only one `code_write` of the full 8186-character file). All diagnostics came back clean except for the deliberate `sorry` warning at line 117.

### Verification trail

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `lean_local_search "LinearMap.BilinForm"` | `Lean project path not set. Call a file-based tool first.` (priming step) |
| 2 | `lean_diagnostic_messages Basic.lean` (pre-write) | 0 errors, 0 warnings on the empty stub |
| 3 | `lean_loogle "LinearMap.BilinForm"` | confirmed `LinearMap.BilinForm` lives in `Mathlib.LinearAlgebra.BilinearMap` |
| 4 | `lean_loogle "LinearMap.BilinMap"` | confirmed `LinearMap.BilinMap` for distinct-space pairings |
| 5 | `lean_leansearch "perfect pairing of vector spaces"` | found `LinearMap.IsPerfPair`, `LinearMap.IsPerfPair.of_injective` |
| 6 | `lean_run_code` (sandbox) — first attempt with `LinearMap.mk₂` had a type-class instance error | iterated to a working signature |
| 7 | `lean_run_code` — second attempt succeeded; signature `LinearMap.mk₂ F (...) (linearity_proofs)` confirmed |
| 8 | `Write Basic.lean` (8186 chars) | created file in one shot |
| 9 | `lean_diagnostic_messages` | 0 errors, 1 warning (the intentional `sorry` at line 117) |
| 10 | `lake env lean InducedOrbitToy/Basic.lean` | clean except `Basic.lean:117:8: warning: declaration uses 'sorry'` |
| 11 | `lake build InducedOrbitToy.Basic` | `⚠ [8026/8026] Built InducedOrbitToy.Basic (10s)` |
| 12 | `#print axioms` for three key declarations | only standard axioms + `sorryAx` for `c_eq_finrank_quotient`; `SliceSetup.ambientForm` and `UnipotentRadical` are sorry-free |

### API exposed (matches `PROGRESS.md` spec)

- Predicates: `IsEpsSymm`, `IsSkewAdjoint`, `IsPerfectPairing`, `IsPaired`, `IsIsotropic`.
- Structures: `PairedSpaces F`, `X0Setup F`, `SliceSetup F extends X0Setup F`.
- Numeric: `c (S : X0Setup F) : ℕ := Module.finrank F (LinearMap.ker S.X0)`.
- Lone placeholder lemma: `c_eq_finrank_quotient (S) : c S = Module.finrank F (S.V0 ⧸ LinearMap.range S.X0) := by sorry`.
- `SliceSetup` namespace: `S.E`, `S.E'`, `S.lambda`, `S.V := E × V0 × E'`, `S.ambientForm` (noncomputable, built via `LinearMap.mk₂`), `S.flagE`, `S.flagEV0`.
- `IsParabolic`, `UnipotentRadical` — fully defined; the latter is a `Submodule` whose `add_mem'`, `zero_mem'`, `smul_mem'` proofs go through without `sorry`.

### Single open obligation

```lean
theorem c_eq_finrank_quotient (S : X0Setup F) :
    c S = Module.finrank F (S.V0 ⧸ LinearMap.range S.X0) := by sorry
```

The `Basic.md` task report flags `Submodule.finrank_quotient_add_finrank` and `LinearMap.finrank_range_add_finrank_ker` as the standard tools to discharge it. No Mathlib gap.

### What was learned

- `LinearMap.mk₂` is the right Mathlib constructor for the ambient bilinear form on `E × V0 × E'`; the four linearity-proof obligations close cleanly with `simp [Prod.fst_add, Prod.snd_add, ...]; ring`.
- Bundling instances inside the structure with `[addCommGroupV0 : AddCommGroup V0]` and re-exposing them with `attribute [instance]` lets downstream files write `(S : X0Setup F)` and immediately use `S.V0` as a module without re-stating instances.
- `IsPerfectPairing` was kept as a project-local predicate even though Mathlib has `LinearMap.IsPerfPair`; the report flags this as an intentional choice and notes that an equivalence lemma can be added later if needed.

## Target 2 — `InducedOrbitToy/X0Geometry.lean`

**Status:** partial (file compiles, 7 `sorry`s remain — all delegated to the prover stage).

### Verification trail (with the one actual `code_change` recorded)

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `lean_loogle "IsPerfectPairing"` | no results |
| 2 | `lean_loogle "PerfectPairing"` | rate-limited |
| 3 | `lean_leansearch "perfect pairing finite dimensional vector spaces"` | found `LinearMap.IsPerfPair.of_injective` |
| 4 | `lean_leansearch "orthogonal complement of bilinear form submodule"` | found `LinearMap.BilinForm.orthogonal`, `Submodule.orthogonalBilin` |
| 5 | `lean_leansearch "range linear map orthogonal complement bilinear form ker"` | candidate lemmas for `(Im X0)⊥ = ker X0` |
| 6 | `lean_leansearch "finrank quotient range linear map ker"` | `LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank` family |
| 7 | `lean_leansearch "restrict bilinear form to submodule"` | `LinearMap.BilinForm.restrict`, `LinearMap.domRestrict₁₂` |
| 8 | `lean_loogle "LinearMap.BilinForm.orthogonal"` | confirmed `B.orthogonal N : Submodule R M` |
| 9 | `Write X0Geometry.lean` | initial draft, 8105 chars |
| 10 | `lean_diagnostic_messages` (relative path `InducedOrbitToy/X0Geometry.lean`) | tool error: "no `lean-toolchain` ancestor" — relative path bug |
| 11 | `lean_diagnostic_messages` (absolute path) | **error** + 3 sorry warnings; the error was that `def c` was a non-computable use of `Module.finrank` |
| 12 | **Edit** at line of `def c (...) : ℕ := Module.finrank F (LinearMap.ker X0)` | inserted `noncomputable` keyword (see `code_change` below) |
| 13 | `lean_diagnostic_messages` (absolute path) | clean except 7 `sorry` warnings |
| 14 | `lake env lean InducedOrbitToy/X0Geometry.lean` | exit 0; only the seven `sorry` warnings |

### The single `code_change` event

```diff
- def c (F : Type*) {V0 : Type*} [Field F]
-     [AddCommGroup V0] [Module F V0] (X0 : V0 →ₗ[F] V0) : ℕ :=
-   Module.finrank F (LinearMap.ker X0)
+ noncomputable def c (F : Type*) {V0 : Type*} [Field F]
+     [AddCommGroup V0] [Module F V0] (X0 : V0 →ₗ[F] V0) : ℕ :=
+   Module.finrank F (LinearMap.ker X0)
```

`Module.finrank` is `noncomputable`, so the resulting `def` had to be marked the same. Once added, the diagnostic dropped from `error_count: 1` to `error_count: 0`.

### Sorry inventory (all stubs from autoformalize)

| Line | Declaration | Blueprint clause | Strategy hint (from task report) |
| --- | --- | --- | --- |
| 54 | `ker_le_orthogonal_range` | `ker X0 ≤ (Im X0)⊥` | unfold `IsSkewAdjoint`, `LinearMap.BilinForm.mem_orthogonal_iff`, `mem_range` |
| 67 | `orthogonal_range_eq_ker` | `(Im X0)⊥ = ker X0` | combine 54 with `Submodule.finrank_add_finrank_orthogonal` for nondegenerate `B` |
| 78 | `finrank_quotient_range_eq_finrank_ker` | `dim(V0/Im X0) = dim ker X0` | `Submodule.finrank_quotient` + `LinearMap.finrank_range_add_finrank_ker` |
| 91 | `finrank_Vplus_eq_c` | `dim Vplus = c` | `Submodule.finrank_sup_add_finrank_inf_eq` with the `IsCompl` hypothesis |
| 104 | `VplusEquivQuotientRange` (`def` with `(sorry : ...)` body) | `Vplus ≃ V0 / Im X0` | `Submodule.quotientEquivOfIsCompl` |
| 125 | `vplusKerPairing_isPerfPair` | perfect pairing `Vplus × ker X0 → F` | `LinearMap.IsPerfPair.of_injective` after both injectivities |
| 171 | `sDual_restrict_ker_isIso` | `S^∨\|_{ker X0} : ker X0 ≃ L1` | compose previous perfect pairing with `lambda` and with `S` |

The aggregate `theorem x0Geometry` (line 178) is **sorry-free**: it `refine`s to four conjuncts and discharges each by `exact` of one of the lemmas above. So filling the seven sorries in this file plus the one in `Basic.lean` closes `lem:x0-geometry`.

### What was learned

- `LinearMap.IsPerfPair` is the right Mathlib notion (the project-local `IsPerfectPairing` in `Basic.lean` should be reconciled with it before Round 2 — the task report explicitly recommends this).
- `LinearMap.BilinForm.orthogonal` is the canonical `Submodule R M` orthogonal-complement constructor; do not roll your own.
- `LinearMap.domRestrict₁₂` cleanly produces the bilinear restriction `Vplus →ₗ[F] (ker X0) →ₗ[F] F` from a `LinearMap.BilinForm F V0`.
- The `lean_diagnostic_messages` MCP tool requires **absolute paths**; relative paths fail with `"no lean-toolchain ancestor"`.

## Cross-cutting findings

1. **Naming collision risk.** Both files declare `InducedOrbitToy.IsEpsSymm` and `InducedOrbitToy.IsSkewAdjoint` (with identical types). Currently they live in `namespace InducedOrbitToy` in *different* files, so `import InducedOrbitToy.Basic` from `X0Geometry.lean` may pick up Basic's version *or* shadow it depending on the module ordering. The `X0Geometry.lean` task report explicitly asks the next iteration to delete the local copies and re-route to Basic's canonical definitions. **The library does not yet have a top-level `InducedOrbitToy.lean` aggregator that imports both files**, so the collision has not actually been triggered yet.
2. **Plan vs. execution mismatch.** Round 2 should not have started. The X0Geometry prover did useful work, but its lemma signatures use ad-hoc hypotheses (`B`, `X0`, `Vplus`, `IsCompl Vplus (range X0)`, …) instead of consuming a single `S : X0Setup F`. The next plan iteration should rewrite the X0Geometry signatures to take `(S : X0Setup F)` so the bundled API actually carries weight.
3. **Mathlib coverage looks adequate.** Both task reports independently report "no Mathlib gap detected." The blueprint's block-matrix manipulations decompose cleanly over `Prod`-projections; the perfect-pairing API is `LinearMap.IsPerfPair`; orthogonal complements are `LinearMap.BilinForm.orthogonal`.
4. **`lean_loogle` rate limit (3/30s) was hit once.** Switching to `lean_leansearch` (10/30s by default in this MCP setup) is the intended workaround.

## Recommendations for next session

See `recommendations.md`.
