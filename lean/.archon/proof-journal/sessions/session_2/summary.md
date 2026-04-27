# Session 2 — Autoformalize (Round 2)

## Metadata

- **Session:** 2 (stage `autoformalize`, Round 2 — five parallel provers)
- **Iteration:** `iter-002` (mode `parallel`, five prover tasks)
- **Sorry count before:** 8 (`Basic.lean`:1, `X0Geometry.lean`:7)
- **Sorry count after:** 34
  - `InducedOrbitToy/Basic.lean`: 1 (unchanged)
  - `InducedOrbitToy/X0Geometry.lean`: 8 (+1 — bundled refactor preserved 7 + added 1 doc-comment hit; raw `grep "sorry"` of 8 includes one inside docstring; 7 actual sorry tactics)
  - `InducedOrbitToy/Slice.lean`: 11 (9 declaration uses + 2 docstring hits per task report; raw grep = 11 because of literal-`sorry` term-mode placeholders)
  - `InducedOrbitToy/NormalForm.lean`: 6 (5 theorem bodies + 1 placeholder `def`)
  - `InducedOrbitToy/LocalForms.lean`: 3
  - `InducedOrbitToy/Orbits.lean`: 5
- **Axioms introduced:** 0 (`#print axioms` for every public theorem reports only `[propext, sorryAx, Classical.choice, Quot.sound]`)
- **Targets attempted (parallel provers, five files):**
  - `InducedOrbitToy/X0Geometry.lean` — optional bundled refactor
  - `InducedOrbitToy/Slice.lean` — `lem:parametrize-x0-plus-u`, `lem:unipotent-conjugation`
  - `InducedOrbitToy/NormalForm.lean` — `prop:p-normal-form`, `prop:kernel-image`
  - `InducedOrbitToy/LocalForms.lean` — `lem:local-form-classes`
  - `InducedOrbitToy/Orbits.lean` — `prop:induced-orbits`, `prop:s-independence-and-orbit-criterion`, `prop:multiplicity`, `thm:main`
- **Build status:** `lake build` succeeds with only `sorry` warnings; full project compiles.
- **Pre-processed log:** 156 events, 5 edits, 8 diagnostic checks, 1 explicit `lean_build`, 21 lemma searches, 3 errors observed during the round (all later resolved).

## Process observation

Round 2 ran cleanly in parallel — all five files compiled at end of round. Cross-file
duplicate-declaration risk was managed organically: provers for `Orbits.lean` and
`LocalForms.lean` coordinated through reads (the Orbits prover noticed `IsSkewT`,
`Tset_circ`, `ClassifyBilinearForms`, `IsometryRel` were already defined upstream and
imported them). One transient breakage during the round (Orbits redeclared classes from
LocalForms) was self-corrected before the prover's final write.

## Target 1 — `InducedOrbitToy/X0Geometry.lean` (bundled refactor)

**Status:** solved (acceptance criteria met).

The optional refactor swapped every theorem signature from the unbundled
`(B, X0, Vplus, hcompl, …)` parameter pack to `(S : X0Setup F)`. Proof bodies preserved
as `sorry` per the round spec. The auxiliary parameter named `S` in `DualTransposeData`
and `sDual_restrict_ker_isIso` was renamed to `T` to avoid shadowing.

### Verification trail

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `Read X0Geometry.lean`, `Basic.lean` | confirmed bundled `X0Setup F` API and instance attributes |
| 2 | `lake env lean InducedOrbitToy/X0Geometry.lean` (pre-edit) | clean, 7 sorry warnings |
| 3 | `Write X0Geometry.lean` (full rewrite, 6226 chars) | bundled signatures + Tdual rename |
| 4 | `lake env lean InducedOrbitToy/X0Geometry.lean` | clean, 7 sorry warnings, no errors |
| 5 | `grep "(B :"` → empty; `grep -c "sorry"` → 8 (7 actual + 1 docstring); `grep -c "axiom"` → 0 | acceptance met |
| 6 | `#print axioms` per declaration | only `sorryAx`/`propext`/`Classical.choice`/`Quot.sound` |

### Final aggregate signature

```lean
theorem x0Geometry (S : X0Setup F)
    (hnondeg : S.formV0.Nondegenerate) :
    S.formV0.orthogonal (LinearMap.range S.X0) = LinearMap.ker S.X0
      ∧ Module.finrank F (S.V0 ⧸ LinearMap.range S.X0)
          = Module.finrank F (LinearMap.ker S.X0)
      ∧ Module.finrank F S.Vplus = c S
      ∧ (vplusKerPairing S).IsPerfPair
```

### What was learned

- Bundling drops 4 lines of `intro` boilerplate per proof in the upcoming prover stage.
- The structure-field rename trick (`Sdual` → `Tdual`) avoids parameter-name shadowing
  with the new `S : X0Setup F` argument, and is invisible to downstream callers (only
  `Slice.lean` re-exports, never reads the field directly).

## Target 2 — `InducedOrbitToy/Slice.lean`

**Status:** solved (acceptance criteria met) — autoformalization complete; all 9 named
declarations (4 lemmas + 5 supporting `def`s/theorems) compile.

### Verification trail

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `Read Slice.lean`, `Basic.lean`, `X0Geometry.lean` | initial scan |
| 2 | `lean_local_search "linearProjOfIsCompl"`, `"Submodule.linearProjOfIsCompl"`, `"IsPerfPair"` | empty results (priming) |
| 3 | `lean_hover_info LinearMap.mk₂` | confirmed signature for `BT` later |
| 4 | `lean_leansearch "IsAdjointPair bilinear form"`, `"LinearMap.compl₁₂ bilinear form"` | found `LinearMap.IsAdjointPair`, `LinearMap.BilinForm.comp` |
| 5 | `Write Slice.lean` (7797 chars) | one-shot draft with 9 sorry placeholders |
| 6 | `lean_diagnostic_messages` | 0 errors, 9 sorry warnings |
| 7 | `lake env lean InducedOrbitToy/Slice.lean` | clean except `sorry` warnings (lines 49, 54, 133, 141, 150, 167, 173, 180, 194) |
| 8 | `lake build InducedOrbitToy.Slice` | succeeds |
| 9 | `grep -c "sorry"` → 11 (9 declaration uses + 2 docstring); `grep -c "axiom"` → 0 | acceptance met |

### API exposed (matches `informal/slice.md`)

`IsSkewB`, `Cdual` (term-mode `sorry`), `Cdual_pairing_eq`, `X0Lift` (sorry-free),
`XCB` (sorry-free modulo `Cdual`), `projL1'`, `projL0'`, `CST`, `BST`, `XST`,
`parametrizeX0PlusU_mem`, `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`,
`uD` (term-mode `sorry`), `uD_neg_inverse`, `uD_isParabolic`, `uD_conj_XCB`.

### What was learned

- `Submodule.linearProjOfIsCompl` is the right Mathlib construct for the `L1' ⊕ L0'`
  decomposition; works directly off `IsCompl S.L1' S.L0'`.
- `Cdual` and `uD` are kept as term-mode `sorry` placeholders rather than abstract
  axioms — the prover stage can fill them in cleanly with the perfect-pairing inverse
  and the explicit block-matrix formula respectively.
- `X0Lift` is fully concrete via `LinearMap.fst`/`snd`/`inl`/`inr` over the `Prod`
  ambient — no `sorry`. Reusable pattern for any "embed an operator on a summand into
  the whole product" construction.

## Target 3 — `InducedOrbitToy/NormalForm.lean`

**Status:** solved (acceptance criteria met). Required 4 edits across 2 iterations to
resolve a `Decidable` synthesis issue and a wrong namespace for `IsAdjointPair`.

### Verification trail

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `Read NormalForm.lean`, `Slice.lean`, `Basic.lean`, `X0Geometry.lean` | priming |
| 2 | `Write NormalForm.lean` (9835 chars) | initial draft |
| 3 | `lake env lean InducedOrbitToy/NormalForm.lean` | **3 errors**: (a) `failed to synthesize Decidable (S.eps = 1 ∧ Odd l)` at line 78, (b) `Unknown constant LinearMap.BilinForm.IsAdjointPair` at line 111, (c) two `unusedSimpArgs` linter warnings on `BT`'s `simp` calls |
| 4 | `lean_loogle "LinearMap.BilinForm.IsAdjointPair"` | empty |
| 5 | `lean_loogle "IsAdjointPair"` | empty |
| 6 | `lean_local_search "IsAdjointPair"` | "Lean project path not set" |
| 7 | `lean_run_code` (sandbox) | confirmed `LinearMap.IsAdjointPair` lives at top of `LinearMap` namespace |
| 8 | Edit `MaximalRank` def: insert `open Classical in` before the `if … then …` | introduces `Classical.dec` for the conjunction |
| 9 | Edit `IsParabolicElement`: `LinearMap.BilinForm.IsAdjointPair` → `LinearMap.IsAdjointPair` | resolves missing constant |
| 10 | Edit `BT`'s simp calls: drop `LinearMap.add_apply`, `Submodule.coe_add`, `Submodule.coe_smul`, `LinearMap.smul_apply` arguments | resolves unused-simp linter |
| 11 | `lake env lean` re-run | only `sorry` warnings left |
| 12 | One more `Write` (round-up to 7794 chars) reorganising final theorem statements | final form |
| 13 | `lake build InducedOrbitToy.NormalForm` | succeeds |
| 14 | `lean_run_code` `#print axioms` for the five public theorems | only `[propext, sorryAx, Classical.choice, Quot.sound]` |

### Key code edits

```diff
- noncomputable def MaximalRank : ℕ :=
-   let l := Module.finrank F S.L0'
-   if S.eps = 1 ∧ Odd l then l - 1 else l
+ noncomputable def MaximalRank : ℕ :=
+   let l := Module.finrank F S.L0'
+   open Classical in if S.eps = 1 ∧ Odd l then l - 1 else l
```

```diff
- LinearMap.BilinForm.IsAdjointPair S.ambientForm S.ambientForm p p
+ LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p
```

```diff
- simp [map_add, LinearMap.add_apply, Submodule.coe_add]
+ simp [map_add]
```

### What was learned

- Mathlib's `IsAdjointPair` lives in the bare `LinearMap` namespace, **not**
  `LinearMap.BilinForm.IsAdjointPair`. Always sandbox-check (`lean_run_code` with a
  one-liner `#check`) before committing.
- `Decidable (S.eps = 1 ∧ Odd l)` is **not** automatically synthesised even with
  `[DecidableEq F]`. Either insert `open Classical in` locally or build the instance
  via `haveI`. A bare `open Classical in` *outside* a `def` block is a syntax error
  ("unexpected token 'open'; expected 'lemma'"); it must go inside the body or as an
  `attribute Classical.dec`-style `haveI`.
- Mathlib's lint-as-error mode (configured project-wide) means redundant `simp` args
  block builds. Always trim `simp` lists to the minimum.

## Target 4 — `InducedOrbitToy/LocalForms.lean`

**Status:** solved (acceptance criteria met). Required 2 edits to resolve the same
`Decidable` issue (`MaximalRank` was originally defined here too) and to delete the
local placeholders once the parallel `NormalForm` prover finished.

### Verification trail

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `Read LocalForms.lean`, `NormalForm.lean`, `Slice.lean`, `Basic.lean` | priming |
| 2 | `grep "local-form" references/blueprint_verified.md` | found blueprint anchors at lines 413, 547 |
| 3 | First `Write LocalForms.lean` (6724 chars) | included local `MaximalRank`, `Tset_circ`, etc. |
| 4 | `lake env lean` | error: `failed to synthesize Decidable (S.eps = 1 ∧ Odd l)` at line 65; 3 sorry warnings |
| 5 | First Edit: insert `open Classical in` before the `let l := …` (top-level) | new error: "unexpected token 'open'; expected 'lemma'" |
| 6 | Second Edit: replace top-level `open Classical in` with body-level `haveI : Decidable (S.eps = 1 ∧ Odd l) := Classical.dec _; if …` | clean |
| 7 | `lake env lean` | only 3 sorry warnings |
| 8 | `lake build` (full project) | succeeds |
| 9 | Second `Write LocalForms.lean` (4472 chars) | removed local duplicates; switched to `S.IsSkewT`, `S.MaximalRank`, `S.Tset_circ`, `S.BT` from `NormalForm` |
| 10 | `lake env lean InducedOrbitToy/LocalForms.lean` | succeeds, only 3 sorry warnings (lines 68, 81, 94) |
| 11 | `lean_run_code` `#print axioms` for `localFormClasses_finite`, `localFormClasses_open`, `localFormClasses` | only `[propext, sorryAx, Classical.choice, Quot.sound]` |

### Key code edit

```diff
- noncomputable def MaximalRank (S : SliceSetup F) : ℕ :=
-   let l := Module.finrank F S.L0'
-   if S.eps = 1 ∧ Odd l then l - 1 else l
+ noncomputable def MaximalRank (S : SliceSetup F) : ℕ :=
+   let l := Module.finrank F S.L0'
+   haveI : Decidable (S.eps = 1 ∧ Odd l) := Classical.dec _
+   if S.eps = 1 ∧ Odd l then l - 1 else l
```

After observing that the parallel `NormalForm` prover defined `MaximalRank` etc.
canonically, this file's second pass deleted its local copies and switched to the
`SliceSetup` namespace versions.

### API exposed

- `class ClassifyBilinearForms (F : Type*) [Field F] : Prop` — placeholder
- `def IsometryRel (S : SliceSetup F) : (S.L0' →ₗ[F] S.L0) → (S.L0' →ₗ[F] S.L0) → Prop`
- `theorem localFormClasses_finite` (sorry)
- `theorem localFormClasses_open` (sorry)
- `theorem localFormClasses` (sorry)

### What was learned

- The `haveI : Decidable _ := Classical.dec _` pattern is the in-body fix for the
  `Decidable` synthesis issue when `open Classical in` doesn't fit syntactically.
- Coordinating across parallel provers via "second pass to delete duplicates after
  the sibling prover lands its canonical version" is a viable pattern when the round
  finishes with all files green.

## Target 5 — `InducedOrbitToy/Orbits.lean`

**Status:** solved (acceptance criteria met).

### Verification trail

| Step | Tool | Outcome |
| --- | --- | --- |
| 1 | `Read Orbits.lean` (empty), `Basic.lean`, `LocalForms.lean`, `Slice.lean`, `NormalForm.lean`, `X0Geometry.lean` | full upstream survey |
| 2 | `lean_diagnostic_messages Orbits.lean` (relative path) | error: "Invalid Lean file path" — needed absolute path |
| 3 | `lean_diagnostic_messages /Users/.../Orbits.lean` (absolute) | clean (file is empty stub) |
| 4 | `lean_local_search "linearProjOfIsCompl"`, `"Submodule.linearProjOfIsCompl"`, `"IsPerfPair"`, `"Ring.inverse"` | all empty (priming) |
| 5 | `lean_leansearch "IsAdjointPair bilinear form"`, `"LinearMap.compl₁₂ bilinear form"` | found `LinearMap.IsAdjointPair`, `LinearMap.BilinForm.comp` |
| 6 | `lean_loogle "LinearMap.IsAdjointPair"`, `"LinearMap.IsOrthogonal"`, `"Module.End"` | confirmed `LinearMap.IsOrthogonal` lives in `Mathlib.LinearAlgebra.SesquilinearForm.Basic` |
| 7 | First `Write Orbits.lean` (8167 chars) | initial draft |
| 8 | `lean_diagnostic_messages` | error: "invalid binder annotation, type is not a class instance" at lines 101, 105 — typeclass-binder mistake |
| 9 | Second `Write Orbits.lean` (6951 chars) | rewrote the typeclass-bracketed parameters as plain `(_ : …)` and made `IndPG`/`Multiplicity` take the topology as a hypothesis instead of an instance |
| 10 | `lean_diagnostic_messages` | clean except expected `sorry` warnings |
| 11 | `lake env lean InducedOrbitToy/Orbits.lean` | succeeds, only sorries |
| 12 | `lake build` | succeeds (8033/8033) |
| 13 | `lean_verify InducedOrbitToy.main` | axioms: `[propext, sorryAx, Classical.choice, Quot.sound]`, plus a flagged `opaque` pattern at line 87 (acceptable; matches the informal sketch's "Multiplicity is opaque ℕ") |

### API exposed (matches `informal/orbits.md`)

`IsometryEnd`, `IsometryV0`, `IsInP`, `GOrbit`, `O0`, `embO0` (sorry-free),
`O0PlusU`, `IndPG` (takes topology hypothesis), `Multiplicity` (placeholder `ℕ`,
takes topology hypothesis); theorems `inducedOrbits` (containment form),
`sIndependenceAndOrbitCriterion`, `multiplicityNonDeg`, `multiplicityOddCase`, `main`.

### What was learned

- `[TopologicalSpace (Module.End F S.V)]` cannot be stated as an instance binder
  on the file-level `variable`; Lean rejects the binder annotation when the type's
  metavariable cannot be resolved. **Fix:** thread the topology as an explicit
  argument on each theorem that needs it.
- `Ring.inverse g` is the right way to get a "best-effort inverse" inside an orbit
  predicate when the ring isn't necessarily a division ring; for unit `g` it returns
  the genuine inverse, for non-units it returns `0`. Combined with an `IsUnit g`
  side-condition this is information-preserving.
- `LinearMap.IsOrthogonal` (in `Mathlib.LinearAlgebra.SesquilinearForm.Basic`) is
  the right notion of "form-preserving endomorphism" — no need to roll a custom
  `IsometryEnd` from scratch beyond bundling the unit + `IsOrthogonal`.

## Cross-cutting findings

1. **Cross-file coordination via post-hoc deletion.** Two provers (LocalForms and Orbits)
   initially staged local copies of `IsSkewT`, `Tset_circ`, `ClassifyBilinearForms`,
   `IsometryRel` because their upstream files were stubs at start of round. Both
   provers self-corrected to import-and-reuse once the sibling provers' work landed.
   This worked but is fragile; explicit dependency ordering would have avoided the
   duplicate-declaration error window.
2. **Two recurring Lean gotchas surfaced this round:**
   - `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise — needs `open Classical in`
     (in-body) or `haveI : Decidable _ := Classical.dec _`.
   - `LinearMap.IsAdjointPair`, **not** `LinearMap.BilinForm.IsAdjointPair`. The
     latter does not exist in current Mathlib.
3. **`[TopologicalSpace (Module.End F S.V)]` as a `variable` instance binder fails**
   ("invalid binder annotation, type is not a class instance"); thread it as an
   explicit hypothesis on each theorem instead.
4. **MCP `lean_diagnostic_messages` requires absolute paths** — same gotcha as
   session 1, hit again at the start of the Orbits prover.
5. **Mathlib coverage remains adequate.** No `axiom` declarations were introduced.
   The only "missing" Mathlib piece is the component-group `π₀(Z_G(x) ∩ P)` needed
   to define `Multiplicity` non-trivially; the round handled this via the informal
   sketch's opaque-`ℕ` placeholder, which is the correct deferral.
6. **`#print axioms` audit:** every public theorem in the five files depends only
   on `[propext, sorryAx, Classical.choice, Quot.sound]`. No custom `axiom`
   leaks anywhere.

## Recommendations for next session

See `recommendations.md`. TL;DR: Round 2 closes successfully — total 34 sorries, 0
custom axioms, full `lake build` green. The next stage is `prover` (discharge the
34 sorries, prioritising the X0Geometry chain since it's the most self-contained
and has the cleanest Mathlib hints).
