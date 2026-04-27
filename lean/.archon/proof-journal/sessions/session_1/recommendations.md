# Recommendations for Next Plan Iteration

## TL;DR

Round 1 (`Basic.lean`) is **structurally complete** with the planned API exposed. Round 2 was unintentionally started: `X0Geometry.lean` exists and still uses ad-hoc unbundled hypotheses.

Post-review reconciliation already removed the duplicate `IsEpsSymm` / `IsSkewAdjoint` definitions from `X0Geometry.lean`, renamed the local `c` helper to `cX0`, and restored full `lake build`.

The next plan iteration should:

1. Optionally refactor `X0Geometry.lean` to consume bundled `(S : X0Setup F)` instead of unbundled parameters.
2. Issue Round 2 properly — the four remaining files (`Slice.lean`, `NormalForm.lean`, `LocalForms.lean`, `Orbits.lean`) plus the optional bundled refactor pass on `X0Geometry.lean`.
3. Schedule the prover stage for the eight `sorry`s already on disk.

---

## Priority 1 — Reconcile `Basic.lean` ↔ `X0Geometry.lean`

**Status:** The local `def IsEpsSymm` and `def IsSkewAdjoint` have already been deleted after review. Remaining optional work: rewrite every lemma signature in `InducedOrbitToy/X0Geometry.lean` to consume a bundled `(S : X0Setup F)` instead of the current `(B : LinearMap.BilinForm F V0) (X0 : V0 →ₗ[F] V0) (Vplus : Submodule F V0) (hcompl : IsCompl Vplus (LinearMap.range X0))` parameter pack.

**Why:** Without the rewrite, downstream files cannot reuse the X0Geometry lemmas through the bundled API; we get two incompatible "calling conventions" for the same content.

**Suggested target signature (from `task_results/X0Geometry.md`):**

```lean
theorem x0Geometry (S : X0Setup F)
    (hε : S.eps = 1 ∨ S.eps = -1) (hsymm : IsEpsSymm S.formV0 S.eps)
    (hnondeg : S.formV0.Nondegenerate) :
    S.formV0.orthogonal (LinearMap.range S.X0) = LinearMap.ker S.X0
      ∧ Module.finrank F (S.V0 ⧸ LinearMap.range S.X0)
          = Module.finrank F (LinearMap.ker S.X0)
      ∧ Module.finrank F S.Vplus = c S
      ∧ (vplusKerPairing S.formV0 S.X0 S.Vplus).IsPerfPair
```

(`X0Setup` already carries `epsValid`, `epsSymm`, and `isCompl`, so a bundled version can drop several explicit hypotheses entirely.)

**Acceptance:** After the rewrite, `grep -n "def IsEpsSymm\|def IsSkewAdjoint" InducedOrbitToy/X0Geometry.lean` returns nothing, and `lake build InducedOrbitToy.X0Geometry` still succeeds.

---

## Priority 2 — Targets closest to completion (recommend prioritising in the prover stage)

These are the eight existing sorries. Each comes with a concrete Mathlib hint.

### Highest-leverage (closes `lem:x0-geometry` modulo reconciliation above)

| Sorry | Mathlib lemma to use |
| --- | --- |
| `c_eq_finrank_quotient` (Basic.lean:117) | `Submodule.finrank_quotient_add_finrank` + `LinearMap.finrank_range_add_finrank_ker` (rank-nullity) |
| `ker_le_orthogonal_range` (X0Geometry.lean:54) | unfold `IsSkewAdjoint`, then `LinearMap.BilinForm.mem_orthogonal_iff` + `LinearMap.mem_range` |
| `orthogonal_range_eq_ker` (X0Geometry.lean:67) | combine the previous lemma with `Submodule.finrank_add_finrank_orthogonal` (needs `Nondegenerate`) for the reverse inclusion via dimension |
| `finrank_quotient_range_eq_finrank_ker` (X0Geometry.lean:78) | `Submodule.finrank_quotient_add_finrank` + `LinearMap.finrank_range_add_finrank_ker` (same machinery as `c_eq_finrank_quotient`; the two should likely share a helper) |
| `finrank_Vplus_eq_c` (X0Geometry.lean:91) | `Submodule.finrank_sup_add_finrank_inf_eq` together with the `IsCompl Vplus (range X0)` hypothesis to extract `dim Vplus = dim (V0/range X0)` |
| `VplusEquivQuotientRange` (X0Geometry.lean:104, term-mode `(sorry : _)`) | `Submodule.quotientEquivOfIsCompl` (Mathlib has it directly) |
| `vplusKerPairing_isPerfPair` (X0Geometry.lean:125) | `LinearMap.IsPerfPair.of_injective` after showing both `Vplus` and `ker X0` inject into the dual via the restricted form |

### Slightly harder (needs the bundled `lambda` from `PairedSpaces`)

| Sorry | Notes |
| --- | --- |
| `sDual_restrict_ker_isIso` (X0Geometry.lean:171) | composes the perfect pairing `Vplus × ker X0 → F` with `lambda`'s perfect pairing `E × E' → F`; requires `DualTransposeData`'s pointwise identity. Best done **after** the bundled rewrite from Priority 1, so that `lambda` lives on the structure. |

---

## Priority 3 — Promising approaches that need more work

- **`LinearMap.mk₂` + `Prod` projections for the ambient form `V := E × V0 × E'`.** The pattern in `Basic.lean` lines 155–176 (four linearity sub-proofs each closed by `simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]; ring` or its `smul` analogue) is reusable for any future bilinear form on a `Prod`-of-`Prod` ambient space. The `NormalForm.lean` and `LocalForms.lean` modules will likely need similar constructions; lean on this template.
- **Submodule with explicit carrier predicate + manually proved `add_mem'`/`smul_mem'`/`zero_mem'`.** The `UnipotentRadical` definition in `Basic.lean` (lines 205–236) shows the pattern: tuple-of-conditions carrier, `simpa [LinearMap.add_apply] using Submodule.add_mem _ ...`. Reusable for `IsParabolic`'s constructive variant if needed and for any later "operators preserving a flag" submodule.

---

## Priority 4 — Round 2 dispatch (the four files not yet started)

`Slice.lean`, `NormalForm.lean`, `LocalForms.lean`, `Orbits.lean` are still untouched. After the X0Geometry refactor lands, these four can run **in parallel** since `Basic.lean` already exposes `X0Setup`, `SliceSetup`, `PairedSpaces`, `IsParabolic`, `UnipotentRadical`, `c`, the ambient form, and the flag.

Suggested per-file blueprint coverage (cross-checked against the blueprint TOC the autoformalize prover already mapped out in `task_results/X0Geometry.md`):

- `Slice.lean` → `lem:parametrize-x0-plus-u` (lines 56–119 of `references/blueprint_verified.md`).
- `NormalForm.lean` → "block matrix" presentations (lines 83–113).
- `LocalForms.lean` → local form classification.
- `Orbits.lean` → induced-orbit characterisation.

---

## Targets that are blocked / should not be retried this round

**None.** No Mathlib gap was discovered. Both task reports independently confirm the standard finite-dimensional API suffices. The only "blocker" is process (the parallel dispatch shouldn't have run X0Geometry early), which is fixable by sequencing the next iteration correctly.

---

## Reusable proof patterns discovered

1. **`LinearMap.mk₂` over a `Prod` ambient** — see Priority 3 above.
2. **Bundled instance fields via `attribute [instance]`** — `PairedSpaces`, `X0Setup`, `SliceSetup` show how to bundle `[AddCommGroup _] [Module F _] [Module.Finite F _]` inside a structure and re-export them so downstream files can write `(S : X0Setup F)` and immediately use `S.V0` as a typeclass-resolved module.
3. **MCP gotcha — absolute paths only.** `lean_diagnostic_messages` requires absolute file paths. Document this in the prover prompts to save a round trip in future sessions.
4. **`lean_loogle` rate limit (3/30s)** — fall back to `lean_leansearch` (10/30s) when hit.

---

## Process recommendation for the harness

The plan agent should **enforce** the Round 1 / Round 2 sequencing it declares. In this session, Round 2 provers received `Basic.lean` empty and had to do duplicate work. Either gate Round 2 on Round 1 completion or avoid declaring sequencing that the dispatcher ignores.
