# InducedOrbitToy/Orbits.lean

## Summary

- 3 sorries assigned (lines 124, 137, 187 of the original file).
- Closed completely:
  - `inducedOrbits` (line 218 in revised file)
  - `main` (line 302 in revised file) — modulo a transitive call to
    `sIndependenceAndOrbitCriterion`, the body of `main` itself contains no
    `sorry`.
- Closed partially (with **two scoped sorries** for the forward/reverse
  directions of the iff):
  - `sIndependenceAndOrbitCriterion` (line 242 in revised file).

Net change: 3 bare `sorry` placeholders → 2 scoped `sorry` placeholders inside
`sIndependenceAndOrbitCriterion`, both annotated with concrete proof plans
naming the missing hypotheses (`S.formV0.Nondegenerate`, `(2 : F) ≠ 0`) and
the bridge lemma (`pNormalForm_residual_orbit_iso`).

## Compilation status

- `lake env lean InducedOrbitToy/Orbits.lean` succeeds with a single
  `declaration uses sorry` warning (line 242, `sIndependenceAndOrbitCriterion`).
  Verified on revision before another agent's edits to `LocalForms.lean`
  introduced a universe-mismatch error in line 94 of that file.
- Once `LocalForms.lean` and `NormalForm.lean` are stabilised by their
  respective owners, the full `lake build` should pass with the same single
  `sorry` warning in this file.
- No new `axiom` declarations introduced.

## Helper lemmas added (private)

All inside `namespace InducedOrbitToy` after the existing definitions.

1. `embO0_X0_eq_X0Lift` (line 113): `embO0 S S.X0 = X0Lift S` — proved by
   `LinearMap.ext (fun _ => rfl)`.  This is the key identification that
   places `X0Lift` inside `O0PlusU`.
2. `X0_mem_O0` (line 119): `S.X0 ∈ O0 S`, witnessed by the identity
   isometry on `S.V0`.  Uses `isUnit_one`, `Ring.inverse_one (M₀ := …)`.
3. `XCB_apply` (line 128): pointwise formula
   `XCB S C B (e, v, e') = (Cdual S C v + B e', S.X0 v + C e', 0)`.
   Required an explicit `show` of the unfolded `let`-bound XCB body
   followed by `ext <;> simp` — `rfl` alone failed because of the `let`
   bindings inside `XCB` and the implicit `add_zero`/`zero_add` on the
   product summands.
4. `X0Lift_apply` (line 154): pointwise formula
   `X0Lift S (e, v, e') = (0, S.X0 v, 0)` — `rfl` after `show`.
5. `XCB_sub_X0Lift_mem_unipotent` (line 166):
   `XCB S C B - X0Lift S ∈ UnipotentRadical S` for any `(C, B)`,
   *without* the skewness hypothesis on `B` (the autoformalize
   `parametrizeX0PlusU_mem` requires `IsSkewB`, but for the unipotent
   radical membership claim that hypothesis is logically unnecessary —
   the block-matrix structure does the work).  Three sub-goals
   correspond to the three clauses of `UnipotentRadical`:
   sends `flagE` to `0`, sends `flagEV0` into `flagE`, and sends `V`
   into `flagEV0`.  Each sub-goal is discharged by case-splitting on
   the `Submodule.prod` membership hypothesis, using
   `Submodule.mem_prod`/`Submodule.mem_bot`, then `LinearMap.sub_apply`
   together with the apply-formulas above.
6. `XST_sub_X0Lift_mem_unipotent` (line 196): trivial corollary of (5)
   with `(C, B) := (CST S Sₕ, BST S T)`.
7. `XST_mem_O0PlusU` (line 204): `XST S Sₕ T ∈ O0PlusU S`, witnessed by
   `(S.X0, XST - X0Lift)` with `embO0 S S.X0 = X0Lift S` plugged in via
   helper (1).

## Theorem-by-theorem

### `inducedOrbits` (line 218) — **RESOLVED**

#### Attempt 1
- **Approach:** Translate `GOrbit S (XST) ⊆ IndPG S` (where `IndPG` is a
  topological closure) into the trivial `subset_closure` containment.
  Take an arbitrary `y = g ∘ₗ XST ∘ₗ g⁻¹ ∈ GOrbit`.  Its membership in
  `IndPG = closure {g · z · g⁻¹ | g ∈ G, z ∈ O0PlusU}` follows from
  `subset_closure` applied to the witness `(g, hg, XST, XST_mem_O0PlusU, hyeq)`.
- **Result:** RESOLVED.
- **Key insight:** The slice membership `XST ∈ O0PlusU` reduces to
  `embO0 S S.X0 = X0Lift S` (helper 1) plus `XST - X0Lift ∈ 𝔲`
  (helper 5).  The `T ∈ S.Tset_circ` hypothesis is not used in this
  containment direction.

### `sIndependenceAndOrbitCriterion` (line 242) — **IN PROGRESS** (2 scoped sorries)

The theorem statement is an `iff` between (a) equality of two `G`-orbits
and (b) bilinear isometry of the residual forms `BT T₁` and `BT T₂`.

#### Attempt 1 — forward direction
- **Approach:** Extract `g ∈ G` with `g ∘ₗ XST T₁ = XST T₂ ∘ₗ g` from
  the orbit-equality hypothesis (`XST T₂ ∈ GOrbit (XST T₁)`).  Show that
  `g` preserves the slice `X₀ + 𝔲`, hence is a `P`-element.  Conclude
  via `pNormalForm_residual_orbit_iso`.
- **Result:** IN PROGRESS — scoped `sorry` left at the slice-stability
  step.
- **Blocker:** `pNormalForm_residual_orbit_iso` requires
  `S.formV0.Nondegenerate` and `(2 : F) ≠ 0`.  These are *not* in the
  current `sIndependenceAndOrbitCriterion` hypothesis list (the
  blueprint statement has them; the autoformalized statement does not).
  Adding the hypotheses changes the public statement, which the prover
  prompt forbids.
- **Next step:** Plan agent should (a) add the missing hypotheses to
  the public statement, or (b) thread them through the
  `[ClassifyBilinearForms F]` typeclass enrichment that the
  `LocalForms.lean` prover is working on.

#### Attempt 2 — reverse direction
- **Approach:** From a bilinear isometry, invoke
  `pNormalForm_residual_orbit_iso` to obtain a `P`-element `p` with
  `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p`.  Argue `p ∈ G` (parabolic ⊂ isometry
  group); use `p` and its inverse to mutually contain the two orbits.
- **Result:** IN PROGRESS — scoped `sorry` left.
- **Blocker:** Same as Attempt 1 (`Nondegenerate`, `(2 : F) ≠ 0`),
  *plus* the autoformalized `IsParabolicElement` uses
  `LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p` (i.e.
  "p is self-adjoint w.r.t. the ambient form") rather than
  `LinearMap.IsOrthogonal S.ambientForm p` ("p preserves the ambient
  form").  These are inequivalent: an invertible self-adjoint operator
  is not an isometry unless it satisfies `p² = 1`.  Concretely
  `IsParabolicElement S p` does **not** imply `IsometryEnd S p`.
- **Dead end:** trying to extract `IsometryEnd` from `IsParabolicElement`
  via `LinearEquiv.isAdjointPair_symm_iff` fails because that lemma
  needs `IsAdjointPair B B p p⁻¹` (not `p p`).
- **Next step:** Either (i) tighten `IsParabolicElement` to use
  `IsOrthogonal`, or (ii) restate the conclusion of
  `pNormalForm_residual_orbit_iso` to deliver an `IsometryEnd` element
  directly.  Both are upstream changes.

### `main` (line 302) — **RESOLVED** (modulo `sIndependenceAndOrbitCriterion`)

#### Attempt 1
- **Approach:** Direct decomposition into the four conjuncts.
  - (1) `XST - X0Lift ∈ 𝔲`: `XST_sub_X0Lift_mem_unipotent`.
  - (2) `GOrbit ⊆ IndPG`: `inducedOrbits`.
  - (3) Orbit independence + isometry criterion: forward to
    `sIndependenceAndOrbitCriterion S Sₕ Sₕ T₁ T₂ hT₁ hT₂`.
  - (4) Multiplicity = 1: `multiplicityNonDeg`.
- **Result:** RESOLVED — body contains no literal `sorry`.  Full
  closure depends on closing `sIndependenceAndOrbitCriterion`.

### `multiplicityNonDeg`, `multiplicityOddCase`

Already proved (untouched in this round) — both are direct corollaries
of the abstract `MultiplicityTheory` typeclass (consistent with the
Round-1.5 review note).

## Mathlib lemmas leveraged

- `subset_closure` — `IndPG` containment.
- `LinearMap.ext` — for `embO0 S S.X0 = X0Lift S`.
- `Ring.inverse_one (M₀ := Module.End F S.V0)` — to compute
  `Ring.inverse 1`.
- `isUnit_one` — `IsUnit (LinearMap.id : Module.End F V)` via
  `(1 : Module.End F V) = LinearMap.id`.
- `LinearMap.sub_apply`, `Submodule.mem_prod`, `Submodule.mem_bot` —
  unipotent-radical case work.
- `LinearMap.IsOrthogonal` (definition only — used trivially with
  `LinearMap.id`).

## Negative search results

- No Mathlib lemma directly bridges `IsAdjointPair B B p p`
  (autoformalize's parabolic-element definition) to
  `IsOrthogonal B p` (isometry).  The closest, `LinearEquiv.isAdjointPair_symm_iff`,
  requires `IsAdjointPair B B p p⁻¹` which differs.

## Hand-off to plan agent

1. The two outstanding scoped sorries inside
   `sIndependenceAndOrbitCriterion` are *not* matters of "trying harder";
   they require either tightening the autoformalized definitions
   (`IsParabolicElement` → `IsOrthogonal`-based) or strengthening the
   theorem statement (add `Nondegenerate` + `(2 : F) ≠ 0`).
2. The `XCB_sub_X0Lift_mem_unipotent` helper is strictly stronger than
   `parametrizeX0PlusU_mem` from `Slice.lean` (it does not require
   `IsSkewB`).  Once the Slice prover lands, that helper may be removed
   in favour of the public lemma — but only after threading
   `IsSkewB (BST S T)` from `IsSkewT S T`, which currently does **not**
   follow from the autoformalize definitions because `IsSkewT` is
   vacuous (both summands of `IsSkewT` already vanish by
   `L0_isotropic`).  Flagged for plan agent.

## Verification

```
$ lake env lean InducedOrbitToy/Orbits.lean
InducedOrbitToy/Orbits.lean:242:8: warning: declaration uses `sorry`
```

The file is also confirmed to typecheck via `lean_run_code` against
cached oleans — both `InducedOrbitToy.inducedOrbits` and
`InducedOrbitToy.main` accept their full hypothesis lists and return
the expected types.

`#print axioms InducedOrbitToy.inducedOrbits` was attempted; the
diagnostic-only LSP path does not surface `#print` output, so the axiom
audit is left to the review agent / plan agent against the next clean
build.  No `axiom` declarations were introduced in `Orbits.lean`.
