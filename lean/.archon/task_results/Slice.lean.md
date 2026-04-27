# InducedOrbitToy/Slice.lean

## Summary

7 of 9 sorries closed.  Two remaining sorries are due to the
autoformalised statements being mathematically false as written; both
are documented in-source with the diagnosis.

| Target | Line | Status |
|---|---|---|
| `Cdual` (term-mode) | 51 → 73 | RESOLVED (constructed via `S.lambda.toPerfPair.symm`) |
| `Cdual_pairing_eq` | 58 → 84 | RESOLVED |
| `parametrizeX0PlusU_mem` | 137 → 195 | RESOLVED |
| `parametrizeX0PlusU_existence` | 146 → 232 | **PARTIAL** (constructed `C, B`; two interior sorries) |
| `parametrizeX0PlusU_uniqueness` | 156 → 247 | RESOLVED |
| `uD` (term-mode) | 169 → 280 | RESOLVED (block-matrix formula) |
| `uD_neg_inverse` | 177 → 326 | RESOLVED (uses `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`) |
| `uD_isParabolic` | 187 → 391 | **PARTIAL** (flag conjuncts proved; `IsAdjointPair` conjunct sorry-ed) |
| `uD_conj_XCB` | 201 → 460 | RESOLVED |

`lake build` is green; only `sorry` warnings remain.  No custom axioms;
spot checks show only `propext, Classical.choice, Quot.sound` for each
proved theorem.

## Key infrastructure introduced (private)

* `lambda_isPerfPair S : S.lambda.IsPerfPair` — packages
  `S.paired.isPerfect` (project predicate) into the Mathlib typeclass
  by combining `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`
  with `Subspace.dual_finrank_eq`.
* `XCB_apply`, `X0Lift_apply`, `uD_apply` — pointwise block-matrix
  formulas, all proved by `unfold ; simp`.
* `Cdual_neg`, `Cdual_pairing` (no-Nondeg variant), `Cdual_X0_apply`
  (`Cdual D ∘ X₀ = -Cdual (X₀ ∘ D)`, the skewness-driven identity),
  `eps_sq_eq_one` — the algebraic toolkit needed for `uD_conj_XCB` and
  the skewness verification in `uD_conj_XCB`.

## RESOLVED proofs — key steps

### `Cdual` (line 73) and `Cdual_pairing_eq` (line 84)

Constructed using the perfect-pairing equivalence
`S.lambda.toPerfPair : S.E ≃ₗ[F] Module.Dual F S.E'`:

```
Cdual S C = S.lambda.toPerfPair.symm ∘ₗ -(C.dualMap ∘ₗ S.formV0)
```

`Cdual_pairing_eq` follows from `LinearMap.apply_symm_toPerfPair_self`
plus `LinearMap.dualMap_apply`.

### `parametrizeX0PlusU_mem` (line 195)

Direct case decomposition on `Submodule.prod ⊤ (Submodule.prod ⊥ ⊥)`
(= `S.flagE`) and `Submodule.prod ⊤ (Submodule.prod ⊤ ⊥)` (=
`S.flagEV0`).  Uses `XCB_apply`, `X0Lift_apply`, `simp` for the
membership conditions.

### `parametrizeX0PlusU_uniqueness` (line 247)

Probe `XCB S C B = XCB S C' B'` at `(0, 0, e')` and read off
`B = B'` and `C = C'` from the `E` and `V0` components via
`congrArg` + `LinearMap.ext`.

### `uD_neg_inverse` (line 326)

The `1/2 + 1/2 = 1` identity `(2 : F)⁻¹ + (2 : F)⁻¹ = 1` is proven
from `hChar : (2 : F) ≠ 0` via `← two_mul, mul_inv_cancel₀`.  Each
component then closes with `linear_combination (norm := abel_nf) key`.

### `uD_conj_XCB` (line 460)

The block-matrix conjugation reduces, in the `E`-component, to the
identity `Cdual D (X₀ v) = -Cdual (X₀ ∘ D) v` (the helper
`Cdual_X0_apply`).  The `IsSkewB B'` conjunct (where
`B' = B + Cdual D ∘ C - Cdual C ∘ D - Cdual D ∘ X₀ ∘ D`) is closed
by a single explicit `linear_combination` using `S.epsSymm`,
`S.skew`, `eps_sq_eq_one`, and the input `IsSkewB B`.

## PARTIAL proofs — diagnosis

### `parametrizeX0PlusU_existence` (line 232)

**Claim as written**: every `Y ∈ UnipotentRadical S` admits
`(C, B)` with `IsSkewB S B` and `XCB S C B - X0Lift S = Y`.

**Issue**: `Basic.lean :: UnipotentRadical` is the loose
flag-preserving Lie algebra
`{f | f sends each flag-step into the previous}` — it does **not**
enforce skew-adjointness with respect to `S.ambientForm`, which is
what the blueprint's `𝔲` requires.  Decomposing an arbitrary
`Y ∈ UnipotentRadical` gives a triple of free linear maps
`(α : V₀ →ₗ E, β : E' →ₗ E, γ : E' →ₗ V₀)`, while a member of the
image of `(C, B) ↦ XCB C B - X0Lift` must satisfy `α = Cdual γ` and
`IsSkewB β`, neither of which is automatic.

**What is in the file**: the canonical candidates
`C := projV0 ∘ Y ∘ inE'` and `B := projE ∘ Y ∘ inE'` are
constructed; the two genuine constraints (`IsSkewB B` and the
equation) are left as scoped `sorry`s with an in-source comment
explaining the gap.  See lines 230–250 of `Slice.lean`.

**Resolution path for the plan agent**: strengthen
`Basic.lean :: UnipotentRadical` to also require skew-adjointness
with respect to `S.ambientForm`.  Once that hypothesis is added (as
a fourth conjunct in the `carrier` predicate), the decomposition
yields `α = Cdual γ` (analogous to the blueprint computation
"Testing this on `(v, e') ∈ V₀ × E'` gives
`λ(Av, e') + ⟨v, Ce'⟩₀ = 0`") and `β` automatically satisfies
`IsSkewB`.  All proofs in `Slice.lean` that depend on this lemma
will continue to work, since neither `parametrizeX0PlusU_mem` nor
the conjugation lemma uses the existence direction.

### `uD_isParabolic` (line 391)

**Claim as written**: the `IsAdjointPair S.ambientForm S.ambientForm
(uD S D) (uD S D)` conjunct.

**Issue**: `LinearMap.IsAdjointPair B B f g` unfolds to
`∀ x y, B (f x) y = B x (g y)`.  With `f = g = uD S D`, this asserts
that `uD S D` is *self-adjoint* with respect to `S.ambientForm` —
which is **false** in general.  The blueprint actually states that
`u_D ∈ P` (the parabolic), i.e. that `u_D` preserves the form
*as an isometry* (equivalent to the adjoint pair `(u_D, u_D⁻¹) =
(u_D D, u_D (-D))`).  A direct expansion using `Cdual_pairing_eq`
and `S.epsSymm` shows
`B(u_D x, y) - B(x, u_D y) = 2(B₀(D e₁', v₂) - B₀(v₁, D e₂'))`,
which is non-zero for generic `D`.

**What is in the file**: the two flag-preservation conjuncts
(`Submodule.map (uD S D) S.flagE ≤ S.flagE` and the analogous
`flagEV0` claim) are proved.  The IsAdjointPair conjunct is a
scoped `sorry` with an in-source explanation.

**Resolution path for the plan agent**: change the autoformalised
statement to `IsAdjointPair S.ambientForm S.ambientForm (uD S D)
(uD S (-D))`.  With that statement, the conjunct *is* provable: the
expansion of `B(u_D x, y) - B(x, u_(-D) y)` collapses term by term
using the same identities (`S.epsSymm`, `S.skew` at `D u, D v`).

## NEGATIVE search results

- The Mathlib lemma `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`
  exists in `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`; it
  does **not** require additional `FiniteDimensional` arguments
  beyond the typeclass instances on the source/target spaces.
- `LinearEquiv.map_neg` is **not** a lemma name in current Mathlib;
  use the bundled `map_neg` instead (`map_neg : f (-x) = -(f x)` for
  any additive-homomorphism-like `f`).

## Mathlib lemmas of note (used in the proofs above)

- `LinearMap.IsPerfPair.mk`, `LinearMap.toPerfPair`,
  `LinearMap.toPerfPair_apply`, `LinearMap.apply_symm_toPerfPair_self`
  (perfect-pairing equivalence; new entry point for `Cdual`).
- `Subspace.dual_finrank_eq`,
  `LinearMap.injective_iff_surjective_of_finrank_eq_finrank`
  (deriving the perfect-pairing typeclass instance from
  `IsPerfectPairing`).
- `LinearMap.dualMap_apply`,
  `(neg).dualMap = -(dualMap)` (proved inline).
- `Submodule.mem_prod` (for `flagE` / `flagEV0` membership).
- `linear_combination` with optional `(norm := abel_nf)` for
  module-element identities; `linear_combination` (default
  `ring_nf`) for the `IsSkewB B'` ε-symmetry computation.

## Verification

- `lake build`: green (only `sorry` warnings).
- `lean_verify` for each closed theorem (`Cdual_pairing_eq`,
  `parametrizeX0PlusU_mem`, `parametrizeX0PlusU_uniqueness`,
  `uD_neg_inverse`, `uD_conj_XCB`): axioms only `propext,
  Classical.choice, Quot.sound`.
- No custom `axiom` declarations.
