# Informal content for `InducedOrbitToy/LocalForms.lean`

Blueprint section to formalize: `lem:local-form-classes` (lines 413–432) of
`references/blueprint_verified.md`.

## Setting

Imports `InducedOrbitToy.NormalForm`. Reuses `BT`, `IsSkewT`, `Tset`,
`Tset_circ` as defined there (or in `Basic.lean` if extracted earlier).

## Goal

The blueprint's claim is that the maximal-rank forms occurring in `𝒯°` have
**finitely many isometry classes**, and **each isometry class is open** in
`𝒯°` (in the analytic topology over `ℝ` or a non-archimedean local field).

This statement involves:

1. A topology on `𝒯° ⊆ Hom_F(L0', L0)`. For a generic `[Field F]`, no such
   topology is available in Mathlib. We therefore **abstract the topology
   away**: state the openness as `IsOpen` in some unspecified
   `[TopologicalSpace (S.L0' →ₗ[F] S.L0)]` instance. Take the topology as a
   hypothesis or inject it via `[t : TopologicalSpace _]`.
2. Field-specific classification (Sylvester, Hasse-Minkowski). Mathlib has
   partial support; in autoformalize we expose only the high-level claim
   "finitely many isometry classes" via a `Finite (𝒯° / isometry)` quotient
   abstraction.

## Suggested approach for autoformalize

Do **not** attempt to encode `ℝ` vs. non-archimedean locally compact `F`
classification yet. Instead, expose the result as one self-contained
theorem using **abstract hypotheses**:

```
namespace InducedOrbitToy

/-- Equivalence on `𝒯` recording isometry of the residual bilinear form
`B_T (u v) = λ(T u, v)` on `L0'`. -/
def IsometryRel (S : SliceSetup F) :
    (S.L0' →ₗ[F] S.L0) → (S.L0' →ₗ[F] S.L0) → Prop :=
  fun T₁ T₂ =>
    ∃ h : S.L0' ≃ₗ[F] S.L0',
      ∀ u v, BT S T₂ (h u) (h v) = BT S T₁ u v

/-- `lem:local-form-classes`: under classification hypotheses on `F` (`ℝ` or
non-archimedean local of char 0), the isometry-equivalence has finitely many
classes on `Tset_circ`, and each class is open in any topology making
addition continuous. -/
theorem localFormClasses (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (hClassify : ClassifyBilinearForms F) :
    -- finite set of representatives + each class open in 𝒯°
    ∃ (reps : Finset (S.L0' →ₗ[F] S.L0)),
      (∀ T, T ∈ Tset_circ S → ∃ T₀ ∈ reps, IsometryRel S T T₀) ∧
      (∀ T₀ ∈ reps, ∀ [TopologicalSpace (S.L0' →ₗ[F] S.L0)]
          [ContinuousAdd (S.L0' →ₗ[F] S.L0)],
        IsOpen { T ∈ Tset_circ S | IsometryRel S T T₀ }) := by
  sorry

end InducedOrbitToy
```

where `ClassifyBilinearForms F : Prop` is a **new abstract predicate**
defined in this file as a placeholder for "the field `F` admits the
classification of non-degenerate ε-symmetric bilinear forms with finitely
many invariants and locally constant invariants." Concrete instances are
out of scope for this round.

```
class ClassifyBilinearForms (F : Type*) [Field F] : Prop where
  finitelyManyClasses :
    ∀ (V : Type*) [AddCommGroup V] [Module F V] [Module.Finite F V],
      ∃ (n : ℕ), True  -- placeholder; refined later
```

(Use the most stripped-down predicate that compiles. The whole point of
this stage is to **block out the API surface** without committing to a
proof.)

## Alternative if the abstract topology is too painful

If the `[TopologicalSpace (S.L0' →ₗ[F] S.L0)]` typeclass requirement is
hard to thread through, drop the `IsOpen` clause and state only the
finitely-many-classes part:

```
theorem localFormClasses_finite (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (hClassify : ClassifyBilinearForms F) :
    ∃ (reps : Finset (S.L0' →ₗ[F] S.L0)),
      ∀ T ∈ Tset_circ S, ∃ T₀ ∈ reps, IsometryRel S T T₀ := by
  sorry
```

Plus a separate openness statement:

```
theorem localFormClasses_open
    [TopologicalSpace (S.L0' →ₗ[F] S.L0)]
    [ContinuousAdd (S.L0' →ₗ[F] S.L0)]
    (S : SliceSetup F)
    (T₀ : S.L0' →ₗ[F] S.L0) (hT₀ : T₀ ∈ Tset_circ S) :
    IsOpen { T ∈ Tset_circ S | IsometryRel S T T₀ } := by
  sorry
```

The autoformalize-stage prover may pick whichever shape compiles cleanly.

## What is NOT required for this round

- Proving any of the classification facts. Those depend on field-specific
  results that are out of scope.
- Implementing `ClassifyBilinearForms F` for any concrete field.
- Naming the analytic topology on `Hom(L0', L0)`.

## Acceptance

`lake env lean InducedOrbitToy/LocalForms.lean` succeeds with only `sorry`
warnings, no errors, no axioms.
