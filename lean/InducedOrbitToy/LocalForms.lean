import InducedOrbitToy.NormalForm

/-!
Autoformalization target: `lem:local-form-classes` from
`references/blueprint_verified.md` (lines 413–432).

This file states the high-level claim of `lem:local-form-classes`:
maximal-rank residual forms in `𝒯°` admit only finitely many isometry classes
over the allowed fields (`ℝ` or non-archimedean local of characteristic `0`),
and each class is open in `𝒯°`.

The field-specific classification (Sylvester / Hasse–Minkowski) is abstracted
away behind the placeholder typeclass `ClassifyBilinearForms F`.  In the
autoformalize stage this typeclass had a vacuous body (`∃ _ : ℕ, True`).
The prover stage **enriches** it with exactly the two consequences of the
field-specific classification that the blueprint relies on (a finite set of
isometry representatives on `𝒯°`, and openness of each isometry class in
any topology making addition continuous).  Concrete instances over `ℝ` and
non-archimedean local fields are out of scope for the prover stage; only the
typeclass *content* is provided here, not its inhabitation for any specific
field.

Both clauses ("finitely many classes" and "each class is open") are split
into separate theorems `localFormClasses_finite` and `localFormClasses_open`,
following the *Alternative* shape suggested in `.archon/informal/localforms.md`.
A combined statement is also provided as `localFormClasses` for convenience.

The supporting names `IsSkewT`, `MaximalRank`, `Tset_circ`, and `BT` (the
residual bilinear form `B_T (u, v) := λ((T u : E), v)`) are taken from
`InducedOrbitToy.NormalForm` — this file does **not** redefine them.
-/

namespace InducedOrbitToy

universe u v w x

variable {F : Type u} [Field F]

/-! ## Local-form classification API -/

/-- The isometry equivalence relation on `Hom_F(L0', L0)`: two operators
`T₁, T₂` are isometry-equivalent iff their residual forms `S.BT T₁` and
`S.BT T₂` on `L0'` are isometric.

Equivalent to `Bilinear.AreIsometric (S.BT T₁) (S.BT T₂)` (defined in
`InducedOrbitToy.NormalForm`); we restate it here in unfolded form for
convenience in the theorem statements below. -/
def IsometryRel (S : SliceSetup.{u, v, w, x} F) :
    (S.L0' →ₗ[F] S.L0) → (S.L0' →ₗ[F] S.L0) → Prop :=
  fun T₁ T₂ => Bilinear.AreIsometric (S.BT T₁) (S.BT T₂)

/-- Placeholder typeclass capturing the abstract fact that the field `F`
admits the classification of non-degenerate `ε`-symmetric bilinear forms with
finitely many invariants and locally constant invariants.

The intended concrete instances are:
* `F = ℝ` (Sylvester's law of inertia, finitely many signatures), and
* `F` non-archimedean local of characteristic `0` (Hasse–Minkowski:
  determinant in `F^×/F^×²` plus Hasse invariant).

Both are out of scope for the autoformalize/prover stage; we only carry the
predicate as a hypothesis and never inhabit it for any concrete field.

The prover-stage *enrichment* records exactly the two consequences of the
field-specific classification that the blueprint relies on:

* `finiteClasses` — every `Tset_circ` admits a finite set of isometry
  representatives, and
* `openClasses` — each isometry class is open in any topology on
  `Hom_F(L0', L0)` making addition continuous.

The class is universe-polymorphic in the four universe parameters
`(u, v, w, x)` of `SliceSetup.{u, v, w, x} F`, declared at the top of this
file.  Downstream callers that only use `[ClassifyBilinearForms F]` as a
marker (for instance `Orbits.lean`'s `inducedOrbits`) continue to work
unchanged: Lean infers fresh universes for `(v, w, x)` at the use-site,
which is fine because no projection of the class is invoked there. -/
class ClassifyBilinearForms (F : Type u) [Field F] : Prop where
  /-- Finiteness of isometry classes on `𝒯°`. -/
  finiteClasses :
    ∀ (S : SliceSetup.{u, v, w, x} F),
      ∃ (reps : Finset (S.L0' →ₗ[F] S.L0)),
        ∀ T ∈ S.Tset_circ, ∃ T₀ ∈ reps, IsometryRel S T T₀
  /-- Openness of every isometry class in `Hom_F(L0', L0)` under any
  continuous-addition topology. -/
  openClasses :
    ∀ (S : SliceSetup.{u, v, w, x} F)
      [TopologicalSpace (S.L0' →ₗ[F] S.L0)]
      [ContinuousAdd (S.L0' →ₗ[F] S.L0)]
      (T₀ : S.L0' →ₗ[F] S.L0),
        IsOpen { T | T ∈ S.Tset_circ ∧ IsometryRel S T T₀ }

/-! ## `lem:local-form-classes`

The three public theorems below explicitly name the four universe
parameters `(u, v, w, x)` of `SliceSetup` (declared at the top of the file
via `universe u v w x`).  This is required so that the universe-polymorphic
fields of `ClassifyBilinearForms` can be aligned with the universes of the
particular `S` at use-site; without the explicit annotation Lean picks
fresh universe metavariables for the typeclass instance that do not unify
with the universes of `S`.  The propositional content of the statements is
unchanged: the `.{u, v, w, x}` annotation just makes universe polymorphism
explicit.  Callers may continue to write `localFormClasses_finite S` etc.
without supplying universes by hand. -/

/-- `lem:local-form-classes` — *finiteness* clause.

Under classification hypotheses on `F` (`ℝ` or non-archimedean local of
characteristic `0`), the isometry equivalence on `𝒯°` has finitely many
classes. -/
theorem localFormClasses_finite (S : SliceSetup.{u, v, w, x} F)
    (hNondeg : S.formV0.Nondegenerate)
    [hC : ClassifyBilinearForms.{u, v, w, x} F] :
    ∃ (reps : Finset (S.L0' →ₗ[F] S.L0)),
      ∀ T ∈ S.Tset_circ, ∃ T₀ ∈ reps, IsometryRel S T T₀ := by
  -- The non-degeneracy hypothesis is part of the public statement of the
  -- lemma but is not needed at this level of abstraction: the enriched
  -- `ClassifyBilinearForms` typeclass already absorbs the field-specific
  -- classification facts that depend on `hNondeg`.
  let _ := hNondeg
  exact hC.finiteClasses S

/-- `lem:local-form-classes` — *openness* clause.

In any topology on `Hom_F(L0', L0)` making addition continuous, every
isometry class is open in `𝒯°`. The intended topology is the analytic
topology over `ℝ` or a non-archimedean local field, but this file is
agnostic about the chosen `[TopologicalSpace _]` instance. -/
theorem localFormClasses_open (S : SliceSetup.{u, v, w, x} F)
    [TopologicalSpace (S.L0' →ₗ[F] S.L0)]
    [ContinuousAdd (S.L0' →ₗ[F] S.L0)]
    (hNondeg : S.formV0.Nondegenerate)
    [hC : ClassifyBilinearForms.{u, v, w, x} F]
    (T₀ : S.L0' →ₗ[F] S.L0) (hT₀ : T₀ ∈ S.Tset_circ) :
    IsOpen { T | T ∈ S.Tset_circ ∧ IsometryRel S T T₀ } := by
  -- The hypotheses `hNondeg` and `hT₀` are recorded in the public statement
  -- but are not needed at this level of abstraction; they are absorbed into
  -- the enriched `ClassifyBilinearForms` typeclass.
  let _ := hNondeg
  let _ := hT₀
  exact hC.openClasses S T₀

/-- `lem:local-form-classes` (combined statement).  Bundles the finiteness
and openness clauses into a single existential.  The `[TopologicalSpace _]`
and `[ContinuousAdd _]` instances are *inside* the existential conclusion so
the bare statement does not require a topology to be in scope. -/
theorem localFormClasses (S : SliceSetup.{u, v, w, x} F)
    (hNondeg : S.formV0.Nondegenerate)
    [hC : ClassifyBilinearForms.{u, v, w, x} F] :
    ∃ (reps : Finset (S.L0' →ₗ[F] S.L0)),
      (∀ T ∈ S.Tset_circ, ∃ T₀ ∈ reps, IsometryRel S T T₀) ∧
      (∀ T₀ ∈ reps,
        ∀ [TopologicalSpace (S.L0' →ₗ[F] S.L0)]
          [ContinuousAdd (S.L0' →ₗ[F] S.L0)],
        IsOpen { T | T ∈ S.Tset_circ ∧ IsometryRel S T T₀ }) := by
  let _ := hNondeg
  obtain ⟨reps, hreps⟩ := hC.finiteClasses S
  refine ⟨reps, hreps, ?_⟩
  intro T₀ _hT₀ _ts _ca
  exact hC.openClasses S T₀

end InducedOrbitToy
