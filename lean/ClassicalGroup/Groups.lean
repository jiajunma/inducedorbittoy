import ClassicalGroup.Uniqueness

/-!
# Group-identification statement layer for the ClassicalGroup task

The theorem in `classicalgroup.md` also identifies the centralizer of `J` in the
complex isometry group with the expected real classical group.  This file keeps
that assertion separate from the core existence/uniqueness theorem so that the
choice of real Lie group API does not block the linear-algebra formalization.
-/

namespace ClassicalGroup

universe u

/-- A complex-linear isometry of a formed complex vector space. -/
structure ComplexFormIsometry (eps : Sign)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] where
  /-- The underlying complex-linear automorphism. -/
  toLinearEquiv : V ≃ₗ[ℂ] V
  /-- Preservation of the formed-space bilinear form. -/
  preserves_form :
    ∀ u v : V, FormedSpace.B eps V (toLinearEquiv u) (toLinearEquiv v) =
      FormedSpace.B eps V u v

namespace ComplexFormIsometry

variable {eps : Sign} {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V]

/-- Use a complex form isometry as a function. -/
instance : CoeFun (ComplexFormIsometry eps V) (fun _ => V → V) where
  coe g := g.toLinearEquiv

@[simp] theorem coe_apply (g : ComplexFormIsometry eps V) (v : V) :
    g v = g.toLinearEquiv v := rfl

end ComplexFormIsometry

/-- The predicate that a complex form isometry commutes with `J`. -/
def CommutesWithJ {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (g : ComplexFormIsometry eps V) : Prop :=
  ∀ v : V, g (J v) = J (g v)

/-- The centralizer of `J` inside the complex isometry group, as a type of
isometries satisfying the commuting predicate. -/
def ComplexFormIsometryCentralizerJ {eps : Sign}
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) : Type u :=
  { g : ComplexFormIsometry eps V // CommutesWithJ J g }

/-- Labels for the expected real classical groups in the statement. -/
inductive ExpectedRealGroupKind where
  | orthogonal_pq
  | real_symplectic
  | quaternionic_unitary
  | quaternionic_skew_unitary
  deriving DecidableEq, Repr

/-- The expected real-group label attached to a family. -/
def expectedRealGroupKind : ClassicalStar → ExpectedRealGroupKind
  | .B => .orthogonal_pq
  | .D => .orthogonal_pq
  | .C => .real_symplectic
  | .Ctilda => .real_symplectic
  | .Cstar => .quaternionic_unitary
  | .Dstar => .quaternionic_skew_unitary

/-- Abstract placeholder for the eventual Mathlib/native real Lie group target.

This records the intended target kind without committing yet to a concrete API
for `O(p,q)`, `Sp(2p,ℝ)`, `Sp(a,b)`, or `O*(2p)`.  Later, this structure should
be replaced by or connected to concrete group definitions. -/
structure AbstractExpectedRealGroup (star : ClassicalStar) (p q : ℕ) where
  carrier : Type u
  group : Group carrier
  kind : ExpectedRealGroupKind
  kind_eq : kind = expectedRealGroupKind star

/-- Abstract group-identification statement for property (10) of
`classicalgroup.md`.

This is intentionally isolated.  The core construction can be proved first;
then this predicate can be strengthened by replacing `AbstractExpectedRealGroup`
with concrete real Lie groups. -/
def HasExpectedGroupIdentification (star : ClassicalStar) (p q : ℕ)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    (J : JStructure star.eps V star.jSign) : Prop :=
  ∃ G : AbstractExpectedRealGroup.{u} star p q,
    Nonempty (ComplexFormIsometryCentralizerJ V J ≃ G.carrier)

/-- Group-identification theorem statement for a supplied classical space. -/
theorem group_identification_of_classical_space (star : ClassicalStar) (p q : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    (J : JStructure star.eps V star.jSign)
    (L : LStructure star.eps V star.dotEps)
    (h : IsClassicalSpace star p q V J L) :
    HasExpectedGroupIdentification star p q V J := by
  /-
  Blueprint proof: compute the centralizer of `J` in each standard model.
  * `B,D`: real matrices preserving `S_{p,q}`, giving full `O(p,q)`.
  * `C,Ctilda`: real matrices preserving the standard symplectic form,
    giving `Sp(2p,ℝ)`; the metaplectic cover is external.
  * `C*`: maps commuting with `J` are quaternionic-linear and preserve the
    quaternionic Hermitian form of signature `(p/2,q/2)`, giving `Sp(p/2,q/2)`.
  * `D*`: the same construction gives the quaternionic skew-Hermitian group
    `O*(2p)`.
  -/
  sorry

/-- Existence package strengthened by the abstract group-identification layer. -/
def HasClassicalSpaceWithGroupIdentification (star : ClassicalStar) (p q : ℕ) : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V),
    ∃ (_ : FormedSpace star.eps V),
      ∃ (J : JStructure star.eps V star.jSign)
        (L : LStructure star.eps V star.dotEps),
        IsClassicalSpace star p q V J L ∧ HasExpectedGroupIdentification star p q V J

/-- Existence plus group-identification theorem statement. -/
theorem exists_classical_space_with_group_identification (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    HasClassicalSpaceWithGroupIdentification.{u} star p q := by
  /-
  Use `exists_classical_space` to get a classical space and then apply
  `group_identification_of_classical_space` to that witness.
  -/
  sorry

end ClassicalGroup
