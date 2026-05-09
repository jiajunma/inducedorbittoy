import ClassicalGroup.Lemmas

/-!
# Existence theorem statements for the ClassicalGroup task

This file states the existence package and the case-by-case standard-model
existence theorems required by `classicalgroup.md`.  Standard model
constructions will be implemented in the model files later.
-/

namespace ClassicalGroup

universe u

/-- Existence package for a raw signature `(star,p,q)`.

It says there is some finite-dimensional complex vector space, a formed-space
structure, and form-preserving `J` and `L` satisfying `IsClassicalSpace`. -/
def HasClassicalSpace (star : ClassicalStar) (p q : ℕ) : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : Module.Finite ℂ V),
    ∃ (_ : FormedSpace star.eps V),
      ∃ (J : JStructure star.eps V star.jSign)
        (L : LStructure star.eps V star.dotEps),
        IsClassicalSpace star p q V J L

/-- Packed-signature version of `HasClassicalSpace`. -/
def HasClassicalSpaceFor (s : ClassicalSignature) : Prop :=
  HasClassicalSpace.{u} s.star s.p s.q

/-- Case `B`: existence from the explicit `S_{p,q}` model. -/
theorem exists_B_model (p q : ℕ) (hOdd : Odd (p + q)) :
    HasClassicalSpace.{u} ClassicalStar.B p q := by
  /-
  Blueprint model: `V = ℂ^(p+q)`, `B(u,v)=uᵀ S_{p,q} v`, `J=conjugation`,
  and `L=S_{p,q}`.  Direct matrix calculations prove all fields.
  -/
  sorry

/-- Case `D`: existence from the same explicit `S_{p,q}` model. -/
theorem exists_D_model (p q : ℕ) (hEven : Even (p + q)) :
    HasClassicalSpace.{u} ClassicalStar.D p q := by
  /-
  Same construction as the `B` case; only the signature parity condition differs.
  -/
  sorry

/-- Case `C`: existence from the real symplectic model. -/
theorem exists_C_model (r : ℕ) :
    HasClassicalSpace.{u} ClassicalStar.C r r := by
  /-
  Blueprint model: `V = ℂ^r ⊕ ℂ^r`, `B((z,w),(z',w')) = zᵀw' - wᵀz'`,
  `J=conjugation`, and `L(z,w)=(w,-z)`.
  -/
  sorry

/-- Case `Ctilda`: same linear data as the `C` model. -/
theorem exists_Ctilda_model (r : ℕ) :
    HasClassicalSpace.{u} ClassicalStar.Ctilda r r := by
  /-
  The metaplectic cover is external; the underlying `J,L` data are the same as
  in the `C` model.
  -/
  sorry

/-- Case `C*`: existence with `p=2a`, `q=2b`. -/
theorem exists_Cstar_model (a b : ℕ) :
    HasClassicalSpace.{u} ClassicalStar.Cstar (2 * a) (2 * b) := by
  /-
  Blueprint model: `V = ℂ^(a+b) ⊕ ℂ^(a+b)`, alternating form with matrix
  `S_{a,b}`, `J(z,w)=(-conj w, conj z)`, and `L(z,w)=(S z, S w)`.
  -/
  sorry

/-- Case `D*`: existence with `p=q=r`. -/
theorem exists_Dstar_model (r : ℕ) :
    HasClassicalSpace.{u} ClassicalStar.Dstar r r := by
  /-
  Blueprint model: `V = ℂ^r ⊕ ℂ^r`,
  `B((z,w),(z',w')) = -i(zᵀw' + wᵀz')`,
  `J(z,w)=(-conj w,conj z)`, and `L(z,w)=(i z,-i w)`.
  -/
  sorry

/-- Existence obtained by dispatching to the four blueprint model cases. -/
theorem exists_classical_space_by_cases (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    HasClassicalSpace.{u} star p q := by
  /-
  Case split on `star`.  In the `C*` case use the evenness hypotheses to write
  `p=2a`, `q=2b`, then call `exists_Cstar_model`.
  -/
  sorry

/-- Main existence theorem, raw interface. -/
theorem exists_classical_space (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    HasClassicalSpace.{u} star p q := by
  exact exists_classical_space_by_cases star p q hsig

/-- Main existence theorem, packed-signature interface. -/
theorem exists_classical_space_for (s : ClassicalSignature) :
    HasClassicalSpaceFor.{u} s := by
  exact exists_classical_space.{u} s.star s.p s.q s.isClassical

end ClassicalGroup
