import ClassicalGroup.Existence

/-!
# Uniqueness theorem statements for the ClassicalGroup task

Uniqueness is formalized as existence of a complex-linear isomorphism preserving
the form and intertwining both `J` and `L`, not as equality of structures.
-/

namespace ClassicalGroup

universe u

/-- Pairwise uniqueness for all classical spaces of a fixed raw signature. -/
def UniqueClassicalSpacesFor (star : ClassicalStar) (p q : ℕ) : Prop :=
  ∀ (V W : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace star.eps W]
    (JV : JStructure star.eps V star.jSign)
    (LV : LStructure star.eps V star.dotEps)
    (JW : JStructure star.eps W star.jSign)
    (LW : LStructure star.eps W star.dotEps),
      IsClassicalSpace star p q V JV LV →
        IsClassicalSpace star p q W JW LW →
          Nonempty (ClassicalSpaceIso star V W JV LV JW LW)

/-- Pairwise uniqueness in the `B` case. -/
theorem unique_B_model (p q : ℕ) (hOdd : Odd (p + q)) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.B p q := by
  /-
  Blueprint proof: pass to the `J`-fixed real form, decompose into the real
  `L=+1` and `L=-1` eigenspaces, choose orthonormal bases for the positive and
  negative parts, and compare with the `S_{p,q}` model.
  -/
  sorry

/-- Pairwise uniqueness in the `D` case. -/
theorem unique_D_model (p q : ℕ) (hEven : Even (p + q)) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.D p q := by
  /-
  Same normal-form argument as the `B` case; only the parity condition differs.
  -/
  sorry

/-- Pairwise uniqueness in the `C` case. -/
theorem unique_C_model (r : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.C r r := by
  /-
  Blueprint proof: pass to the `J`-fixed real symplectic space with positive
  metric `H`; construct an adapted symplectic basis by Gram-Schmidt.
  -/
  sorry

/-- Pairwise uniqueness in the `Ctilda` case. -/
theorem unique_Ctilda_model (r : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.Ctilda r r := by
  /-
  Same linear normal form as in the `C` case.  The metaplectic cover is not part
  of the `J,L` data.
  -/
  sorry

/-- Pairwise uniqueness in the `C*` case with `p=2a`, `q=2b`. -/
theorem unique_Cstar_model (a b : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.Cstar (2 * a) (2 * b) := by
  /-
  Blueprint proof: use the quaternionic structure induced by `J²=-1`; the
  `L=±1` eigenspaces are quaternionic subspaces, and quaternionic orthonormal
  bases reduce the form to the standard `Sp(a,b)` model.
  -/
  sorry

/-- Pairwise uniqueness in the `D*` case. -/
theorem unique_Dstar_model (r : ℕ) :
    UniqueClassicalSpacesFor.{u} ClassicalStar.Dstar r r := by
  /-
  Blueprint proof: set `A=-iL`; choose an `H`-orthonormal basis of the `A=+1`
  eigenspace and pair it with its image under `J`.
  -/
  sorry

/-- Uniqueness obtained by dispatching to the blueprint cases. -/
theorem unique_classical_spaces_by_cases (star : ClassicalStar) (p q : ℕ)
    (hsig : IsClassicalSignature star p q) :
    UniqueClassicalSpacesFor.{u} star p q := by
  /-
  Case split on `star`.  In the `C*` case use evenness to write `p=2a`,
  `q=2b`, then call `unique_Cstar_model`.
  -/
  sorry

/-- Main uniqueness theorem, raw interface. -/
theorem classical_space_unique (star : ClassicalStar) (p q : ℕ)
    (V W : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace star.eps W]
    (JV : JStructure star.eps V star.jSign)
    (LV : LStructure star.eps V star.dotEps)
    (JW : JStructure star.eps W star.jSign)
    (LW : LStructure star.eps W star.dotEps)
    (hV : IsClassicalSpace star p q V JV LV)
    (hW : IsClassicalSpace star p q W JW LW) :
    Nonempty (ClassicalSpaceIso star V W JV LV JW LW) := by
  exact unique_classical_spaces_by_cases star p q (isClassicalSpace_signature hV)
    V W JV LV JW LW hV hW

/-- Main uniqueness theorem, packed-signature interface. -/
theorem classical_space_unique_for (s : ClassicalSignature)
    (V W : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace s.eps V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]
    [FormedSpace s.eps W]
    (JV : JStructure s.eps V s.jSign)
    (LV : LStructure s.eps V s.dotEps)
    (JW : JStructure s.eps W s.jSign)
    (LW : LStructure s.eps W s.dotEps)
    (hV : IsClassicalSpaceFor s V JV LV)
    (hW : IsClassicalSpaceFor s W JW LW) :
    Nonempty (ClassicalSpaceIsoFor s V W JV LV JW LW) := by
  exact classical_space_unique s.star s.p s.q V W JV LV JW LW hV hW

end ClassicalGroup
