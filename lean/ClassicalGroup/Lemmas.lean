import ClassicalGroup.Basic

/-!
# Lemma statements for the ClassicalGroup task

This file records the reusable theorems that the construction and uniqueness
proofs need.  Some proofs are intentionally left as `sorry` at this skeleton
stage, but each nontrivial statement carries the blueprint argument as a source
comment.
-/

namespace ClassicalGroup

universe u

/-! ## Basic destructors for `IsClassicalSpace` -/

/-- Extract the signature condition from a classical-space proof. -/
theorem isClassicalSpace_signature {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    IsClassicalSignature star p q :=
  h.1

/-- Extract the complex-dimension condition from a classical-space proof. -/
theorem isClassicalSpace_finrank {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    Module.finrank ℂ V = p + q :=
  h.2.1

/-- Extract the paired compatibility condition from a classical-space proof. -/
theorem isClassicalSpace_compatible {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    JLCompatible J L :=
  h.2.2.1

/-- Extract the `L`-signature/eigenspace condition from a classical-space proof. -/
theorem isClassicalSpace_LSignature {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    LSignatureCondition star p q V L :=
  h.2.2.2

/-- Extract the commutation relation `LJ = JL`. -/
theorem isClassicalSpace_commute {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    ∀ v : V, L (J v) = J (L v) :=
  (isClassicalSpace_compatible h).commute

/-- Extract positivity of the Cartan Hermitian form. -/
theorem isClassicalSpace_cartan_positive {star : ClassicalStar} {p q : ℕ}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace star.eps V]
    {J : JStructure star.eps V star.jSign}
    {L : LStructure star.eps V star.dotEps}
    (h : IsClassicalSpace star p q V J L) :
    PositiveDefiniteHermitian star.eps V J L :=
  (isClassicalSpace_compatible h).cartan_positive

/-! ## Eigenspace lemmas needed by the blueprint -/

/-- `J` sends an `L`-eigenvector of eigenvalue `a` to an `L`-eigenvector of
conjugate eigenvalue `star a`, assuming `LJ = JL`.

Blueprint proof: if `L v = a v`, then
`L (J v) = J (L v) = J (a v) = star a • J v`, using conjugate-linearity of
`J`. -/
theorem linearEigenspace_J_mem_conj {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ} {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    J v ∈ linearEigenspace L.toLinearEquiv ((starRingEnd ℂ) a) := by
  sorry

/-- If the eigenvalue is fixed by complex conjugation, then the corresponding
`L`-eigenspace is `J`-stable. -/
theorem linearEigenspace_J_mem_of_star_eq {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign lSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V lSign)
    (hJL : JLCompatible J L) {a : ℂ}
    (ha : (starRingEnd ℂ) a = a) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv a) :
    J v ∈ linearEigenspace L.toLinearEquiv a := by
  sorry

/-- In the `dotε = -1` cases, `J` maps the `i`-eigenspace of `L` into the
`-i`-eigenspace. -/
theorem linearEigenspace_J_mem_i_to_neg_i {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.neg)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv Complex.I) :
    J v ∈ linearEigenspace L.toLinearEquiv (-Complex.I) := by
  sorry

/-- In the `dotε = -1` cases, `J` maps the `-i`-eigenspace of `L` into the
`i`-eigenspace. -/
theorem linearEigenspace_J_mem_neg_i_to_i {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.neg)
    (hJL : JLCompatible J L) {v : V}
    (hv : v ∈ linearEigenspace L.toLinearEquiv (-Complex.I)) :
    J v ∈ linearEigenspace L.toLinearEquiv Complex.I := by
  sorry

/-- When `L² = -1`, the `i` and `-i` eigenspaces have equal complex dimension,
provided `J` and `L` are compatible.

This is a theorem, not part of the definition of `LStructure`: the equality uses
conjugate-linearity of `J`, bijectivity of `J`, and `LJ = JL`.  The proof should
restrict `J` to an anti-linear equivalence between the two eigenspaces and then
convert that anti-linear equivalence into equality of complex dimensions. -/
theorem eig_i_finrank_eq_eig_neg_i_finrank {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {jSign : Sign}
    (J : JStructure eps V jSign) (L : LStructure eps V Sign.neg)
    (hJL : JLCompatible J L) :
    Module.finrank ℂ (linearEigenspace L.toLinearEquiv Complex.I) =
      Module.finrank ℂ (linearEigenspace L.toLinearEquiv (-Complex.I)) := by
  sorry

/-- Distinct `L`-eigenspaces are orthogonal for the bilinear form whenever the
product of eigenvalues is not `1`.

Blueprint proof: if `L u = a u` and `L v = b v`, then form preservation gives
`B(u,v)=B(Lu,Lv)=a*b*B(u,v)`.  If `a*b ≠ 1`, then `B(u,v)=0`. -/
theorem L_eigenspaces_form_orthogonal {eps : Sign}
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] {lSign : Sign}
    (L : LStructure eps V lSign) {a b : ℂ} (hab : a * b ≠ 1)
    {u v : V} (hu : u ∈ linearEigenspace L.toLinearEquiv a)
    (hv : v ∈ linearEigenspace L.toLinearEquiv b) :
    FormedSpace.B eps V u v = 0 := by
  sorry

/-- A subspace is totally isotropic for the formed-space bilinear form. -/
def FormTotallyIsotropic (eps : Sign)
    (V : Type u) [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace eps V] (S : Submodule ℂ V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, FormedSpace.B eps V u v = 0

/-! ## Case-specific intermediate theorem statements -/

/-- In the `B,D` cases, the `+1` and `-1` eigenspaces of `L` are orthogonal. -/
theorem BD_plus_minus_orthogonal
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.pos)
    {u v : V} (hu : u ∈ linearEigenspace L.toLinearEquiv 1)
    (hv : v ∈ linearEigenspace L.toLinearEquiv (-1)) :
    FormedSpace.B Sign.pos V u v = 0 := by
  sorry

/-- In the `C*` case, the `+1` eigenspace of `L` is stable under `J`. -/
theorem Cstar_J_stable_plus (a b : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (h : @IsClassicalSpace ClassicalStar.Cstar (2 * a) (2 * b) V _ _ _
      ‹FormedSpace Sign.neg V› J L)
    {v : V} (hv : v ∈ linearEigenspace L.toLinearEquiv 1) :
    J v ∈ linearEigenspace L.toLinearEquiv 1 := by
  sorry

/-- In the `C*` case, the `-1` eigenspace of `L` is stable under `J`. -/
theorem Cstar_J_stable_minus (a b : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.neg V]
    (J : JStructure Sign.neg V Sign.neg)
    (L : LStructure Sign.neg V Sign.pos)
    (h : @IsClassicalSpace ClassicalStar.Cstar (2 * a) (2 * b) V _ _ _
      ‹FormedSpace Sign.neg V› J L)
    {v : V} (hv : v ∈ linearEigenspace L.toLinearEquiv (-1)) :
    J v ∈ linearEigenspace L.toLinearEquiv (-1) := by
  sorry

namespace DStarAux

/-- In the `D*` case, the auxiliary operator `A = -iL`. -/
noncomputable def A
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) : V →ₗ[ℂ] V :=
  (-Complex.I) • L.toLinearMap

end DStarAux

/-- In the `D*` case, `J` maps the `A=+1` eigenspace to the `A=-1` eigenspace. -/
theorem Dstar_J_maps_A_plus_to_minus (r : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (h : @IsClassicalSpace ClassicalStar.Dstar r r V _ _ _
      ‹FormedSpace Sign.pos V› J L)
    {v : V} (hv : v ∈ LinearMap.ker (DStarAux.A L - 1 • LinearMap.id)) :
    J v ∈ LinearMap.ker (DStarAux.A L - (-1) • LinearMap.id) := by
  sorry

/-- In the `D*` case, the two eigenspaces of `A = -iL` have equal dimension. -/
theorem Dstar_A_eigen_dims_eq (r : ℕ)
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V]
    (J : JStructure Sign.pos V Sign.neg)
    (L : LStructure Sign.pos V Sign.neg)
    (h : @IsClassicalSpace ClassicalStar.Dstar r r V _ _ _
      ‹FormedSpace Sign.pos V› J L) :
    Module.finrank ℂ (LinearMap.ker (DStarAux.A L - 1 • LinearMap.id)) =
      Module.finrank ℂ (LinearMap.ker (DStarAux.A L - (-1) • LinearMap.id)) := by
  sorry

/-- In the `D*` case, the `A=+1` eigenspace is totally isotropic. -/
theorem Dstar_A_plus_totally_isotropic
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    FormTotallyIsotropic Sign.pos V (LinearMap.ker (DStarAux.A L - 1 • LinearMap.id)) := by
  sorry

/-- In the `D*` case, the `A=-1` eigenspace is totally isotropic. -/
theorem Dstar_A_minus_totally_isotropic
    {V : Type u} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    [FormedSpace Sign.pos V] (L : LStructure Sign.pos V Sign.neg) :
    FormTotallyIsotropic Sign.pos V (LinearMap.ker (DStarAux.A L - (-1) • LinearMap.id)) := by
  sorry

end ClassicalGroup
