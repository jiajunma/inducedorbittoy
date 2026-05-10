# ClassicalGroup/NormalForms.lean

## orthogonalAdaptedBasis_exists (line 627)
### Attempt 1
- **Approach:** Use `BDPlusFixedOrthonormalBasis_exists` and
  `BDMinusFixedOrthonormalBasis_exists` to obtain fixed-real bases in the
  `L=+1` and `L=-1` eigenspaces, prove their underlying vectors are complex
  linearly independent from their diagonal Gram matrices, promote them to
  complex bases by the finrank hypotheses, and combine them with
  `Submodule.prodEquivOfIsCompl` using `linearEigenspace_one_neg_one_isCompl`.
- **Result:** RESOLVED.
- **Key insight:** The fixed-real-to-complex bridge can be bypassed for this
  theorem by using the already-proved bilinear Gram identities: pairing a
  complex linear relation with each basis vector immediately extracts the
  coefficient.
- **Relevant lemmas used:** `BDPlusFixedOrthonormalBasis_exists`,
  `BDMinusFixedOrthonormalBasis_exists`, `BD_plus_minus_orthogonal`,
  `linearEigenspace_apply_eq`, `linearEigenspace_one_neg_one_isCompl`,
  `Module.Basis.prod`, `Module.Basis.map`.
- **Local helpers added:** private `form_orthogonal_linearIndependent` and
  `basisOfFormOrthogonal` in `NormalForms.lean`.

## Remaining sorries
### symplecticAdaptedBasis_exists
### Attempt 1
- **Approach:** Add the standard symplectic Gram-matrix infrastructure before
  `symplecticAdaptedBasis_exists`: prove linear independence by pairing a zero
  relation with the opposite block, then promote the family to a complex basis
  using `span_eq_top_of_card_eq_finrank'` and `hfin`.
- **Result:** RESOLVED for this subgoal. Added private helpers
  `symplectic_gram_linearIndependent` and `basisOfSymplecticGram` in
  `NormalForms.lean`.
- **Key insight:** Coefficient extraction is immediate from the four displayed
  Gram identities:
  pairing with `v (Sum.inr i)` gives `c (Sum.inl i) = 0`, while pairing with
  `v (Sum.inl i)` gives `-c (Sum.inr i) = 0`.
- **Search notes:** `lean_local_search "symplectic"` found only project-local
  normal-form declarations. `lean_leansearch` for finite-dimensional
  symplectic bases found bilinear-form primitives such as
  `LinearMap.BilinForm.dualBasis`, but no ready-made compatible symplectic
  Gram-Schmidt theorem.
- **Current result:** IN PROGRESS. The remaining gap is to construct a
  `J`-fixed family `v : Fin r ⊕ Fin r → V` with
  `L (v (Sum.inl i)) = -v (Sum.inr i)`,
  `L (v (Sum.inr i)) = v (Sum.inl i)`, and the four standard symplectic Gram
  identities. Once such a family exists, `basisOfSymplecticGram` gives the
  `basis` field and the adapted-basis record fields are direct.
- **Next step:** Formalize the real compatible Gram-Schmidt lemma on
  `JFixedRealSubmodule V J`, using the positive form
  `g(x,y) = B(L x, y)` and the `L`-stable orthogonal-complement induction from
  the blueprint.

### Attempt 2
- **Approach:** Added the next bridge layer requested by the plan. First added
  private `symplecticJFixedInnerCore` on `JFixedRealSubmodule V J`, with inner
  product `Re B(Lx,y)`, using `hcompat.cartan_positive` for symmetry,
  nonnegativity, and definiteness. Then added private
  `symplecticAdaptedBasis_of_isotropic_g_orthonormal`: from
  `e : Fin r -> V` with `J(e_i)=e_i`, `B(e_i,e_j)=0`, and
  `B(L e_i,e_j)=δ_ij`, define
  `v (Sum.inl i)=e_i`, `v (Sum.inr i)=-L(e_i)`, build the basis with
  `basisOfSymplecticGram`, and fill all `SymplecticAdaptedBasis` fields.
- **Result:** RESOLVED for the bridge and metric-core subgoals. The main theorem
  now reduces explicitly to the remaining existence of such an `e` family.
- **Key insight:** The four Gram identities follow from `hIso`, `hG`,
  `L.preserves_form`, `FormedSpace.eps_symm` for `Sign.neg`, `hcompat.commute`,
  and `L.sq`. No new axioms or statement changes were needed.
- **Current result:** IN PROGRESS. The only `symplecticAdaptedBasis_exists`
  hole is now the suffices subgoal:
  `∃ e : Fin r -> V, J(e_i)=e_i ∧ B(e_i,e_j)=0 ∧ B(L e_i,e_j)=δ_ij`.
- **Next step:** Instantiate `symplecticJFixedInnerCore` as an
  `InnerProductSpace ℝ (JFixedRealSubmodule V J)`, prove the `L`-stable
  `g`-orthogonal complement induction, and obtain the required `e_i` by
  compatible symplectic Gram-Schmidt.

### Attempt 3
- **Approach:** Added the missing compatible Gram-Schmidt theorem as private
  `symplecticCompatibleFamily_exists`. The proof works by induction on `r` in a
  finite-dimensional real inner product space with a skew-adjoint operator
  `L` satisfying `L^2=-1`: pick a unit vector `v`, split off
  `span {v, L v}`, prove its orthogonal complement is `L`-stable, recurse, and
  prepend `v`.
- **Additional helper:** Added private
  `finrank_JFixedRealSubmodule_eq_complex`, using the existing
  `finrank_JFixedSubmoduleIn_eq_complex` bridge with `S = ⊤`, so
  `dim_ℝ V^J = dim_ℂ V`.
- **Result:** RESOLVED. `symplecticAdaptedBasis_exists` is now sorry-free. The
  final construction instantiates the positive real core
  `symplecticJFixedInnerCore J L hcompat`, restricts `L` to `V^J`, applies
  `symplecticCompatibleFamily_exists`, and converts the real inner-product
  identities back to complex bilinear-form identities via
  `form_star_eq_of_mem_JFixedRealSubmodule` and
  `complex_eq_of_star_eq_of_re_eq`.
- **Axiom check:** `lean_verify ClassicalGroup.symplecticAdaptedBasis_exists`
  and `lean_verify ClassicalGroup.symplecticNormalFormIso` both report only
  `propext`, `Classical.choice`, and `Quot.sound`.

### cstarAdaptedBasis_exists
### Attempt 1
- **Approach:** Added the requested `C*` helper layer. First proved private
  `cstar_gram_linearIndependent` by coefficient extraction from the
  `cstarGram` matrix, then `basisOfCstarGram` by the same
  `span_eq_top_of_card_eq_finrank'` promotion pattern used for the symplectic
  case. Added `cstarAdaptedBasis_of_quaternionic_families`, which packages
  positive and negative families `e_i, J e_i` into the `CstarAdaptedBasis`
  record and derives cross-block vanishing from
  `L_eigenspaces_form_orthogonal`.
- **Result:** RESOLVED for the helper layer.
- **Key insight:** The signs in `cstarGram` are recovered by pairing each
  coefficient with its quaternionic partner: positive `e` pairs with positive
  `J e` by `+1`, positive `J e` pairs back by `-1`; the negative block has the
  opposite signs.

### Attempt 2
- **Approach:** Added private `quaternionicCompatibleFamily_exists`, a complex
  inner-product Gram-Schmidt induction for an antiunitary semilinear equivalence
  `J` with `J^2=-1`. The induction splits off the orthonormal pair
  `v, J v`, proves the orthogonal complement is `J`-stable, restricts `J` to
  the complement with `SemilinearEquiv.ofSubmodules`, and recurses.
- **Result:** RESOLVED.
- **Key insight:** Orthogonality of `v` and `J v` follows from
  `inner (J (J v)) (J v) = inner v (J v)`, hence
  `-inner v (J v) = inner v (J v)`.

### Attempt 3
- **Approach:** Closed `cstarAdaptedBasis_exists`. Instantiated
  `cartanInnerCore V J L hcompat.cartan_positive` as a complex inner product on
  `V`, proved globally that `J` is antiunitary for this Cartan inner product,
  restricted `J` to the `L=+1` and `L=-1` eigenspaces, applied
  `quaternionicCompatibleFamily_exists` to each block using the finrank
  hypotheses, and converted the resulting inner-product identities to the
  required bilinear-form identities.
- **Result:** RESOLVED. `cstarAdaptedBasis_exists` and `cstarNormalFormIso` are
  now sorry-free.
- **Axiom check:** `lean_verify ClassicalGroup.cstarAdaptedBasis_exists` and
  `lean_verify ClassicalGroup.cstarNormalFormIso` both report only standard
  axioms: `propext`, `Classical.choice`, and `Quot.sound`.

### dstarAdaptedBasis_exists
### Attempt 1
- **Approach:** Added the `D*` helper layer in `NormalForms.lean`: first
  `dstar_gram_linearIndependent` and `basisOfDstarGram` by coefficient
  extraction from `dstarGram`, then explicit `L=i`/`L=-i` projection helpers
  using `(1/2) • (v - I • L v)` and `(1/2) • (v + I • L v)`. These prove the
  two eigenspaces are complementary. Combined this with
  `eig_i_finrank_eq_eig_neg_i_finrank` and `hfin : finrank V = r+r` to get
  `finrank (L=i) = r`.
- **Approach:** Instantiated `cartanInnerCore V J L hcompat.cartan_positive` as
  a complex inner product on `V`, chose `stdOrthonormalBasis` of the `L=i`
  eigenspace, and packed the family `e_i, J e_i` through
  `dstarAdaptedBasis_of_i_orthonormal`.
- **Result:** RESOLVED. `dstarAdaptedBasis_exists`, `dstarNormalFormIso`, and
  `normalForm_Dstar` are now sorry-free.
- **Key insight:** For `e_i` in the `L=i` eigenspace, Cartan orthonormality gives
  `B (L e_i) (J e_j) = δ_ji`, hence `I * B e_i (J e_j) = δ_ji`, so
  `B e_i (J e_j) = -I * δ_ij`, exactly the cross-block value in `dstarGram`.
  Same-block vanishing follows from `L_eigenspaces_form_orthogonal` because
  `I*I ≠ 1` and `(-I)*(-I) ≠ 1`.
- **Relevant lemmas used:** `linearEigenspace_J_mem_i_to_neg_i`,
  `eig_i_finrank_eq_eig_neg_i_finrank`, `linearEigenspace_apply_eq`,
  `L_eigenspaces_form_orthogonal`, `cartanInnerCore`, `stdOrthonormalBasis`,
  `Submodule.finrank_add_eq_of_isCompl`, `FormedSpace.eps_symm`.
- **Axiom check:** `lean_verify ClassicalGroup.dstarAdaptedBasis_exists`,
  `lean_verify ClassicalGroup.dstarNormalFormIso`, and
  `lean_verify ClassicalGroup.normalForm_Dstar` all report only standard axioms:
  `propext`, `Classical.choice`, and `Quot.sound`.

## Verification
- `lean_diagnostic_messages ClassicalGroup/NormalForms.lean` reports no items.
- `lake env lean ClassicalGroup/NormalForms.lean` passed with no output.
- `lake build ClassicalGroup` passed. It reported only the two pre-existing
  `ClassicalGroup/Lemmas.lean` unnecessary-`simpa` warnings.
- `rg -n "sorry" ClassicalGroup/*.lean` now returns no matches.
- `lean_verify ClassicalGroup.dstarAdaptedBasis_exists`,
  `lean_verify ClassicalGroup.dstarNormalFormIso`, and
  `lean_verify ClassicalGroup.normalForm_Dstar` all report only standard axioms:
  `propext`, `Classical.choice`, and `Quot.sound`.

## Previous verification
- `lake env lean ClassicalGroup/NormalForms.lean` passed after closing
  `cstarAdaptedBasis_exists`; the only remaining declaration-use warning was the
  tracked `dstarAdaptedBasis_exists` sorry.
- `lake build ClassicalGroup` passed after closing `cstarAdaptedBasis_exists`.
  It reported the two pre-existing `ClassicalGroup/Lemmas.lean`
  unnecessary-`simpa` warnings and the one expected `NormalForms.lean`
  `dstarAdaptedBasis_exists` sorry warning.
- `rg -n "sorry" ClassicalGroup/*.lean` reported:
  `NormalForms.lean:2615`.
- `lean_verify ClassicalGroup.cstarAdaptedBasis_exists` and
  `lean_verify ClassicalGroup.cstarNormalFormIso` both report only standard
  axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Earlier verification
- `lake env lean ClassicalGroup/NormalForms.lean` passed after closing
  `symplecticAdaptedBasis_exists`; only remaining declaration-use warnings are
  the two tracked later `NormalForms.lean` sorries.
- `lake build ClassicalGroup` passed after closing the theorem. It reported the
  two pre-existing `ClassicalGroup/Lemmas.lean` unnecessary-`simpa` warnings
  and the two expected `NormalForms.lean` sorry warnings.
- `rg -n "sorry" ClassicalGroup/*.lean` now reports:
  `NormalForms.lean:1810` and `NormalForms.lean:2045`.
- `lean_verify ClassicalGroup.orthogonalAdaptedBasis_exists` reports only
  standard axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `lean_verify ClassicalGroup.symplecticJFixedInnerCore` and
  `lean_verify ClassicalGroup.symplecticAdaptedBasis_of_isotropic_g_orthonormal`
  both report only standard axioms: `propext`, `Classical.choice`,
  `Quot.sound`.
- `lean_verify ClassicalGroup.symplecticAdaptedBasis_exists` and
  `lean_verify ClassicalGroup.symplecticNormalFormIso` both report only standard
  axioms: `propext`, `Classical.choice`, `Quot.sound`.
