# ClassicalGroup Done

Coordinate-to-normal-form layers are already proved.
Standard model existence is already proved.

Solved in current ClassicalGroup run:
- `ClassicalGroup/NormalForms.lean :: orthogonalAdaptedBasis_exists`.
  Archon iteration 21 added private helpers `form_orthogonal_linearIndependent` and
  `basisOfFormOrthogonal`, constructed complex bases for the `L=+1` and `L=-1` eigenspaces,
  combined them by `Submodule.prodEquivOfIsCompl`, and verified the adapted-basis fields.
  Plan-agent verification on 2026-05-10 confirmed the declaration depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- Helper layers now available in `ClassicalGroup/NormalForms.lean`:
  `symplectic_gram_linearIndependent`,
  `basisOfSymplecticGram`,
  `symplecticJFixedInnerCore`,
  `finrank_JFixedRealSubmodule_eq_complex`,
  `symplecticCompatibleFamily_exists`,
  `symplecticAdaptedBasis_of_isotropic_g_orthonormal`.
  Plan-agent verification on 2026-05-10T02:53:25+08:00 kept `ClassicalGroup/NormalForms.lean`
  green with only the three tracked sorry warnings.
- `ClassicalGroup/NormalForms.lean :: symplecticAdaptedBasis_exists`.
  Archon session 23 added the fixed-real dimension bridge
  `finrank_JFixedRealSubmodule_eq_complex` and the abstract compatible real Gram-Schmidt helper
  `symplecticCompatibleFamily_exists`, restricted `L` to `JFixedRealSubmodule V J`, and converted
  the real inner-product output back into complex bilinear-form identities using
  `form_star_eq_of_mem_JFixedRealSubmodule` and `complex_eq_of_star_eq_of_re_eq`.
  Plan-agent verification on 2026-05-10T04:16:37+08:00 confirmed the theorem depends only on
  `propext`, `Classical.choice`, and `Quot.sound`.
- `ClassicalGroup/NormalForms.lean :: symplecticNormalFormIso`.
  This wrapper is solved as a direct consequence of `symplecticAdaptedBasis_exists` and
  `SymplecticAdaptedBasis.toNormalFormIso`. Plan-agent verification on
  2026-05-10T04:16:37+08:00 confirmed only the standard axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- Helper layers now available in `ClassicalGroup/NormalForms.lean`:
  `cstar_gram_linearIndependent`,
  `basisOfCstarGram`,
  `quaternionicCompatibleFamily_exists`, and
  `cstarAdaptedBasis_of_quaternionic_families`.
  These package the `CstarGram` coefficient-extraction basis argument, abstract
  quaternionic complex Gram-Schmidt, and the bridge from positive/negative
  quaternionic families to a `CstarAdaptedBasis`.
- `ClassicalGroup/NormalForms.lean :: cstarAdaptedBasis_exists`.
  Archon session 24 restricted the Cartan Hermitian form to the `L=+1` and
  `L=-1` eigenspaces, used direct `J`-stability from
  `linearEigenspace_J_mem_of_star_eq J L hcompat (by simp)`, applied
  `quaternionicCompatibleFamily_exists` in each block, and converted the
  inner-product identities back to the required bilinear-form Gram entries.
  Plan-agent verification on 2026-05-10T04:34:44+08:00 confirmed the theorem
  depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- `ClassicalGroup/NormalForms.lean :: cstarNormalFormIso`.
  This wrapper is solved as a direct consequence of `cstarAdaptedBasis_exists`
  and `CstarAdaptedBasis.toNormalFormIso`. Plan-agent verification on
  2026-05-10T04:34:44+08:00 confirmed only the standard axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- `ClassicalGroup/NormalForms.lean :: dstarAdaptedBasis_exists`.
  Archon session 25 added the `DstarGram` basis helpers, explicit `L=i`/`L=-i`
  eigenspace complement and half-dimension bridge, and the bridge from an
  `L=i` orthonormal family to `DstarAdaptedBasis`. Final verification on
  2026-05-10T04:55+08:00 found no `sorry` matches in `ClassicalGroup/*.lean`
  and `lake build ClassicalGroup` succeeded.
