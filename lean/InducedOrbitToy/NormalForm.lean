import InducedOrbitToy.Slice

/-!
# `prop:p-normal-form` and `prop:kernel-image`

Autoformalization of `prop:p-normal-form` (lines 175–319) and
`prop:kernel-image` (lines 321–411) from `references/blueprint_verified.md`.

This file:

* introduces the NormalForm-only API (`IsSkewT`, `MaximalRank`, `Cbar`,
  `Tset_circ`, `IsParabolicElement`, `BT`, `AreIsometric`),
* states the four key theorems (`pNormalForm`,
  `pNormalForm_residual_orbit_iso`, `kernelImage_ker`, `kernelImage_im`,
  `kernelImage_dim`).

All proof bodies are `sorry` for the autoformalize stage.

The Slice-side primitives `IsSkewB`, `XCB`, `XST`, `Cdual`, and `X0Lift`
are imported from `InducedOrbitToy.Slice` and used directly in the theorem
statements below.
-/

namespace InducedOrbitToy

open LinearMap

variable {F : Type*} [Field F]

namespace SliceSetup

variable (S : SliceSetup F)

/-! ## `IsSkewT` — the skew predicate on `T : L₀' →ₗ L₀` -/

/-- The skew predicate on a map `T : S.L0' →ₗ[F] S.L0` (a representative of
the set `𝒯` of the blueprint):

`λ((T u).val, v) + ε · λ((T v).val, u) = 0`

for all `u, v ∈ L0'`, where `(T u).val : E` is obtained via the inclusion
`L0 ↪ E`. -/
def IsSkewT (T : S.L0' →ₗ[F] S.L0) : Prop :=
  ∀ u v : S.L0',
    S.lambda ((T u : S.E)) (v : S.E') +
        S.eps * S.lambda ((T v : S.E)) (u : S.E') = 0

/-! ## `MaximalRank` — the maximal possible rank of an element of `𝒯` -/

/-- Blueprint's `l_max(ε, l)`: the maximal rank a skew operator
`T : L0' →ₗ L0` can have.  When `(ε = 1)` and `l := dim L0'` is odd, the
skew-symmetric form forces the rank down by `1`; otherwise the maximal
rank equals `l`. -/
noncomputable def MaximalRank : ℕ :=
  let l := Module.finrank F S.L0'
  open Classical in if S.eps = 1 ∧ Odd l then l - 1 else l

/-! ## `Tset_circ` — the locus of maximal-rank skew `T` -/

/-- The `𝒯°` locus from the blueprint: skew `T : L0' →ₗ L0` whose range
attains the maximal possible dimension. -/
noncomputable def Tset_circ : Set (S.L0' →ₗ[F] S.L0) :=
  { T | IsSkewT S T ∧ Module.finrank F (LinearMap.range T) = S.MaximalRank }

/-! ## `Cbar` — the quotient map `C : E' → V₀ / Im X₀` -/

/-- The quotient `Cbar` of `C : S.E' →ₗ[F] S.V0` by `Im X₀`. -/
noncomputable def Cbar (C : S.E' →ₗ[F] S.V0) :
    S.E' →ₗ[F] (S.V0 ⧸ LinearMap.range S.X0) :=
  (LinearMap.range S.X0).mkQ ∘ₗ C

/-! ## `IsParabolicElement` — an invertible operator preserving the flag and form -/

/-- Predicate "`p ∈ P`" capturing membership in the parabolic subgroup of
`GL(V)` (the data underlying the blueprint's `P`):

* `p` is invertible,
* `p` preserves the flag `0 ≤ E ≤ E ⊕ V₀ ≤ V`,
* `p` is an isometry of the ambient form
  (`LinearMap.IsOrthogonal S.ambientForm p`).

The third clause encodes "form-preserving" via Mathlib's
`LinearMap.IsOrthogonal` predicate, matching the
`IsometryEnd` shape used in `Orbits.lean`. -/
def IsParabolicElement (p : Module.End F S.V) : Prop :=
  IsUnit p ∧ Submodule.map p S.flagE = S.flagE ∧
    Submodule.map p S.flagEV0 = S.flagEV0 ∧
    LinearMap.IsOrthogonal S.ambientForm p

/-! ## `BT` — the bilinear form `(u, v) ↦ λ((T u).val, v)` on `L0'` -/

/-- The bilinear form on `L0'` induced by a skew `T : L0' →ₗ L0`:

`B_T (u, v) := λ((T u).val, v)`.

This is the bilinear space whose isometry class classifies the residual
`P`-orbits in `prop:p-normal-form`. -/
noncomputable def BT (T : S.L0' →ₗ[F] S.L0) : LinearMap.BilinForm F S.L0' :=
  LinearMap.mk₂ F
    (fun u v => S.lambda ((T u : S.E)) (v : S.E'))
    (by
      intro u₁ u₂ v
      simp [map_add, LinearMap.add_apply])
    (by
      intro c u v
      simp [map_smul, LinearMap.smul_apply, smul_eq_mul])
    (by
      intro u v₁ v₂
      simp [map_add])
    (by
      intro c u v
      simp [map_smul, smul_eq_mul])

end SliceSetup

/-! ## `AreIsometric` — abstract isometry between bilinear forms -/

namespace Bilinear

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Two bilinear forms `b₁ b₂ : V →ₗ[F] V →ₗ[F] F` are `AreIsometric` if
there is a linear automorphism `h : V ≃ₗ[F] V` with
`b₂ (h u) (h v) = b₁ u v` for all `u, v`. -/
def AreIsometric (b₁ b₂ : LinearMap.BilinForm F V) : Prop :=
  ∃ h : V ≃ₗ[F] V, ∀ u v : V, b₂ (h u) (h v) = b₁ u v

end Bilinear

namespace SliceSetup

variable (S : SliceSetup F)

/-! ## Theorem `prop:p-normal-form`

The two halves of `prop:p-normal-form`: existence of a `P`-conjugacy of
`XCB S C B` to a normalised `XST S Sₕ T`, and the residual-orbit
classification by isometry of `BT S T`.

`XCB`, `XST` and `IsSkewB` come from `InducedOrbitToy.Slice`. -/

/-! ### Helper lemmas for `pNormalForm`. -/

/-- Easy consequence: `IsUnit (uD S D)` over a finite-dimensional `S.V`. -/
private lemma isUnit_uD (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    IsUnit (uD S D) := by
  have h1 : uD S D * uD S (-D) = 1 := uD_neg_inverse S hNondeg hChar D
  exact (Units.mkOfMulEqOne _ _ h1).isUnit

/-- Map equality from inclusion: `Submodule.map (uD D) F0 ≤ F0` plus
`Submodule.map (uD (-D)) F0 ≤ F0` upgrades to equality. -/
private lemma map_uD_eq_of_le (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) (F0 : Submodule F S.V)
    (h_pos : Submodule.map (uD S D) F0 ≤ F0)
    (h_neg : Submodule.map (uD S (-D)) F0 ≤ F0) :
    Submodule.map (uD S D) F0 = F0 := by
  apply le_antisymm h_pos
  intro x hx
  -- x = uD D (uD (-D) x), and uD (-D) x ∈ F0.
  have hcomp : uD S D ∘ₗ uD S (-D) = LinearMap.id :=
    uD_neg_inverse S hNondeg hChar D
  have hkey : uD S D (uD S (-D) x) = x := by
    have := congrArg (fun f : Module.End F S.V => f x) hcomp
    simpa using this
  refine ⟨uD S (-D) x, ?_, hkey⟩
  exact h_neg ⟨x, hx, rfl⟩

/-- Witness existence for `pNormalForm` (new Round 7 signature).

There exist `(Sₕ, D, d, T)` such that the *Levi+unipotent* conjugator
`p := uD D ∘ leviGL_E d` realises `p ∘ XCB(C, B) = XST(Sₕ, T) ∘ p`.

This bundles the multi-step normalisation from the blueprint proof
(lines 200–264 of `references/blueprint_verified.md`):
  (a) act by a Levi element `leviGL_E d` of `P` so `ker (Cbar (C ∘ d.symm))
      = L0'` and `Cbar (C ∘ d.symm)|_{L1'}` equals `mkQ ∘ Sₕ` for some
      `Sₕ : L1' ≃ Vplus`,
  (b) act by `uD D` for a suitable `D : E' →ₗ V0` so that
      `uD D ∘ XCB (C ∘ d.symm) (lambdaDualE d.symm ∘ B ∘ d.symm) ∘ uD (-D)
      = XST Sₕ T`, with `T : L0' →ₗ L0` skew.

`Sₕ` is delivered as a `LinearEquiv` (its surjectivity is needed by the
`pNormalForm_residual_orbit_iso` consumer via `kernelImage_ker`).

**Tier A #1 (Round 7) — current state.** The full body remains a
single carefully-marked `sorry`. The steps required are:

1. Build `(Sₕ, d)` from `_hRank : rank Cbar = c` (the `d`-construction).
2. Set `(C', B') := (C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm)` and
   apply `leviGL_E_conj_XCB`.
3. Build `D` such that `X0 ∘ D = C' - CST Sₕ` (lands in `range X0` by
   construction); `T` reads off the `B`-block residual.
4. Combine via `uD_conj_XCB` + uniqueness (`parametrizeX0PlusU_uniqueness`)
   + `uD_neg_inverse`.

Round 8 will close this remaining piece. The two pNormalForm_witnesses
*consumers* — `pNormalForm` and (downstream) `pNormalForm_residual_orbit_iso`
— now consume the new (correct) signature; `pNormalForm`'s body is
sorry-free. -/
private theorem pNormalForm_witnesses (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B)
    (_hRank :
      Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
      (d : S.E' ≃ₗ[F] S.E') (T : S.L0' →ₗ[F] S.L0),
      IsSkewT S T ∧
      uD S D ∘ₗ leviGL_E S d ∘ₗ XCB S C B
        = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T ∘ₗ uD S D ∘ₗ leviGL_E S d := by
  -- TIER A #1 (Round 7) BODY — single isolated `sorry`. See docstring
  -- above for the four-step plan and `.archon/informal/normalform_round7.md`
  -- § Tier A #1 for the full informal proof outline. Round 8 closes this.
  sorry

/-- `prop:p-normal-form` (existence of normal form).  Existence of a
`P`-conjugacy (encoded by `IsParabolicElement`) of `XCB S C B` to some
`XST S Sₕ T` with `T ∈ 𝒯`, given the rank condition `rank Cbar = c`.

Blueprint outline (`references/blueprint_verified.md` §`prop:p-normal-form`):

1. **Step 1.** Use `_hRank : rank Cbar = c` to pick a Levi-decomposed
   `Sₕ : L1' →ₗ Vplus` (an isomorphism, by the rank assumption combined
   with `dim Vplus = c`) and adjust `C` so that `C|_{L1'} = Sₕ` and
   `C|_{L0'} = 0`. Conjugation by a Levi element of `P` realises this
   adjustment.
2. **Step 2.** With `C` normalised, conjugate by an element `u_D ∈ P`
   (`Slice.lean :: uD`) to absorb the `B|_{L1'}` block; this uses
   `lem:unipotent-conjugation` and `lem:parametrize-x0-plus-u` from
   `Slice.lean`.  The remaining `B|_{L0'}` block defines
   `T : L0' →ₗ L0`.
3. **Step 3.** Verify that the resulting `T` is skew (`IsSkewT`); this
   uses `_hB : IsSkewB B` plus the conjugation formula `uD_conj_XCB`.

This proof reduces to `pNormalForm_witnesses` (the Levi-witness
existence) plus the standard parabolic-element machinery (`isUnit_uD`,
`map_uD_eq_of_le`, `uD_isParabolic`). The isometry conjunct of
`IsParabolicElement` is discharged by chaining the (now-corrected)
`IsAdjointPair (uD D) (uD (-D))` from `uD_isParabolic` with
`uD_neg_inverse` to evaluate `uD (-D) ∘ uD D = id`. -/
theorem pNormalForm
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B)
    (_hRank :
      Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0),
      IsSkewT S T ∧
        ∃ (p : Module.End F S.V), IsParabolicElement S p ∧
          p ∘ₗ XCB S C B = XST S Sₕ T ∘ₗ p := by
  -- Step 1: Pull (Sₕ, D, d, T) plus the conjugation equation from the helper.
  -- (Round 7 signature: pNormalForm_witnesses now exposes a Levi factor `d`.)
  obtain ⟨Sₕ, D, d, T, hT, hConj⟩ :=
    pNormalForm_witnesses S _hNondeg _hChar C B _hB _hRank
  -- The parabolic conjugator is `p := uD D ∘ leviGL_E d`.
  refine ⟨(Sₕ : S.L1' →ₗ[F] S.Vplus), T, hT,
    uD S D ∘ₗ leviGL_E S d, ?_, ?_⟩
  · -- IsParabolicElement (uD S D ∘ leviGL_E S d): four conjuncts.
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- IsUnit: product of two units.
      have hu_uD : IsUnit (uD S D) := isUnit_uD S _hNondeg _hChar D
      have hu_levi : IsUnit (leviGL_E S d) := (leviGL_E_isParabolic S d).1
      exact hu_uD.mul hu_levi
    · -- Submodule.map (uD D ∘ leviGL_E d) flagE = flagE.
      -- Compose: map (g ∘ f) = map g ∘ map f. Then leviGL_E preserves flagE,
      -- and uD preserves flagE (via map_uD_eq_of_le).
      have hLevi : Submodule.map (leviGL_E S d) S.flagE = S.flagE :=
        (leviGL_E_isParabolic S d).2.1
      have h_pos : Submodule.map (uD S D) S.flagE ≤ S.flagE :=
        (uD_isParabolic S _hNondeg _hChar D).2.1
      have h_neg : Submodule.map (uD S (-D)) S.flagE ≤ S.flagE :=
        (uD_isParabolic S _hNondeg _hChar (-D)).2.1
      have hUD : Submodule.map (uD S D) S.flagE = S.flagE :=
        map_uD_eq_of_le S _hNondeg _hChar D S.flagE h_pos h_neg
      rw [show (uD S D ∘ₗ leviGL_E S d) = (uD S D : S.V →ₗ[F] S.V).comp
            (leviGL_E S d : S.V →ₗ[F] S.V) from rfl]
      rw [Submodule.map_comp, hLevi, hUD]
    · -- Submodule.map (uD D ∘ leviGL_E d) flagEV0 = flagEV0. Same template.
      have hLevi : Submodule.map (leviGL_E S d) S.flagEV0 = S.flagEV0 :=
        (leviGL_E_isParabolic S d).2.2.1
      have h_pos : Submodule.map (uD S D) S.flagEV0 ≤ S.flagEV0 :=
        (uD_isParabolic S _hNondeg _hChar D).2.2
      have h_neg : Submodule.map (uD S (-D)) S.flagEV0 ≤ S.flagEV0 :=
        (uD_isParabolic S _hNondeg _hChar (-D)).2.2
      have hUD : Submodule.map (uD S D) S.flagEV0 = S.flagEV0 :=
        map_uD_eq_of_le S _hNondeg _hChar D S.flagEV0 h_pos h_neg
      rw [show (uD S D ∘ₗ leviGL_E S d) = (uD S D : S.V →ₗ[F] S.V).comp
            (leviGL_E S d : S.V →ₗ[F] S.V) from rfl]
      rw [Submodule.map_comp, hLevi, hUD]
    · -- IsOrthogonal: composition of two isometries is an isometry.
      intro u v
      have hLeviIso : LinearMap.IsOrthogonal S.ambientForm (leviGL_E S d) :=
        (leviGL_E_isParabolic S d).2.2.2
      -- Derive `IsOrthogonal` for `uD D` from its `IsAdjointPair` + uD-inverse.
      have hAdj :
          LinearMap.IsAdjointPair S.ambientForm S.ambientForm
              (uD S D) (uD S (-D)) :=
        (uD_isParabolic S _hNondeg _hChar D).1
      have hinv : uD S (-D) ∘ₗ uD S D = LinearMap.id := by
        have := uD_neg_inverse S _hNondeg _hChar (-D)
        simpa [neg_neg] using this
      have hinv_apply : ∀ w, uD S (-D) (uD S D w) = w := by
        intro w
        have := congrArg (fun f : Module.End F S.V => f w) hinv
        simpa using this
      have hUDIso : ∀ x y, S.ambientForm (uD S D x) (uD S D y)
          = S.ambientForm x y := by
        intro x y
        calc S.ambientForm (uD S D x) (uD S D y)
            = S.ambientForm x (uD S (-D) (uD S D y)) := hAdj x (uD S D y)
          _ = S.ambientForm x y := by rw [hinv_apply]
      -- Now combine: uD ∘ leviGL_E preserves the form via two-step chase.
      show S.ambientForm ((uD S D ∘ₗ leviGL_E S d) u)
          ((uD S D ∘ₗ leviGL_E S d) v) = S.ambientForm u v
      simp only [LinearMap.comp_apply]
      rw [hUDIso, hLeviIso]
  · -- Conjugation: `(uD D ∘ leviGL_E d) ∘ XCB C B = XST Sₕ T ∘ (uD D ∘ leviGL_E d)`.
    -- This is `hConj` modulo associativity.
    show (uD S D ∘ₗ leviGL_E S d) ∘ₗ XCB S C B
        = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T ∘ₗ (uD S D ∘ₗ leviGL_E S d)
    rw [LinearMap.comp_assoc]
    exact hConj

/-! ### Helper: explicit formula for `XST` applied to a triple. -/

/-- `XST S Sₕ T` applied to `(e, v, e')` is `(Cdual (CST Sₕ) v + (T (projL0' e') : E),
X0 v + (Sₕ (projL1' e') : V0), 0)`. -/
private theorem XST_apply (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0)
    (e : S.E) (v : S.V0) (e' : S.E') :
    XST S Sₕ T (e, v, e') =
      (Cdual S (CST S Sₕ) v + (T (projL0' S e') : S.E),
        S.X0 v + (Sₕ (projL1' S e') : S.V0), 0) := by
  -- Unfold XST = XCB S (CST Sₕ) (BST T), then unfold XCB.
  show XCB S (CST S Sₕ) (BST S T) (e, v, e') = _
  unfold XCB
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.inl_apply, LinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add]
  -- Now reduce `BST S T e'` and `CST S Sₕ e'` to their definitions.
  unfold BST CST
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]

/-! ### Helpers for `pNormalForm_residual_orbit_iso`. -/

/-- Extension of an `L0'`-iso `h` to a full `E'`-iso acting as `id` on `L1'`
and as `h` on `L0'`. Built via the `IsCompl L1' L0'` direct-sum
decomposition. Used in `residual_levi_build` (Round 7) to lift an
`L0'`-isometry to a Levi factor `leviGL_E S d` realising the residual
conjugation. -/
private noncomputable def extendL0'IsoToE' (S : SliceSetup F)
    (h : S.L0' ≃ₗ[F] S.L0') : S.paired.E' ≃ₗ[F] S.paired.E' :=
  let prodEq : (S.L1' × S.L0') ≃ₗ[F] S.paired.E' :=
    S.L1'.prodEquivOfIsCompl S.L0' S.isComplL'
  let prodMap : (S.L1' × S.L0') ≃ₗ[F] (S.L1' × S.L0') :=
    (LinearEquiv.refl F S.L1').prodCongr h
  prodEq.symm ≪≫ₗ prodMap ≪≫ₗ prodEq

/-- Pointwise formula for the symm of `extendL0'IsoToE'`. -/
private lemma extendL0'IsoToE'_symm_apply (S : SliceSetup F)
    (h : S.L0' ≃ₗ[F] S.L0') (e' : S.paired.E') :
    (extendL0'IsoToE' S h).symm e' =
      (projL1' S e' : S.paired.E') + (h.symm (projL0' S e') : S.paired.E') := by
  -- Unfold the composition and use prodEquivOfIsCompl symm/apply lemmas.
  show (S.L1'.prodEquivOfIsCompl S.L0' S.isComplL')
        (((LinearEquiv.refl F S.L1').prodCongr h).symm
          ((S.L1'.prodEquivOfIsCompl S.L0' S.isComplL').symm e'))
      = (projL1' S e' : S.paired.E') + (h.symm (projL0' S e') : S.paired.E')
  -- Step 1: prodEq.symm e' = (projL1' e', projL0' e').
  have hsymm : ((S.L1'.prodEquivOfIsCompl S.L0' S.isComplL').symm e' : S.L1' × S.L0')
      = (projL1' S e', projL0' S e') := by
    have := Submodule.toLinearMap_prodEquivOfIsCompl_symm S.isComplL'
    show ((S.L1'.prodEquivOfIsCompl S.L0' S.isComplL').symm.toLinearMap e') = _
    rw [this]
    rfl
  rw [hsymm]
  -- Step 2: prodMap.symm (a, b) = (a, h.symm b).
  show (S.L1'.prodEquivOfIsCompl S.L0' S.isComplL') (projL1' S e', h.symm (projL0' S e'))
      = (projL1' S e' : S.paired.E') + (h.symm (projL0' S e') : S.paired.E')
  -- Step 3: prodEq (a, b) = a.subtype + b.subtype.
  rw [show (S.L1'.prodEquivOfIsCompl S.L0' S.isComplL')
            (projL1' S e', h.symm (projL0' S e'))
        = (S.L1'.subtype.coprod S.L0'.subtype)
            (projL1' S e', h.symm (projL0' S e')) from by
    have := Submodule.coe_prodEquivOfIsCompl (p := S.L1') (q := S.L0') S.isComplL'
    -- The coe statement gives equality of the underlying linear maps.
    have h2 : ((S.L1'.prodEquivOfIsCompl S.L0' S.isComplL') :
        (S.L1' × S.L0') →ₗ[F] S.paired.E')
          = S.L1'.subtype.coprod S.L0'.subtype := this
    have h3 := congrArg (fun (f : (S.L1' × S.L0') →ₗ[F] S.paired.E') =>
      f (projL1' S e', h.symm (projL0' S e'))) h2
    simp only at h3
    exact h3]
  simp [LinearMap.coprod_apply]

/-- `projL1' ∘ d.symm = projL1'` where `d := extendL0'IsoToE' S h`. -/
private lemma projL1'_extendL0'IsoToE'_symm (S : SliceSetup F)
    (h : S.L0' ≃ₗ[F] S.L0') (e' : S.paired.E') :
    projL1' S ((extendL0'IsoToE' S h).symm e') = projL1' S e' := by
  rw [extendL0'IsoToE'_symm_apply, map_add]
  -- projL1' (projL1' e' : E') = projL1' e', projL1' (h.symm _ : E') = 0.
  have h1 : projL1' S ((projL1' S e' : S.L1') : S.paired.E') = projL1' S e' := by
    unfold projL1'
    exact Submodule.linearProjOfIsCompl_apply_left S.isComplL' (projL1' S e')
  have h2 : projL1' S ((h.symm (projL0' S e') : S.L0') : S.paired.E') = 0 := by
    unfold projL1'
    exact Submodule.linearProjOfIsCompl_apply_right S.isComplL' (h.symm (projL0' S e'))
  rw [h1, h2, add_zero]

/-- `projL0' ∘ d.symm = h.symm ∘ projL0'`. -/
private lemma projL0'_extendL0'IsoToE'_symm (S : SliceSetup F)
    (h : S.L0' ≃ₗ[F] S.L0') (e' : S.paired.E') :
    projL0' S ((extendL0'IsoToE' S h).symm e') = h.symm (projL0' S e') := by
  rw [extendL0'IsoToE'_symm_apply, map_add]
  have h1 : projL0' S ((projL1' S e' : S.L1') : S.paired.E') = 0 := by
    unfold projL0'
    exact Submodule.linearProjOfIsCompl_apply_right S.isComplL'.symm (projL1' S e')
  have h2 : projL0' S ((h.symm (projL0' S e') : S.L0') : S.paired.E') =
      h.symm (projL0' S e') := by
    unfold projL0'
    exact Submodule.linearProjOfIsCompl_apply_left S.isComplL'.symm
      (h.symm (projL0' S e'))
  rw [h1, h2, zero_add]

/-- Forward extraction: from a parabolic `p` realising the conjugation
`p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`, extract the Levi `L0'`-block
`h : L0' ≃ₗ L0'` such that `BT T₂ (h u) (h v) = BT T₁ u v`.

**Round 7 strategy (Option B).** We bypass the `parabolic_decompose`
deferral by using:
* `IsParabolicElement` ⇒ `p` preserves `flagEV0 = E ⊕ V0 ⊕ 0`, so the
  third component of `p (e, v, e')` depends only on `e'` (the
  block-triangular structure).
* Conjugation `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` evaluated at `(0, 0, l)`
  for `l ∈ L0'` gives, via the `V0` component, that `p`'s `E'`-action
  preserves `L0'` (using `Sₕ` invertible).
* The L0'-action `h` is then read off from the third component, and the
  isometry `BT T₂ (h u) (h v) = BT T₁ u v` is checked from the same
  conjugation evaluated on a pair of L0'-vectors. -/
private theorem residual_levi_extract (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂)
    (p : Module.End F S.V) (_hP : IsParabolicElement S p)
    (_hConj : p ∘ₗ XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
              = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ ∘ₗ p) :
    Bilinear.AreIsometric (BT S T₁) (BT S T₂) := by
  -- Round 7 strategy (see `.archon/informal/normalform_round7.md` § Tier A #2):
  -- extract the Levi `L0'`-block from the conjugation, bypassing
  -- `parabolic_decompose`.
  obtain ⟨hpUnit, _hpFlagE, hpFlagEV0, hpIso⟩ := _hP
  -- Helper: evaluate the conjugation at `(0, 0, (l : E'))` for `l : L0'`.
  -- Yields key facts about the V0 and E components of `p (0, 0, (l : E'))`.
  have h_eval : ∀ (l : S.L0'),
      p ((((T₁ l : S.L0) : S.paired.E), (0 : S.V0), (0 : S.paired.E')) : S.V)
        = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂
            (p ((0, (0 : S.V0), ((l : S.paired.E') : S.paired.E')) : S.V)) := by
    intro l
    have hConj_l := congrArg
      (fun f : Module.End F S.V =>
        f ((0, (0 : S.V0), ((l : S.paired.E') : S.paired.E')) : S.V)) _hConj
    simp only [LinearMap.comp_apply] at hConj_l
    -- Compute XST(Sₕ, T₁) (0, 0, l) = (T₁ l : E, 0, 0).
    rw [XST_apply] at hConj_l
    have hp0 : projL0' S ((l : S.paired.E') : S.paired.E') = l := by
      unfold projL0'
      exact Submodule.linearProjOfIsCompl_apply_left S.isComplL'.symm l
    have hp1 : projL1' S ((l : S.paired.E') : S.paired.E') = 0 := by
      unfold projL1'
      exact Submodule.linearProjOfIsCompl_apply_right S.isComplL' l
    rw [hp0, hp1, map_zero] at hConj_l
    simp only [map_zero, zero_add, ZeroMemClass.coe_zero, add_zero] at hConj_l
    exact hConj_l
  -- Key Lemma 1: For l : L0', `(p (0, 0, l)).2.2 ∈ L0'`.
  -- This follows from the V0-component of h_eval: since `p ((T₁ l : E), 0, 0) ∈ flagE`
  -- (p preserves flagE), the V0-component of LHS equals 0. Hence
  -- `X0 v + (Sₕ (projL1' e') : V0) = 0`, where (a, v, e') := p (0, 0, l). Decomposing
  -- via Vplus ⊕ range X0 = V0 forces both terms to vanish. Sₕ injective then gives
  -- projL1' e' = 0, hence e' ∈ L0'.
  have h_in_L0' : ∀ (l : S.L0'),
      (p (((0 : S.paired.E), (0 : S.V0), ((l : S.paired.E') : S.paired.E')) : S.V)).2.2
        ∈ S.L0' := by
    intro l
    -- Extract V0-component equality from `h_eval`.
    have h := h_eval l
    -- p ((T₁ l : E), 0, 0) ∈ flagE (p preserves flagE since IsParabolicElement).
    have hpFlagE_mem : p (((T₁ l : S.L0) : S.paired.E), (0 : S.V0),
        (0 : S.paired.E')) ∈ S.flagE := by
      have : (((T₁ l : S.L0) : S.paired.E), (0 : S.V0),
          (0 : S.paired.E')) ∈ S.flagE := by
        refine ⟨trivial, ?_, ?_⟩ <;> simp
      have hPmap : Submodule.map p S.flagE = S.flagE := _hpFlagE
      rw [← hPmap]
      exact ⟨_, this, rfl⟩
    -- LHS V0-component is 0.
    have hLHS_V0 : (p (((T₁ l : S.L0) : S.paired.E), (0 : S.V0),
        (0 : S.paired.E'))).2.1 = 0 := by
      obtain ⟨_, hv, _⟩ := hpFlagE_mem
      simpa using hv
    -- Apply XST_apply to RHS.
    rw [XST_apply] at h
    -- h : p ((T₁ l : E), 0, 0) = (Cdual(...) v + (T₂ proj₀_₀ e' : E), X0 v + (Sₕ proj₁_₀ e' : V0), 0)
    -- where (a, v, e') := p (0, 0, l).
    have h_V0_comp := congrArg (fun x : S.V => x.2.1) h
    simp only at h_V0_comp
    rw [hLHS_V0] at h_V0_comp
    -- h_V0_comp : 0 = X0 v + (Sₕ (projL1' e') : V0).
    -- Decompose: both terms must be 0 (Vplus ⊕ range X0 disjoint).
    set v := (p ((0, (0 : S.V0), ((l : S.paired.E') : S.paired.E')))).2.1 with hv_def
    set e' := (p ((0, (0 : S.V0), ((l : S.paired.E') : S.paired.E')))).2.2 with he'_def
    have hSh_zero : ((Sₕ (projL1' S e') : S.Vplus) : S.V0) = 0 := by
      have h_eq : S.X0 v + ((Sₕ (projL1' S e') : S.Vplus) : S.V0) = 0 := h_V0_comp.symm
      have hX0_in_range : S.X0 v ∈ LinearMap.range S.X0 := ⟨v, rfl⟩
      have hSh_in_Vplus : ((Sₕ (projL1' S e') : S.Vplus) : S.V0) ∈ S.Vplus :=
        (Sₕ (projL1' S e')).2
      have hX0_eq : S.X0 v = -((Sₕ (projL1' S e') : S.Vplus) : S.V0) :=
        eq_neg_of_add_eq_zero_left h_eq
      have hX0_in_Vplus : S.X0 v ∈ S.Vplus := by
        rw [hX0_eq]; exact Submodule.neg_mem _ hSh_in_Vplus
      have hdisj : Disjoint S.Vplus (LinearMap.range S.X0) := S.isCompl.disjoint
      have hX0_zero : S.X0 v = 0 := by
        have hmem : S.X0 v ∈ S.Vplus ⊓ LinearMap.range S.X0 :=
          ⟨hX0_in_Vplus, hX0_in_range⟩
        rw [hdisj.eq_bot] at hmem
        exact (Submodule.mem_bot F).mp hmem
      rw [hX0_zero, zero_add] at h_eq
      exact h_eq
    -- Sₕ.injective ⇒ projL1' e' = 0.
    have hSh_zero' : (Sₕ (projL1' S e') : S.Vplus) = 0 :=
      Subtype.ext hSh_zero
    have h_proj_zero : projL1' S e' = 0 := by
      apply Sₕ.injective
      rw [hSh_zero', map_zero]
    -- projL1' e' = 0 ⇔ e' ∈ L0' (using IsCompl L1' L0').
    -- Specifically, e' = projL1' e' + projL0' e' = 0 + (projL0' e' : E') = (projL0' e' : E') ∈ L0'.
    have hsum :
        ((projL1' S e' : S.L1') : S.paired.E')
          + ((projL0' S e' : S.L0') : S.paired.E') = e' := by
      have hh := Submodule.IsCompl.projection_add_projection_eq_self
        S.isComplL' e'
      rw [Submodule.IsCompl.projection_apply S.isComplL' e',
          Submodule.IsCompl.projection_apply S.isComplL'.symm e'] at hh
      exact hh
    rw [h_proj_zero, ZeroMemClass.coe_zero, zero_add] at hsum
    rw [← hsum]
    exact (projL0' S e').2
  -- Now define qFun : L0' →ₗ L0' via codRestrict of `l ↦ (p (0, 0, l)).2.2`.
  let inE' : S.paired.E' →ₗ[F] S.V :=
    LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
      LinearMap.inr F S.V0 S.paired.E'
  let projE'_V : S.V →ₗ[F] S.paired.E' :=
    LinearMap.snd F S.V0 S.paired.E' ∘ₗ
      LinearMap.snd F S.paired.E (S.V0 × S.paired.E')
  let qFunRaw : S.L0' →ₗ[F] S.paired.E' :=
    projE'_V ∘ₗ p ∘ₗ inE' ∘ₗ S.L0'.subtype
  -- Show qFunRaw lands in L0'.
  have h_qFunRaw_in_L0' : ∀ l : S.L0', qFunRaw l ∈ S.L0' := by
    intro l
    have h := h_in_L0' l
    show (p ((0, 0, (l : S.paired.E')) : S.V)).2.2 ∈ S.L0'
    convert h using 1
  let qFun : S.L0' →ₗ[F] S.L0' := LinearMap.codRestrict S.L0' qFunRaw h_qFunRaw_in_L0'
  -- Step C: qFun is injective.
  have hq_inj : Function.Injective qFun := by
    rw [injective_iff_map_eq_zero]
    intro l hql
    -- qFun l = 0 ⇒ qFunRaw l = 0 ⇒ (p (0, 0, l)).2.2 = 0 ⇒ p (0, 0, l) ∈ flagEV0.
    have hraw : qFunRaw l = 0 := by
      have h_val : ((qFun l : S.L0') : S.paired.E') = 0 := by
        rw [hql]; rfl
      -- (qFun l : E') = qFunRaw l by codRestrict definition.
      exact h_val
    have hp_in_flagEV0 :
        p (((0 : S.paired.E), (0 : S.V0), ((l : S.paired.E') : S.paired.E')) : S.V)
          ∈ S.flagEV0 := by
      refine ⟨trivial, trivial, ?_⟩
      change (p ((0, 0, (l : S.paired.E')) : S.V)).2.2 ∈ (⊥ : Submodule F S.paired.E')
      rw [Submodule.mem_bot]
      show (p ((0, 0, (l : S.paired.E')) : S.V)).2.2 = 0
      have : qFunRaw l = (p ((0, (0 : S.V0), ((l : S.paired.E') : S.paired.E')) : S.V)).2.2 :=
        rfl
      rw [← this]; exact hraw
    -- p preserves flagEV0 (equality), so by invertibility, p_inv preserves flagEV0.
    -- Hence (0, 0, l) = p_inv (p (0, 0, l)) ∈ p_inv flagEV0 ≤ flagEV0.
    -- So third coord is 0, i.e., l = 0.
    have hpFlagEV0_eq : Submodule.map p S.flagEV0 = S.flagEV0 := hpFlagEV0
    -- Build p_inv from hpUnit.
    obtain ⟨pUnit, hpUnit_eq⟩ := hpUnit
    -- pUnit : (Module.End F S.V)ˣ, hpUnit_eq : (pUnit : Module.End F S.V) = p.
    have hpu_eq_p : (pUnit : Module.End F S.V) = p := hpUnit_eq
    -- Apply p_inv := pUnit.inv to both sides.
    have h_orig : p (((0 : S.paired.E), (0 : S.V0),
        ((l : S.paired.E') : S.paired.E')) : S.V) =
        ((pUnit : Module.End F S.V)) ((0, (0 : S.V0),
          ((l : S.paired.E') : S.paired.E')) : S.V) := by
      rw [hpu_eq_p]
    have hpinv_p : ((pUnit.inv : Module.End F S.V) ∘ₗ
        (pUnit : Module.End F S.V)) = LinearMap.id := by
      have : pUnit.inv * (pUnit : Module.End F S.V) = 1 := pUnit.inv_val
      exact this
    have h_zero_in_FEV0 :
        (((0 : S.paired.E), (0 : S.V0), ((l : S.paired.E') : S.paired.E')) : S.V)
          ∈ S.flagEV0 := by
      -- pUnit⁻¹ (p (0, 0, l)) = (0, 0, l). And pUnit⁻¹ (flagEV0) ≤ flagEV0.
      have hp_eq :
          ((pUnit.inv : Module.End F S.V))
              (p (((0 : S.paired.E), (0 : S.V0),
                ((l : S.paired.E') : S.paired.E')) : S.V))
            = (((0 : S.paired.E), (0 : S.V0),
                ((l : S.paired.E') : S.paired.E')) : S.V) := by
        rw [h_orig]
        have := congrArg
          (fun f : Module.End F S.V => f ((0, (0 : S.V0),
            ((l : S.paired.E') : S.paired.E')) : S.V)) hpinv_p
        simpa using this
      -- pUnit⁻¹ maps flagEV0 to flagEV0.
      have hinv_FEV0 : ∀ x ∈ S.flagEV0, (pUnit.inv : Module.End F S.V) x ∈ S.flagEV0 := by
        intro x hx
        -- From hpFlagEV0_eq : map p flagEV0 = flagEV0, surjectivity of p|flagEV0.
        rw [← hpFlagEV0_eq] at hx
        obtain ⟨y, hy_in, hy_eq⟩ := hx
        -- y ∈ flagEV0 with p y = x.
        have : (pUnit.inv : Module.End F S.V) x = y := by
          rw [← hy_eq, ← hpu_eq_p]
          have := congrArg
            (fun f : Module.End F S.V => f y) hpinv_p
          simpa using this
        rw [this]; exact hy_in
      rw [← hp_eq]
      exact hinv_FEV0 _ hp_in_flagEV0
    obtain ⟨_, _, hl_in_bot⟩ := h_zero_in_FEV0
    have hl_zero : ((l : S.paired.E') : S.paired.E') = 0 := by
      change ((l : S.paired.E') : S.paired.E') ∈ (⊥ : Submodule F S.paired.E') at hl_in_bot
      exact (Submodule.mem_bot F).mp hl_in_bot
    apply Subtype.ext
    show ((l : S.paired.E') : S.paired.E') = ((0 : S.L0') : S.paired.E')
    rw [hl_zero]; rfl
  -- Step D: lift qFun to a LinearEquiv (injective + same dim ⇒ bijective).
  have hdim_eq : Module.finrank F S.L0' = Module.finrank F S.L0' := rfl
  let h : S.L0' ≃ₗ[F] S.L0' := LinearMap.linearEquivOfInjective qFun hq_inj hdim_eq
  -- Step E: verify isometry condition `BT T₂ (h u) (h v) = BT T₁ u v`.
  refine ⟨h, ?_⟩
  intro u v
  -- Use the IsOrthogonal conjunct of p applied to (T₁ u : E, 0, 0) and (0, 0, (v : E')).
  -- Compute p (T₁ u : E, 0, 0) and p (0, 0, (v : E')).
  -- Use the hypothesis: S.ambientForm (p x) (p y) = S.ambientForm x y.
  -- Choose x := (T₁ u : E, 0, 0), y := (0, 0, (v : E')).
  -- LHS: S.ambientForm (p (T₁ u : E, 0, 0)) (p (0, 0, v)).
  --    p (T₁ u : E, 0, 0) ∈ flagE (preserved by p), so it's of form (e_p, 0, 0).
  --    p (0, 0, v) = (a_v, c_v, e'_v) with e'_v = (h v : E') (Step A).
  --    ambientForm ((e_p, 0, 0), (a_v, c_v, e'_v))
  --      = λ(e_p, e'_v) + B0(0, c_v) + ε * λ(a_v, 0)
  --      = λ(e_p, (h v : E')) + 0 + 0
  --      = λ(e_p) (h v : E').
  -- RHS: S.ambientForm ((T₁ u : E, 0, 0), (0, 0, (v : E'))) = λ(T₁ u, v) + 0 + 0 = BT T₁ u v.
  -- So λ(e_p) (h v : E') = BT T₁ u v.
  -- We also have h_eval u: p (T₁ u : E, 0, 0) = XST(T₂) (p (0, 0, u)).
  --    Equating E-component: e_p = Cdual(CST Sₕ) c_u + (T₂ (h u) : E).
  --    Plugging in: λ(Cdual(CST Sₕ) c_u + (T₂ (h u) : E)) (h v : E') = BT T₁ u v.
  --    Use Cdual_pairing_eq + (h v ∈ L0' ⇒ projL1' (h v : E') = 0 ⇒ CST Sₕ vanishes on h v)
  --    to drop the Cdual term, leaving:
  --    λ(T₂ (h u) : E) (h v : E') = BT T₁ u v.
  --    But LHS = BT T₂ (h u) (h v) by definition.
  have hOrth := hpIso
      ((((T₁ u : S.L0) : S.paired.E), (0 : S.V0), (0 : S.paired.E')) : S.V)
      ((0, (0 : S.V0), ((v : S.paired.E') : S.paired.E')) : S.V)
  -- Compute RHS of hOrth: ambientForm ((T₁ u : E, 0, 0), (0, 0, v)) = λ(T₁ u, v).
  have hRHS : S.ambientForm
      ((((T₁ u : S.L0) : S.paired.E), (0 : S.V0), (0 : S.paired.E')) : S.V)
      ((0, (0 : S.V0), ((v : S.paired.E') : S.paired.E')) : S.V)
        = S.lambda ((T₁ u : S.L0) : S.paired.E) ((v : S.paired.E') : S.paired.E') := by
    show S.paired.pairing ((T₁ u : S.L0) : S.paired.E)
            ((v : S.paired.E') : S.paired.E') + S.formV0 0 0
            + S.eps * S.paired.pairing 0 0 = _
    simp
  rw [hRHS] at hOrth
  -- LHS of hOrth: compute via h_eval, substituting p (T₁ u, 0, 0).
  have h_eval_u := h_eval u
  -- h_eval_u : p (T₁ u : E, 0, 0) = XST(Sₕ, T₂) (p (0, 0, u))
  rw [h_eval_u] at hOrth
  -- Now LHS of hOrth = ambientForm (XST(Sₕ, T₂) (p (0, 0, u))) (p (0, 0, v)).
  -- Use XST_apply to expand.
  rw [show XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂
        (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V))
      = (Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus))
            (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).2.1
          + (T₂ (projL0' S
              (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).2.2) : S.paired.E),
        S.X0 (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).2.1
          + (Sₕ (projL1' S
              (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).2.2) : S.V0),
        0) from XST_apply S _ _ _ _ _] at hOrth
  -- Set up shorthands.
  set a_u := (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).1 with ha_u_def
  set c_u := (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).2.1 with hc_u_def
  set e'_u := (p ((0, (0 : S.V0), ((u : S.paired.E') : S.paired.E')) : S.V)).2.2 with he'_u_def
  set a_v := (p ((0, (0 : S.V0), ((v : S.paired.E') : S.paired.E')) : S.V)).1 with ha_v_def
  set c_v := (p ((0, (0 : S.V0), ((v : S.paired.E') : S.paired.E')) : S.V)).2.1 with hc_v_def
  set e'_v := (p ((0, (0 : S.V0), ((v : S.paired.E') : S.paired.E')) : S.V)).2.2 with he'_v_def
  -- h u = ⟨e'_u, h_in_L0' u⟩, similarly for v. (These are `(h u : L0').val = e'_u`.)
  have h_u_val : ((h u : S.L0') : S.paired.E') = e'_u := by
    show qFunRaw u = e'_u
    rfl
  have h_v_val : ((h v : S.L0') : S.paired.E') = e'_v := by
    show qFunRaw v = e'_v
    rfl
  -- Now compute LHS of hOrth.
  -- LHS = ambientForm (XST_RHS) (a_v, c_v, e'_v)
  --     = λ((Cdual(CST Sₕ) c_u) + (T₂ (projL0' e'_u) : E), e'_v) + B0((X0 c_u + Sₕ projL1' e'_u : V0), c_v) + ε * λ(a_v, 0).
  -- Last term is 0.
  -- e'_u ∈ L0' (h_in_L0' u), so projL0' e'_u = ⟨e'_u, ...⟩ as L0' element, and projL1' e'_u = 0.
  have h_e'u_in_L0' : e'_u ∈ S.L0' := h_in_L0' u
  have h_e'v_in_L0' : e'_v ∈ S.L0' := h_in_L0' v
  have h_proj_e'u_L1' : projL1' S e'_u = 0 := by
    unfold projL1'
    exact Submodule.linearProjOfIsCompl_apply_right' S.isComplL' _ h_e'u_in_L0'
  have h_proj_e'u_L0' : (projL0' S e'_u : S.paired.E') = e'_u := by
    show ((Submodule.linearProjOfIsCompl S.L0' S.L1' S.isComplL'.symm e'_u :
            S.L0') : S.paired.E') = e'_u
    rw [Submodule.linearProjOfIsCompl_apply_left S.isComplL'.symm ⟨e'_u, h_e'u_in_L0'⟩]
  -- Similarly for v.
  have h_proj_e'v_L1' : projL1' S e'_v = 0 := by
    unfold projL1'
    exact Submodule.linearProjOfIsCompl_apply_right' S.isComplL' _ h_e'v_in_L0'
  have h_proj_e'v_L0' : (projL0' S e'_v : S.paired.E') = e'_v := by
    show ((Submodule.linearProjOfIsCompl S.L0' S.L1' S.isComplL'.symm e'_v :
            S.L0') : S.paired.E') = e'_v
    rw [Submodule.linearProjOfIsCompl_apply_left S.isComplL'.symm ⟨e'_v, h_e'v_in_L0'⟩]
  rw [h_proj_e'u_L1', map_zero, ZeroMemClass.coe_zero, add_zero] at hOrth
  -- The V0-part of XST: X0 c_u + 0 = X0 c_u. But we need to use this is 0 (from h_in_L0' u proof).
  -- Actually, from the h_in_L0' u proof, we showed X0 c_u = 0. Let me re-derive that.
  have h_X0_c_u_zero : S.X0 c_u = 0 := by
    -- From h_eval u : p (T₁ u : E, 0, 0) = XST T₂ (p (0, 0, u)).
    -- The V0 component: 0 = X0 c_u + (Sₕ (projL1' e'_u) : V0).
    -- We have projL1' e'_u = 0, so Sₕ proj = 0, so X0 c_u = 0.
    have h_eu := h_eval u
    rw [XST_apply] at h_eu
    -- p (T₁ u, 0, 0) ∈ flagE so V0 component is 0.
    have hpFlagE_mem_u : p (((T₁ u : S.L0) : S.paired.E), (0 : S.V0),
        (0 : S.paired.E')) ∈ S.flagE := by
      have : (((T₁ u : S.L0) : S.paired.E), (0 : S.V0),
          (0 : S.paired.E')) ∈ S.flagE := by
        refine ⟨trivial, ?_, ?_⟩ <;> simp
      have hPmap : Submodule.map p S.flagE = S.flagE := _hpFlagE
      rw [← hPmap]
      exact ⟨_, this, rfl⟩
    have hLHS_V0_u : (p (((T₁ u : S.L0) : S.paired.E), (0 : S.V0),
        (0 : S.paired.E'))).2.1 = 0 := by
      obtain ⟨_, hv', _⟩ := hpFlagE_mem_u
      simpa using hv'
    have h_V0_eq := congrArg (fun x : S.V => x.2.1) h_eu
    simp only at h_V0_eq
    rw [hLHS_V0_u] at h_V0_eq
    rw [h_proj_e'u_L1', map_zero, ZeroMemClass.coe_zero, add_zero] at h_V0_eq
    show S.X0 c_u = 0
    exact h_V0_eq.symm
  rw [h_X0_c_u_zero] at hOrth
  -- Hmm... actually this rewrite affects only the (X0 c_u + ...) part inside hOrth.
  -- Let's see what hOrth looks like now and continue.
  -- hOrth: ambientForm (Cdual(CST Sₕ) c_u + T₂ (projL0' e'_u : L0') : E,
  --                    (Sₕ (projL1' e'_u) : V0)  -- this is 0, but the rewrite above
  --                                                 might be confused
  --                    , 0)
  --                   (a_v, c_v, e'_v) = λ(T₁ u, v).
  -- Honestly this is too painful to track in comments. Let me re-derive.
  -- After both rewrites, the LHS expression in XST(...) has form:
  -- (Cdual(CST Sₕ) c_u + (T₂ (projL0' e'_u : L0') : E), 0, 0).
  -- (V0 = X0 c_u + Sₕ (projL1' e'_u : V0) = 0 + 0 = 0.
  --  E' = 0.)
  -- Hmm but we already simplified projL1' e'_u to 0 and X0 c_u to 0. So the V0 component of the XST RHS in hOrth should now be 0.
  -- ambientForm ((Cdual(...) c_u + T₂ ... : E, 0, 0), (a_v, c_v, e'_v))
  --   = λ(Cdual c_u + T₂ ... , e'_v) + B0(0, c_v) + ε * λ(a_v, 0)
  --   = λ(Cdual c_u, e'_v) + λ(T₂ ..., e'_v) + 0 + 0.
  -- λ(Cdual c_u, e'_v) = -B0(c_u, CST Sₕ e'_v) by Cdual_pairing_eq.
  -- CST Sₕ e'_v = Vplus.subtype ∘ Sₕ ∘ projL1' e'_v.
  -- projL1' e'_v = 0 (since e'_v ∈ L0'), so CST Sₕ e'_v = 0.
  -- So λ(Cdual c_u, e'_v) = 0.
  -- λ(T₂ (projL0' e'_u : L0') : E, e'_v) = ?
  -- projL0' e'_u : L0' has value e'_u (since e'_u ∈ L0'). So T₂ (projL0' e'_u) = T₂ ⟨e'_u, ...⟩ = T₂ (h u).
  -- λ((T₂ (h u) : E), e'_v) = λ((T₂ (h u) : E), (h v : E')) (using h_v_val).
  -- = BT T₂ (h u) (h v) by definition.
  -- And RHS of hOrth = λ(T₁ u, v) = BT T₁ u v.
  -- So BT T₂ (h u) (h v) = BT T₁ u v. ✓
  --
  -- Implementation:
  show BT S T₂ (h u) (h v) = BT S T₁ u v
  -- Unfold both BT.
  show S.lambda ((T₂ (h u) : S.L0) : S.paired.E)
          (((h v : S.L0') : S.paired.E') : S.paired.E')
      = S.lambda ((T₁ u : S.L0) : S.paired.E) ((v : S.paired.E') : S.paired.E')
  rw [h_v_val]
  -- Goal: λ((T₂ (h u) : E)) e'_v = λ((T₁ u : E)) v.
  -- From hOrth, we know after simplifications that:
  -- ambientForm (XST_RHS) (a_v, c_v, e'_v) = λ((T₁ u : E)) v.
  -- where XST_RHS = (Cdual c_u + T₂ ...,  0,  0) after the rewrites we did.
  -- Compute the ambientForm explicitly.
  have h_proj_e'u_L0'_subt :
      ((Submodule.linearProjOfIsCompl S.L0' S.L1' S.isComplL'.symm e'_u : S.L0')
        : S.paired.E') = e'_u := h_proj_e'u_L0'
  -- Rewrite hOrth's ambientForm via its definition (without `set`).
  have h_amb_unfold :
      S.ambientForm
          ((Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) c_u
              + ((T₂ (projL0' S e'_u) : S.L0) : S.paired.E),
            (0 : S.V0), (0 : S.paired.E')))
          (p ((0, (0 : S.V0), ((v : S.paired.E') : S.paired.E')) : S.V))
        = S.paired.pairing
            (Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) c_u
              + ((T₂ (projL0' S e'_u) : S.L0) : S.paired.E)) e'_v
            + S.formV0 (0 : S.V0) c_v
            + S.eps * S.paired.pairing a_v (0 : S.paired.E') := rfl
  rw [h_amb_unfold] at hOrth
  -- Now hOrth: λ((Cdual + T₂ ...) , e'_v) + B0(0, c_v) + ε * λ(a_v, 0) = λ(T₁ u, v).
  rw [LinearMap.map_zero, LinearMap.zero_apply, map_zero, add_zero, mul_zero,
    add_zero] at hOrth
  -- Now hOrth: λ((Cdual c_u + (T₂ projL0' e'_u : E))) e'_v = λ((T₁ u : E)) v.
  rw [LinearMap.map_add, LinearMap.add_apply] at hOrth
  -- hOrth: λ(Cdual(CST Sₕ) c_u, e'_v) + λ(T₂ (projL0' e'_u : L0') : E, e'_v) = λ(T₁ u, v).
  -- λ(Cdual(CST Sₕ) c_u, e'_v) = -formV0 c_u (CST Sₕ e'_v) by Cdual_pairing_eq.
  -- CST Sₕ e'_v = Vplus.subtype (Sₕ (projL1' e'_v)) = Vplus.subtype (Sₕ 0) = 0.
  have h_CST_e'v : (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) e'_v = 0 := by
    show (S.Vplus.subtype ∘ₗ (Sₕ : S.L1' →ₗ[F] S.Vplus) ∘ₗ projL1' S) e'_v = 0
    simp only [LinearMap.comp_apply, h_proj_e'v_L1', map_zero]
  have h_Cdual_term :
      S.lambda (Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) c_u) e'_v = 0 := by
    rw [Cdual_pairing_eq S _hNondeg, h_CST_e'v, map_zero, neg_zero]
  rw [h_Cdual_term, zero_add] at hOrth
  -- hOrth: λ(T₂ (projL0' e'_u : L0') : E, e'_v) = λ(T₁ u : E, v).
  -- projL0' e'_u : L0' has value e'_u, which equals (h u : E') by h_u_val.
  have h_projL0'_eq : projL0' S e'_u = h u := by
    apply Subtype.ext
    rw [h_proj_e'u_L0', ← h_u_val]
  rw [h_projL0'_eq] at hOrth
  exact hOrth

/-- Backward construction: from an isometry `h : L0' ≃ₗ L0'` of
`(BT T₁) ↦ (BT T₂)`, construct a parabolic `p ∈ Module.End F S.V`
realising the conjugation `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`.

**Round 7 strategy.** Take `p := leviGL_E S d` for
`d := extendL0'IsoToE' S h` (the Levi block extending `h` by `id` on
`L1'`). Parabolicity follows from `leviGL_E_isParabolic`. The
conjugation reduces via `leviGL_E_conj_XCB` to the two-component
identity `(CST Sₕ ∘ d.symm = CST Sₕ)` and
`(lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂)`, the latter being the
residue of the isometry hypothesis `hh`. -/
private theorem residual_levi_build (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂)
    (h : S.L0' ≃ₗ[F] S.L0') (hh : ∀ u v, BT S T₂ (h u) (h v) = BT S T₁ u v) :
    ∃ (p : Module.End F S.V), IsParabolicElement S p ∧
      p ∘ₗ XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
        = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ ∘ₗ p := by
  -- Build `d : E' ≃ E'` extending `h` by id on L1'.
  let d : S.paired.E' ≃ₗ[F] S.paired.E' := extendL0'IsoToE' S h
  -- Take p := leviGL_E S d.
  refine ⟨leviGL_E S d, leviGL_E_isParabolic S d, ?_⟩
  -- Component identity 1: CST Sₕ ∘ d.symm = CST Sₕ
  have h_C : CST S (Sₕ : S.L1' →ₗ[F] S.Vplus) ∘ₗ
        (d.symm : S.paired.E' →ₗ[F] S.paired.E')
      = CST S (Sₕ : S.L1' →ₗ[F] S.Vplus) := by
    apply LinearMap.ext
    intro e0
    show (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus))
            ((d.symm : S.paired.E' →ₗ[F] S.paired.E') e0)
        = (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) e0
    show (S.Vplus.subtype ∘ₗ (Sₕ : S.L1' →ₗ[F] S.Vplus) ∘ₗ projL1' S)
            ((d.symm : S.paired.E' →ₗ[F] S.paired.E') e0)
        = (S.Vplus.subtype ∘ₗ (Sₕ : S.L1' →ₗ[F] S.Vplus) ∘ₗ projL1' S) e0
    simp only [LinearMap.comp_apply]
    rw [show ((d.symm : S.paired.E' →ₗ[F] S.paired.E') e0)
          = (extendL0'IsoToE' S h).symm e0 from rfl]
    rw [show projL1' S ((extendL0'IsoToE' S h).symm e0) = projL1' S e0 from
        projL1'_extendL0'IsoToE'_symm S h e0]
  -- Component identity 2: lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂.
  have h_B : lambdaDualE S (d.symm : S.paired.E' →ₗ[F] S.paired.E')
        ∘ₗ BST S T₁
        ∘ₗ (d.symm : S.paired.E' →ₗ[F] S.paired.E')
      = BST S T₂ := by
    apply LinearMap.ext
    intro e0
    -- Step A: simplify projL0' (d.symm e0) = h.symm (projL0' e0).
    have hp0_dsym : projL0' S ((d.symm : S.paired.E' →ₗ[F] S.paired.E') e0)
        = h.symm (projL0' S e0) := by
      show projL0' S ((extendL0'IsoToE' S h).symm e0) = h.symm (projL0' S e0)
      exact projL0'_extendL0'IsoToE'_symm S h e0
    -- Reduce LHS step-by-step.
    show lambdaDualE S (d.symm : S.paired.E' →ₗ[F] S.paired.E')
            ((BST S T₁ ∘ₗ (d.symm : S.paired.E' →ₗ[F] S.paired.E')) e0)
        = BST S T₂ e0
    simp only [LinearMap.comp_apply]
    have hBST_T₁ : BST S T₁ ((d.symm : S.paired.E' →ₗ[F] S.paired.E') e0)
        = ((T₁ (h.symm (projL0' S e0)) : S.L0) : S.paired.E) := by
      show (S.L0.subtype ∘ₗ T₁ ∘ₗ projL0' S)
            ((d.symm : S.paired.E' →ₗ[F] S.paired.E') e0)
          = ((T₁ (h.symm (projL0' S e0)) : S.L0) : S.paired.E)
      simp only [LinearMap.comp_apply, hp0_dsym]
      rfl
    rw [hBST_T₁]
    -- BST T₂ e0 = (T₂ (projL0' e0) : E).
    show lambdaDualE S (d.symm : S.paired.E' →ₗ[F] S.paired.E')
            ((T₁ (h.symm (projL0' S e0)) : S.L0) : S.paired.E)
        = (S.L0.subtype ∘ₗ T₂ ∘ₗ projL0' S) e0
    simp only [LinearMap.comp_apply]
    show lambdaDualE S (d.symm : S.paired.E' →ₗ[F] S.paired.E')
            ((T₁ (h.symm (projL0' S e0)) : S.L0) : S.paired.E)
        = ((T₂ (projL0' S e0) : S.L0) : S.paired.E)
    -- Use perfect pairing: check pairing with all e''.
    apply S.paired.isPerfect.1
    apply LinearMap.ext
    intro e''
    rw [lambdaDualE_pairing_eq]
    -- Decompose e'' via the IsCompl decomposition.
    have he'' : (((projL1' S e'' : S.L1') : S.paired.E')
                  + ((projL0' S e'' : S.L0') : S.paired.E') : S.paired.E') = e'' := by
      have hcompl := Submodule.IsCompl.projection_add_projection_eq_self
        S.isComplL' e''
      rw [Submodule.IsCompl.projection_apply S.isComplL' e'',
          Submodule.IsCompl.projection_apply S.isComplL'.symm e''] at hcompl
      exact hcompl
    have hdsym_e'' : (d.symm : S.paired.E' →ₗ[F] S.paired.E') e''
        = ((projL1' S e'' : S.L1') : S.paired.E')
            + ((h.symm (projL0' S e'') : S.L0') : S.paired.E') := by
      show (extendL0'IsoToE' S h).symm e'' = _
      rw [extendL0'IsoToE'_symm_apply]
    rw [hdsym_e'']
    -- λ(T₁ ∘ h.symm proj : L0, [a' + h.symm b' : E']) = λ(...)(a') + λ(...)(h.symm b').
    rw [map_add]
    -- Split RHS via the e'' decomposition.
    conv_rhs => rw [← he'', map_add]
    -- λ(T₁(h.symm u) : L0 ↪ E, projL1' e'' : L1' ↪ E') = 0 by L0 ⊥ L1'.
    have h_L0_L1'_a :
        S.lambda ((T₁ (h.symm (projL0' S e0)) : S.L0) : S.paired.E)
            ((projL1' S e'' : S.L1') : S.paired.E') = 0 :=
      S.L0_isotropic_L1' _ (T₁ (h.symm (projL0' S e0))).2
        _ (projL1' S e'').2
    have h_L0_L1'_b :
        S.lambda ((T₂ (projL0' S e0) : S.L0) : S.paired.E)
            ((projL1' S e'' : S.L1') : S.paired.E') = 0 :=
      S.L0_isotropic_L1' _ (T₂ (projL0' S e0)).2
        _ (projL1' S e'').2
    rw [h_L0_L1'_a, h_L0_L1'_b, zero_add, zero_add]
    -- Now: λ(T₁(h.symm u), h.symm b' : E') = λ(T₂ u, b' : E') with
    -- u := projL0' e0, b' := projL0' e''. This is BT T₁ (h.symm u) (h.symm b')
    -- = BT T₂ u b', which follows from hh by substituting u → h.symm u and
    -- v → h.symm b'.
    have hkey' := hh (h.symm (projL0' S e0)) (h.symm (projL0' S e''))
    simp only [LinearEquiv.apply_symm_apply] at hkey'
    have hBT_T₁ : BT S T₁ (h.symm (projL0' S e0)) (h.symm (projL0' S e''))
        = S.lambda ((T₁ (h.symm (projL0' S e0)) : S.L0) : S.paired.E)
            ((h.symm (projL0' S e'') : S.L0') : S.paired.E') := by
      unfold BT; simp [LinearMap.mk₂_apply]
    have hBT_T₂ : BT S T₂ (projL0' S e0) (projL0' S e'')
        = S.lambda ((T₂ (projL0' S e0) : S.L0) : S.paired.E)
            ((projL0' S e'' : S.L0') : S.paired.E') := by
      unfold BT; simp [LinearMap.mk₂_apply]
    rw [← hBT_T₁, ← hBT_T₂]
    exact hkey'.symm
  -- Now combine: leviGL_E d ∘ XCB(CST Sₕ, BST T₁) = XCB(CST Sₕ, BST T₂) ∘ leviGL_E d.
  show leviGL_E S d ∘ₗ XCB S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) (BST S T₁)
      = XCB S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) (BST S T₂) ∘ₗ leviGL_E S d
  rw [leviGL_E_conj_XCB S d]
  rw [h_C, h_B]

/-- `prop:p-normal-form` (residual-orbit isometry).  Two normalised
representatives `XST S Sₕ T₁` and `XST S Sₕ T₂` are `P`-conjugate iff their
residual bilinear forms `BT S T₁` and `BT S T₂` are isometric.

Blueprint outline (`references/blueprint_verified.md` §`prop:p-normal-form`,
items 3 and surrounding text):

* **(→)** Given a parabolic `p` with `p XST(Sₕ, T₁) = XST(Sₕ, T₂) p`,
  the action on the `L_0 ⊕ L_0'` block descends to a Levi factor
  `h : L_0' ≃ₗ L_0'`. The residual transformation law is
  `T₂ = (h⁻¹)^∨ T₁ h`, so `BT T₂ (h u) (h v) = BT T₁ u v` for all `u v`.
  This produces the required `Bilinear.AreIsometric` witness.
* **(←)** Given an isometry `h : L_0' ≃ₗ L_0'` of `(BT T₁) ↦ (BT T₂)`,
  build a parabolic `p ∈ Module.End F S.V` acting as `(h⁻¹)^∨ ⊕ id ⊕ h`
  on the block decomposition `V = L_1 ⊕ L_0 ⊕ V_0 ⊕ L_1' ⊕ L_0'`.
  The conjugation calculation reduces to checking the diagonal blocks
  using `XST_apply` and the isometry condition.

Both directions are factored through `residual_levi_extract` and
`residual_levi_build`. The Round 7 prover refactored `Sₕ` from a bare
`LinearMap` to a `LinearEquiv` (`L1' ≃ₗ Vplus`) here and in the helpers
because the (←) direction's Levi `d`-construction needs `Sₕ.symm`, and
the (→) direction's `kernelImage_ker`-style argument needs `Sₕ`
injective. -/
theorem pNormalForm_residual_orbit_iso
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0) (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂) :
    (∃ (p : Module.End F S.V), IsParabolicElement S p ∧
        p ∘ₗ XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
          = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ ∘ₗ p) ↔
      Bilinear.AreIsometric (BT S T₁) (BT S T₂) := by
  refine ⟨?_, ?_⟩
  · -- (→) Forward: from parabolic conjugation, extract isometry.
    rintro ⟨p, hP, hConj⟩
    exact residual_levi_extract S _hNondeg _hChar Sₕ T₁ T₂ _hT₁ _hT₂ p hP hConj
  · -- (←) Backward: from isometry, build parabolic conjugation.
    rintro ⟨h, hh⟩
    exact residual_levi_build S _hNondeg _hChar Sₕ T₁ T₂ _hT₁ _hT₂ h hh

/-! ## Theorem `prop:kernel-image` -/

/-- The kernel of `XST S Sₕ T`, encoded as a submodule of
`S.V = E × V₀ × E'` that morally equals `E ⊕ 0 ⊕ ker T` — the full `E`
factor, the trivial `V₀` factor, and the `L0'`-summand of `E'` restricted
to `ker T`. -/
noncomputable def kerXST_submod
    (_Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) :
    Submodule F S.V :=
  Submodule.prod ⊤
    (Submodule.prod ⊥
      ((LinearMap.ker T).map S.L0'.subtype))

/-- The "easy" direction of `kernelImage_ker`: `kerXST_submod ⊆ ker XST`. This
direction is fully constructive: any `(e, 0, (l : E'))` with `l ∈ L0'` and
`T l = 0` is in the kernel by direct computation. -/
private theorem kerXST_submod_le_ker (Sₕ : S.L1' →ₗ[F] S.Vplus)
    (T : S.L0' →ₗ[F] S.L0) :
    kerXST_submod S Sₕ T ≤ LinearMap.ker (XST S Sₕ T) := by
  intro x hx
  obtain ⟨e, v, e'⟩ := x
  -- Decode membership of x in `kerXST_submod`.
  rw [kerXST_submod, Submodule.mem_prod, Submodule.mem_prod] at hx
  obtain ⟨_, hv, he'⟩ := hx
  -- `hv : v ∈ ⊥` forces `v = 0`.
  change v ∈ (⊥ : Submodule F S.V0) at hv
  have hv0 : v = 0 := (Submodule.mem_bot F).1 hv
  -- `he' : e' ∈ map L0'.subtype (ker T)` gives a witness `l ∈ L0' ∩ ker T`.
  change e' ∈ (LinearMap.ker T).map S.L0'.subtype at he'
  rw [Submodule.mem_map] at he'
  obtain ⟨l, hl_ker, hl_eq⟩ := he'
  -- e' = S.L0'.subtype l = (l : E')
  have hl_eq' : (l : S.E') = e' := hl_eq
  -- Compute `XST(e, 0, e') = 0` via `XST_apply`.
  rw [LinearMap.mem_ker, XST_apply]
  subst hv0
  -- After v = 0: result is `(Cdual(CST Sₕ) 0 + T(projL0' e'), X0 0 + Sₕ(projL1' e'), 0)`.
  simp only [map_zero, zero_add]
  -- projL0' (l : E') = l (as L0' element), and projL1' (l : E') = 0.
  have hp0 : projL0' S e' = l := by
    rw [← hl_eq']
    unfold projL0'
    exact Submodule.linearProjOfIsCompl_apply_left S.isComplL'.symm l
  have hp1 : projL1' S e' = 0 := by
    rw [← hl_eq']
    unfold projL1'
    exact Submodule.linearProjOfIsCompl_apply_right S.isComplL' l
  rw [hp0, hp1, map_zero]
  -- Now: T l = 0 (from ker T)
  have hTl0 : T l = 0 := hl_ker
  rw [hTl0]
  ext <;> simp

/-- For any `v : S.V0` and any `Sₕ : S.L1' →ₗ[F] S.Vplus`, the dual transpose
`Cdual S (CST S Sₕ) v` lies in `S.L1`.

Reason: `(CST S Sₕ)` vanishes on `L0'` (since `projL1'` is zero on `L0'`), so
by `Cdual_pairing_eq`, `λ(Cdual S (CST S Sₕ) v, l') = -formV0 v ((CST S Sₕ) l')
= 0` for every `l' ∈ L0'`. Decomposing `Cdual S (CST S Sₕ) v = a + b` along
`IsCompl L1 L0`, the `L1`-part `a` pairs to zero with `L0'` by
`L1_isotropic_L0'`, forcing the `L0`-part `b` to also pair to zero with `L0'`,
hence `b = 0` by the perfect pairing `L0_paired`. -/
private lemma Cdual_CST_mem_L1 (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (v : S.V0) :
    Cdual S (CST S Sₕ) v ∈ S.L1 := by
  -- Step 1: λ(Cdual(CST Sₕ) v, l') = 0 for all l' ∈ L0'.
  have h_pair_L0' :
      ∀ l' ∈ S.L0', S.lambda (Cdual S (CST S Sₕ) v) l' = 0 := by
    intro l' hl'
    have hCST_zero : (CST S Sₕ) l' = 0 := by
      show (S.Vplus.subtype ∘ₗ Sₕ ∘ₗ projL1' S) l' = 0
      simp only [LinearMap.comp_apply]
      have hp : projL1' S l' = 0 := by
        unfold projL1'
        exact Submodule.linearProjOfIsCompl_apply_right' S.isComplL' l' hl'
      rw [hp, map_zero]
      rfl
    rw [Cdual_pairing_eq S hNondeg, hCST_zero, map_zero, neg_zero]
  -- Step 2: Decompose Cdual(CST Sₕ) v ∈ L1 ⊔ L0 = ⊤.
  have h_top : Cdual S (CST S Sₕ) v ∈ (⊤ : Submodule F S.E) :=
    Submodule.mem_top
  rw [← S.isComplL.codisjoint.eq_top, Submodule.mem_sup] at h_top
  obtain ⟨a, ha, b, hb, hsum⟩ := h_top
  -- Step 3: λ(b, l') = 0 for all l' ∈ L0'.
  have h_pair_b : ∀ l' ∈ S.L0', S.lambda b l' = 0 := by
    intro l' hl'
    have h_a : S.lambda a l' = 0 := S.L1_isotropic_L0' a ha l' hl'
    have h_x : S.lambda (Cdual S (CST S Sₕ) v) l' = 0 := h_pair_L0' l' hl'
    have hxsum :
        S.lambda (Cdual S (CST S Sₕ) v) l' = S.lambda a l' + S.lambda b l' := by
      rw [← hsum, map_add, LinearMap.add_apply]
    rw [h_x, h_a, zero_add] at hxsum
    exact hxsum.symm
  -- Step 4: b = 0 by L0_paired (left injectivity).
  have hb_zero : b = 0 := S.L0_paired.2.1 b hb h_pair_b
  -- Step 5: x = a + 0 = a ∈ L1.
  rw [← hsum, hb_zero, add_zero]
  exact ha

/-- The `DualTransposeData` packaging used inside `kernelImage_ker` and
`kernelImage_im`. The dual transpose is `Cdual S (CST S Sₕ)`; the Lagrangian
range condition is witnessed by `Cdual_CST_mem_L1`, and the dimension equality
is witnessed by `S.L1_paired.1`. -/
private noncomputable def kernelImage_DTD (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) :
    DualTransposeData S.toX0Setup S.lambda S.L1 S.L1' Sₕ where
  Tdual := Cdual S (CST S Sₕ)
  pairing_eq := by
    intro v a'
    rw [Cdual_pairing_eq S hNondeg]
    -- Reduce `(CST S Sₕ) (a' : E')` to `((Sₕ a' : S.Vplus) : S.V0)`.
    have hp : projL1' S (a' : S.E') = a' := by
      unfold projL1'
      exact Submodule.linearProjOfIsCompl_apply_left S.isComplL' a'
    show -S.formV0 v ((CST S Sₕ) (a' : S.E'))
        = -S.formV0 v ((Sₕ a' : S.Vplus) : S.V0)
    congr 2
    show (S.Vplus.subtype ∘ₗ Sₕ ∘ₗ projL1' S) (a' : S.E')
        = ((Sₕ a' : S.Vplus) : S.V0)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hp]
  range_le_L1 := by
    rintro x ⟨v, rfl⟩
    exact Cdual_CST_mem_L1 S hNondeg Sₕ v
  finrank_L1_eq := S.L1_paired.1

/-- The pairing `S.lambda` packaged as a Mathlib `IsPerfPair`. Replicated
locally because the helper in `Slice.lean` is private to that file. -/
private lemma lambda_isPerfPair_local (S : SliceSetup F) :
    S.lambda.IsPerfPair := by
  obtain ⟨hinjL, hinjR, hdim⟩ := S.paired.isPerfect
  have hL_dim : Module.finrank F S.E
      = Module.finrank F (Module.Dual F S.E') := by
    rw [Subspace.dual_finrank_eq]; exact hdim
  have hR_dim : Module.finrank F S.E'
      = Module.finrank F (Module.Dual F S.E) := by
    rw [Subspace.dual_finrank_eq]; exact hdim.symm
  have hbijL : Function.Bijective S.lambda :=
    ⟨hinjL,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hL_dim).mp hinjL⟩
  have hbijR : Function.Bijective S.lambda.flip :=
    ⟨hinjR,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hR_dim).mp hinjR⟩
  exact LinearMap.IsPerfPair.mk hbijL hbijR

/-- `prop:kernel-image` (kernel formula): `ker X_{S,T} = E ⊕ ker T`.

The `kerXST_submod ⊆ ker XST` direction is constructive (helper
`kerXST_submod_le_ker`).

The reverse `ker XST ⊆ kerXST_submod` direction: given
`(e, v, e') ∈ ker XST`, by `XST_apply` we get
* `Cdual (CST Sₕ) v + (T (projL0' e') : E) = 0`,
* `X0 v + (Sₕ (projL1' e') : V0) = 0`.

The second equation forces `v ∈ ker X0` and `Sₕ (projL1' e') = 0`
(via `S.isCompl.disjoint`). To finish, we need:

1. `Sₕ` injective ⇒ `projL1' e' = 0`, i.e. `e' ∈ L0'`.
2. `Cdual (CST Sₕ) v ∈ S.L1` (so the first equation splits via
   `L1 ⊕ L0 = E`), combined with `Cdual restricted to ker X0` injective
   to conclude `v = 0`.

Both ingredients require additional hypotheses not present in the bare
`SliceSetup`: `Sₕ` injective (or iso), and the Lagrangian condition
`λ(L1, L0') = 0` (which forces `Cdual (CST Sₕ)` to land in `L1`, and is
needed for `sDual_restrict_ker_isIso` to apply to our `Cdual`). -/
theorem kernelImage_ker
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.ker (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) =
      kerXST_submod S (Sₕ : S.L1' →ₗ[F] S.Vplus) T := by
  refine le_antisymm ?_ (kerXST_submod_le_ker S (Sₕ : S.L1' →ₗ[F] S.Vplus) T)
  -- Reverse inclusion: take `(e, v, e') ∈ ker XST` and push through.
  intro x hx
  obtain ⟨e, v, e'⟩ := x
  rw [LinearMap.mem_ker, XST_apply] at hx
  -- Decompose the equation in the product `S.E × S.V0 × S.E'`.
  have hx1 :
      Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v
        + (T (projL0' S e') : S.E) = 0 := by
    have := congrArg Prod.fst hx
    simpa using this
  have hx2 :
      S.X0 v + ((Sₕ (projL1' S e') : S.Vplus) : S.V0) = 0 := by
    have := congrArg (Prod.fst ∘ Prod.snd) hx
    simpa using this
  -- From (hx2): `X0 v ∈ Vplus ∩ range X0 = ⊥`.
  have hX0v_in_Vplus : S.X0 v ∈ S.Vplus := by
    have hX : S.X0 v = -((Sₕ (projL1' S e') : S.Vplus) : S.V0) :=
      eq_neg_of_add_eq_zero_left hx2
    rw [hX]
    exact Submodule.neg_mem _ ((Sₕ (projL1' S e')).2)
  have hX0v_in_range : S.X0 v ∈ LinearMap.range S.X0 := ⟨v, rfl⟩
  have hX0v_zero : S.X0 v = 0 := by
    have hdisj : Disjoint S.Vplus (LinearMap.range S.X0) := S.isCompl.disjoint
    have hmem : S.X0 v ∈ S.Vplus ⊓ LinearMap.range S.X0 :=
      ⟨hX0v_in_Vplus, hX0v_in_range⟩
    rw [hdisj.eq_bot] at hmem
    exact (Submodule.mem_bot F).mp hmem
  have hSh_zero : ((Sₕ (projL1' S e') : S.Vplus) : S.V0) = 0 := by
    have h := hx2
    rw [hX0v_zero, zero_add] at h
    exact h
  have hv_in_kerX0 : v ∈ LinearMap.ker S.X0 := hX0v_zero
  -- Use `Sₕ.injective` plus `Vplus.subtype` injectivity to push to `L1'`.
  have hSh_vplus_zero : (Sₕ (projL1' S e') : S.Vplus) = 0 :=
    Subtype.ext hSh_zero
  have hprojL1'_zero : projL1' S e' = 0 := by
    apply Sₕ.injective
    rw [hSh_vplus_zero, map_zero]
  -- `Cdual(CST Sₕ) v ∈ L1` from the helper.
  have h_Cdual_in_L1 :
      Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v ∈ S.L1 :=
    Cdual_CST_mem_L1 S hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) v
  -- `(T (projL0' e') : E) ∈ L0`.
  have h_T_in_L0 : (T (projL0' S e') : S.E) ∈ S.L0 := (T (projL0' S e')).2
  -- `Cdual = -T ∈ L0`, so `Cdual ∈ L1 ∩ L0 = ⊥`, hence `Cdual = 0`.
  have h_Cdual_zero :
      Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v = 0 := by
    have h_neg_T_in_L0 : -(T (projL0' S e') : S.E) ∈ S.L0 :=
      Submodule.neg_mem _ h_T_in_L0
    have h_Cdual_eq :
        Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v
          = -(T (projL0' S e') : S.E) :=
      eq_neg_of_add_eq_zero_left hx1
    have h_Cdual_in_L0 :
        Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v ∈ S.L0 :=
      h_Cdual_eq ▸ h_neg_T_in_L0
    have hdisj : Disjoint S.L1 S.L0 := S.isComplL.disjoint
    have hmem :
        Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v ∈ S.L1 ⊓ S.L0 :=
      ⟨h_Cdual_in_L1, h_Cdual_in_L0⟩
    rw [hdisj.eq_bot] at hmem
    exact (Submodule.mem_bot F).mp hmem
  have h_T_zero : (T (projL0' S e') : S.E) = 0 := by
    have h := hx1
    rw [h_Cdual_zero, zero_add] at h
    exact h
  -- `v = 0` via `sDual_restrict_ker_isIso`.
  have hv_zero : v = 0 := by
    have hperf := lambda_isPerfPair_local S
    have hL1'_eq_c : Module.finrank F S.L1' = c S.toX0Setup := by
      have h1 : Module.finrank F S.L1' = Module.finrank F S.Vplus :=
        LinearEquiv.finrank_eq Sₕ
      rw [h1]
      exact finrank_Vplus_eq_c S.toX0Setup
    let D := kernelImage_DTD S hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus)
    obtain ⟨φ, hφ⟩ :=
      sDual_restrict_ker_isIso S.toX0Setup hNondeg
        S.lambda hperf S.L1 S.L1' hL1'_eq_c Sₕ D
    have h_phi_E :
        ((φ ⟨v, hv_in_kerX0⟩ : S.L1) : S.E)
          = Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v :=
      hφ ⟨v, hv_in_kerX0⟩
    have h_phi_zero_E : ((φ ⟨v, hv_in_kerX0⟩ : S.L1) : S.E) = 0 := by
      rw [h_phi_E, h_Cdual_zero]
    have h_phi_zero : φ ⟨v, hv_in_kerX0⟩ = 0 := by
      apply Subtype.ext
      simpa using h_phi_zero_E
    have h_w_zero : (⟨v, hv_in_kerX0⟩ : LinearMap.ker S.X0) = 0 := by
      apply φ.injective
      rw [h_phi_zero, map_zero]
    have hcoe :
        ((⟨v, hv_in_kerX0⟩ : LinearMap.ker S.X0) : S.V0)
          = ((0 : LinearMap.ker S.X0) : S.V0) :=
      congrArg (fun w : LinearMap.ker S.X0 => (w : S.V0)) h_w_zero
    simpa using hcoe
  -- Close the two structural goals.
  rw [kerXST_submod, Submodule.mem_prod, Submodule.mem_prod]
  refine ⟨trivial, ?_, ?_⟩
  · -- v ∈ ⊥
    show v ∈ (⊥ : Submodule F S.V0)
    rw [hv_zero]
    exact Submodule.zero_mem _
  · -- e' ∈ map L0'.subtype (ker T)
    show e' ∈ (LinearMap.ker T).map S.L0'.subtype
    rw [Submodule.mem_map]
    refine ⟨projL0' S e', ?_, ?_⟩
    · -- projL0' e' ∈ ker T
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      simpa using h_T_zero
    · -- L0'.subtype (projL0' e') = e'
      show ((projL0' S e' : S.L0') : S.E') = e'
      have hsum :
          ((projL1' S e' : S.L1') : S.E')
            + ((projL0' S e' : S.L0') : S.E') = e' := by
        have h := Submodule.IsCompl.projection_add_projection_eq_self
          S.isComplL' e'
        rw [Submodule.IsCompl.projection_apply S.isComplL' e',
            Submodule.IsCompl.projection_apply S.isComplL'.symm e'] at h
        exact h
      rw [hprojL1'_zero] at hsum
      simpa using hsum

/-- The image of `XST S Sₕ T`, encoded as a submodule of
`S.V = E × V₀ × E'` that morally equals `(L1 ⊕ Im T) ⊕ V₀ ⊕ 0` — the
`L1 ⊕ Im T` part of `E`, the full `V₀` factor, and trivial `E'` part. -/
noncomputable def imXST_submod
    (_Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) :
    Submodule F S.V :=
  Submodule.prod (S.L1 ⊔ (LinearMap.range T).map S.L0.subtype)
    (Submodule.prod ⊤ ⊥)

/-- Helper: `Submodule.prod p q` is linearly equivalent to `↥p × ↥q`. -/
private noncomputable def submoduleProdEquiv
    {F M M' : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup M'] [Module F M']
    (p : Submodule F M) (q : Submodule F M') :
    ↥(p.prod q) ≃ₗ[F] (↥p × ↥q) :=
  { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
    invFun := fun x => ⟨(x.1.1, x.2.1), ⟨x.1.2, x.2.2⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    left_inv := by intro x; ext <;> rfl
    right_inv := by intro x; ext <;> rfl }

/-- Helper: `Submodule.prod p q` has dimension `dim p + dim q` (when both
sides are finite-dimensional). -/
private theorem finrank_submodule_prod
    {F M M' : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup M'] [Module F M']
    (p : Submodule F M) (q : Submodule F M')
    [Module.Finite F p] [Module.Finite F q] :
    Module.finrank F ↥(p.prod q) = Module.finrank F p + Module.finrank F q := by
  rw [(submoduleProdEquiv p q).finrank_eq, Module.finrank_prod]

/-- `prop:kernel-image` (image formula): `Im X_{S,T} = (L1 ⊕ Im T) ⊕ V₀`.

The `imXST_submod ⊆ range XST` direction is constructive (any `(a, b, 0)`
with `a ∈ L1 ⊔ map L0 (range T)` and `b ∈ V0` has a preimage), but it
relies on `S^∨|_{ker X0} : ker X0 ≃ L1` (`sDual_restrict_ker_isIso` from
`X0Geometry.lean`), which is itself a sorry, and on `Sₕ` being surjective
onto `Vplus`. The reverse `range XST ⊆ imXST_submod` direction additionally
requires the Lagrangian condition `λ(L1, L0') = 0` (so that
`Cdual (CST Sₕ) v ∈ L1` for all `v ∈ V0`); this is *not* a part of the
current `SliceSetup` data, so the inclusion cannot be derived from the
current axioms.

Both directions are deferred to the polish stage. -/
theorem kernelImage_im
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.range (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) =
      imXST_submod S (Sₕ : S.L1' →ₗ[F] S.Vplus) T := by
  apply le_antisymm
  · -- Forward: `range XST ⊆ imXST_submod`.
    rintro x ⟨y, rfl⟩
    obtain ⟨e, v, e'⟩ := y
    rw [XST_apply]
    -- Show membership in `(L1 ⊔ map L0.subtype (range T)) × ⊤ × ⊥`.
    refine ⟨?_, trivial, ?_⟩
    · -- E component: `Cdual(CST Sₕ) v + (T(projL0' e') : E) ∈ L1 ⊔ image T`.
      apply Submodule.add_mem
      · exact Submodule.mem_sup_left
          (Cdual_CST_mem_L1 S hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) v)
      · apply Submodule.mem_sup_right
        rw [Submodule.mem_map]
        exact ⟨T (projL0' S e'), ⟨projL0' S e', rfl⟩, rfl⟩
    · -- E' component: `0 ∈ ⊥`.
      show (0 : S.paired.E') ∈ (⊥ : Submodule F S.paired.E')
      exact Submodule.zero_mem _
  · -- Reverse: `imXST_submod ⊆ range XST`.
    intro x hx
    obtain ⟨a, b, c⟩ := x
    rw [imXST_submod, Submodule.mem_prod, Submodule.mem_prod] at hx
    obtain ⟨ha, _hb, hc⟩ := hx
    -- `c = 0`.
    change c ∈ (⊥ : Submodule F S.paired.E') at hc
    have hc0 : c = 0 := (Submodule.mem_bot F).mp hc
    subst hc0
    -- Decompose `a = a_L1 + a_T_e` via `Submodule.mem_sup`.
    rw [Submodule.mem_sup] at ha
    obtain ⟨a_L1, ha_L1, a_T_e, ha_T_e, hsuma⟩ := ha
    rw [Submodule.mem_map] at ha_T_e
    obtain ⟨t_lift, ht_lift_in_range, ht_lift_eq⟩ := ha_T_e
    rw [LinearMap.mem_range] at ht_lift_in_range
    obtain ⟨l, hl_eq⟩ := ht_lift_in_range
    -- `hl_eq : T l = t_lift`, `ht_lift_eq : (t_lift : E) = a_T_e`.
    -- Decompose `b = b_V + r` via `IsCompl Vplus (range X0)`.
    have hb_top : b ∈ (⊤ : Submodule F S.V0) := Submodule.mem_top
    rw [← S.isCompl.codisjoint.eq_top, Submodule.mem_sup] at hb_top
    obtain ⟨b_V, hb_V, r, hr_in_range, hsumb⟩ := hb_top
    rw [LinearMap.mem_range] at hr_in_range
    obtain ⟨v_X0, hv_X0_eq⟩ := hr_in_range
    -- Build `l1' := Sₕ.symm ⟨b_V, hb_V⟩ : L1'`.
    let l1' : S.L1' := Sₕ.symm ⟨b_V, hb_V⟩
    let e' : S.paired.E' := (l1' : S.paired.E') + (l : S.paired.E')
    -- Get `Cdual(CST Sₕ) v_X0 ∈ L1`.
    have h_Cd_vX0_in_L1 :
        Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0 ∈ S.L1 :=
      Cdual_CST_mem_L1 S hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) v_X0
    -- Build the iso `φ : ker X0 ≃ L1` from `sDual_restrict_ker_isIso`.
    have hperf := lambda_isPerfPair_local S
    have hL1'_eq_c : Module.finrank F S.L1' = c S.toX0Setup := by
      have h1 : Module.finrank F S.L1' = Module.finrank F S.Vplus :=
        LinearEquiv.finrank_eq Sₕ
      rw [h1]
      exact finrank_Vplus_eq_c S.toX0Setup
    let D := kernelImage_DTD S hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus)
    obtain ⟨φ, hφ⟩ :=
      sDual_restrict_ker_isIso S.toX0Setup hNondeg
        S.lambda hperf S.L1 S.L1' hL1'_eq_c Sₕ D
    -- `target := a_L1 - Cdual(CST Sₕ) v_X0 ∈ L1`.
    have h_diff_in_L1 :
        a_L1 - Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0 ∈ S.L1 :=
      Submodule.sub_mem _ ha_L1 h_Cd_vX0_in_L1
    let target : S.L1 :=
      ⟨a_L1 - Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0, h_diff_in_L1⟩
    -- `w_a := φ.symm target ∈ ker X0`.
    let w_a : LinearMap.ker S.X0 := φ.symm target
    have h_phi_w_a : φ w_a = target := φ.apply_symm_apply target
    -- `Cdual(CST Sₕ) (w_a : V0) = a_L1 - Cdual(CST Sₕ) v_X0`.
    have h_Cd_w_a :
        Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) (w_a : S.V0)
          = a_L1 - Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0 := by
      have h1 : ((φ w_a : S.L1) : S.E)
          = Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) (w_a : S.V0) := hφ w_a
      have h2 : ((φ w_a : S.L1) : S.E)
          = a_L1 - Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0 := by
        rw [h_phi_w_a]
      rw [← h1, h2]
    -- Construct preimage `(0, v_a + v_X0, e')`.
    refine ⟨((0 : S.paired.E), (w_a : S.V0) + v_X0, e'), ?_⟩
    rw [XST_apply]
    -- Compute `projL1' e' = l1'` and `projL0' e' = l`.
    have hprojL1' : projL1' S e' = l1' := by
      show projL1' S ((l1' : S.paired.E') + (l : S.paired.E')) = l1'
      rw [map_add]
      have h1 : projL1' S (l1' : S.paired.E') = l1' := by
        unfold projL1'
        exact Submodule.linearProjOfIsCompl_apply_left S.isComplL' l1'
      have h2 : projL1' S (l : S.paired.E') = 0 := by
        unfold projL1'
        exact Submodule.linearProjOfIsCompl_apply_right S.isComplL' l
      rw [h1, h2, add_zero]
    have hprojL0' : projL0' S e' = l := by
      show projL0' S ((l1' : S.paired.E') + (l : S.paired.E')) = l
      rw [map_add]
      have h1 : projL0' S (l1' : S.paired.E') = 0 := by
        unfold projL0'
        exact Submodule.linearProjOfIsCompl_apply_right S.isComplL'.symm l1'
      have h2 : projL0' S (l : S.paired.E') = l := by
        unfold projL0'
        exact Submodule.linearProjOfIsCompl_apply_left S.isComplL'.symm l
      rw [h1, h2, zero_add]
    rw [hprojL1', hprojL0']
    -- `(Sₕ l1' : V0) = b_V` (using both forms of Sₕ-application).
    have hSh_l1' :
        (((Sₕ : S.L1' →ₗ[F] S.Vplus) l1' : S.Vplus) : S.V0) = b_V := by
      show (((Sₕ : S.L1' →ₗ[F] S.Vplus) (Sₕ.symm ⟨b_V, hb_V⟩) : S.Vplus) : S.V0)
          = b_V
      simp [LinearEquiv.apply_symm_apply]
    -- `(T l : E) = a_T_e`.
    have hT_l : (T l : S.E) = a_T_e := by
      rw [hl_eq]; exact ht_lift_eq
    -- E component: `Cdual(CST Sₕ) (w_a + v_X0) + (T l : E) = a_L1 + a_T_e = a`.
    have h_X0_w_a : S.X0 (w_a : S.V0) = 0 := w_a.2
    have hsuma' : a_L1 + a_T_e = a := by simpa using hsuma
    have hsumb' : b_V + r = b := by simpa using hsumb
    refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
    · -- E component
      rw [map_add, h_Cd_w_a, hT_l]
      have habel :
          a_L1 - Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0
            + Cdual S (CST S (Sₕ : S.L1' →ₗ[F] S.Vplus)) v_X0 + a_T_e
            = a_L1 + a_T_e := by abel
      rw [habel, hsuma']
    · -- V0 component
      rw [map_add, h_X0_w_a, zero_add, hv_X0_eq, hSh_l1']
      rw [add_comm]
      exact hsumb'
    · -- E' component: 0 = 0.
      rfl

/-- `prop:kernel-image` (dimension formula): `dim ker X_{S,T} = r + (l - rank T)`.

The proof reduces to `kernelImage_ker` (sorry'd reverse direction) plus a
clean dimension count of `kerXST_submod = ⊤ × (⊥ × map L0'.subtype (ker T))`.
The dimension piece is fully proven; the dependency on `kernelImage_ker`
(in particular, its currently sorry'd reverse direction) is the only
remaining gap. -/
theorem kernelImage_dim
    (_hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    Module.finrank F (LinearMap.ker (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T))
      = Module.finrank F S.E +
          (Module.finrank F S.L0' - Module.finrank F (LinearMap.range T)) := by
  -- Step 1: Replace `ker XST` with `kerXST_submod` via `kernelImage_ker`.
  -- After Tier S #4, `kernelImage_ker` takes `Sₕ` as a `LinearEquiv` directly.
  rw [kernelImage_ker S _hNondeg Sₕ T _hT]
  -- Step 2: Compute `dim kerXST_submod = dim E + dim (map L0'.subtype (ker T))`.
  unfold kerXST_submod
  rw [finrank_submodule_prod, finrank_submodule_prod]
  rw [finrank_top, finrank_bot]
  -- Goal: `dim E + (0 + dim (map L0'.subtype (ker T))) = dim E + (dim L0' - dim range T)`
  rw [Submodule.finrank_map_subtype_eq]
  -- Goal: `dim paired.E + (0 + dim (ker T)) = dim S.E + (dim L0' - dim range T)`.
  -- Identify `S.E` with `S.paired.E` (these are definitionally equal but
  -- `omega` does not see through the `abbrev`).
  change Module.finrank F S.paired.E + _ = Module.finrank F S.paired.E + _
  -- Apply `dim ker T = dim L0' - dim range T` via rank-nullity on `T`.
  have hrank : Module.finrank F (LinearMap.range T) + Module.finrank F (LinearMap.ker T)
      = Module.finrank F S.L0' :=
    LinearMap.finrank_range_add_finrank_ker T
  omega

end SliceSetup

end InducedOrbitToy
