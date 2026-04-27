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

/-- Witness existence for `pNormalForm`: there exist `Sₕ`, `D`, `T` such
that the *unipotent* conjugation `uD D ∘ XCB C B ∘ uD (-D)` already
equals `XST Sₕ T`, with `T` skew.

This bundles the *multi-step Levi pre-conjugation* from the blueprint
proof (lines 200–264 of `references/blueprint_verified.md`):
  (a) act by a Levi element of `P` to arrange `ker Cbar = L0'`,
  (b) act by another Levi element on `L1'` to identify `Cbar|_{L1'}` with
      a chosen iso `Sₕ : L1' ≃ Vplus`,
  (c) choose `D` (in two stages, `D_0 : L0' → ker X0` then
      `D_1 : L1' → ker X0`) so that the unipotent `uD D` absorbs the
      `B|_{L1'}`-blocks and so that `XCB (C - X0 D) (B + ...) = XST Sₕ T`.

The Lean encoding of steps (a) and (b) requires Levi-action machinery on
`SliceSetup` that is NOT yet in scope (`Slice.lean` only exposes the
`uD` unipotent piece). Until the plan agent adds the Levi machinery,
we record this existence claim as a focused `sorry`; once filled,
`pNormalForm` follows mechanically.

NOTE: the witness statement glosses over one subtlety — the *input*
`(C, B)` to `pNormalForm` must already be Levi-normalized for the
alignment to hold with `p = uD D`. In the actual blueprint proof the
parabolic `p` is `uD D ∘ ℓ` for a Levi `ℓ`; here we conflate the Levi
action into the choice of `(Sₕ, D, T)`. -/
private theorem pNormalForm_witnesses (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B)
    (_hRank :
      Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' →ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
      (T : S.L0' →ₗ[F] S.L0),
      IsSkewT S T ∧
      uD S D ∘ₗ XCB S C B ∘ₗ uD S (-D) = XST S Sₕ T := by
  -- BLOCKED: see docstring. Requires Levi-conjugation machinery on
  -- SliceSetup that is not yet present in Slice.lean. The blueprint
  -- proof at §prop:p-normal-form (lines 200–264) gives the construction
  -- explicitly: (a) ker Cbar = L0' via Levi(E') action; (b) Cbar|_{L1'}
  -- = Sₕ via another Levi(E') action; (c) D = D₀ ⊕ D₁ chosen via the
  -- perfect pairing V₊ × ker X₀ → F (`vplusKerPairing_isPerfPair`).
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
  -- Step 1: Pull (Sₕ, D, T) plus the conjugation equation from the helper.
  obtain ⟨Sₕ, D, T, hT, hConj⟩ :=
    pNormalForm_witnesses S _hNondeg _hChar C B _hB _hRank
  refine ⟨Sₕ, T, hT, uD S D, ?_, ?_⟩
  · -- IsParabolicElement (uD S D)
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- IsUnit (uD S D)
      exact isUnit_uD S _hNondeg _hChar D
    · -- Submodule.map (uD D) S.flagE = S.flagE
      have h_pos : Submodule.map (uD S D) S.flagE ≤ S.flagE :=
        (uD_isParabolic S _hNondeg _hChar D).2.1
      have h_neg : Submodule.map (uD S (-D)) S.flagE ≤ S.flagE :=
        (uD_isParabolic S _hNondeg _hChar (-D)).2.1
      exact map_uD_eq_of_le S _hNondeg _hChar D S.flagE h_pos h_neg
    · -- Submodule.map (uD D) S.flagEV0 = S.flagEV0
      have h_pos : Submodule.map (uD S D) S.flagEV0 ≤ S.flagEV0 :=
        (uD_isParabolic S _hNondeg _hChar D).2.2
      have h_neg : Submodule.map (uD S (-D)) S.flagEV0 ≤ S.flagEV0 :=
        (uD_isParabolic S _hNondeg _hChar (-D)).2.2
      exact map_uD_eq_of_le S _hNondeg _hChar D S.flagEV0 h_pos h_neg
    · -- LinearMap.IsOrthogonal S.ambientForm (uD S D)
      -- After Tier S #1, `uD_isParabolic`'s 1st conjunct is
      -- `IsAdjointPair S.ambientForm S.ambientForm (uD D) (uD (-D))`.
      -- Chain that with `uD_neg_inverse` to get the isometry identity.
      intro u v
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
      calc S.ambientForm (uD S D u) (uD S D v)
          = S.ambientForm u (uD S (-D) (uD S D v)) := hAdj u (uD S D v)
        _ = S.ambientForm u v := by rw [hinv_apply]
  · -- Conjugation equation: `uD D ∘ XCB C B = XST Sₕ T ∘ uD D`.
    -- From `hConj : uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T`, multiply on
    -- the right by `uD D` and use `uD (-D) ∘ uD D = id`.
    have hinv : uD S (-D) ∘ₗ uD S D = LinearMap.id := by
      have := uD_neg_inverse S _hNondeg _hChar (-D)
      simpa [neg_neg] using this
    -- Apply `(· ∘ₗ uD S D)` to both sides of `hConj`.
    have hgoal := congrArg (fun f : Module.End F S.V => f ∘ₗ uD S D) hConj
    simp only at hgoal
    -- Reduce LHS via associativity and `hinv`.
    have key :
        (uD S D ∘ₗ XCB S C B ∘ₗ uD S (-D)) ∘ₗ uD S D
          = uD S D ∘ₗ XCB S C B := by
      rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hinv,
        LinearMap.comp_id]
    rw [key] at hgoal
    exact hgoal

/-! ### Helpers for `pNormalForm_residual_orbit_iso`. -/

/-- Forward extraction: from a parabolic `p` realising the conjugation
`p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`, extract the Levi `L0'`-block
`h : L0' ≃ₗ L0'` such that `BT T₂ (h u) (h v) = BT T₁ u v`.

This bundles the *Levi block extraction* from the blueprint proof
(lines 270–319 of `references/blueprint_verified.md`):
  (a) write `p = u_D ∘ m` with `m` in the Levi factor,
  (b) `m` acts on `E'` as `d ∈ GL(E')` preserving `L0' = ker Cbar` so
      `h := d|_{L0'} ∈ GL(L0')`,
  (c) the unipotent factor `u_D` does not affect the residual L0' → L0
      block, so the Levi-action law `T₂ = (h⁻¹)^∨ T₁ h` follows.

Step (a) (Levi/unipotent decomposition of a general parabolic) is not
yet exposed in `Slice.lean`. Sorried until that machinery lands. -/
private theorem residual_levi_extract (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂)
    (p : Module.End F S.V) (_hP : IsParabolicElement S p)
    (_hConj : p ∘ₗ XST S Sₕ T₁ = XST S Sₕ T₂ ∘ₗ p) :
    Bilinear.AreIsometric (BT S T₁) (BT S T₂) := by
  -- BLOCKED: Requires Levi/unipotent decomposition of `p`. The blueprint
  -- argument (lines 272–319) writes `p = u_D · m` with `m` Levi, then
  -- restricts `m`'s action on `E'` to `L0'` to obtain `h`. Without that
  -- decomposition machinery in `Slice.lean`, we cannot extract `h`.
  sorry

/-- Backward construction: from an isometry `h : L0' ≃ₗ L0'` of
`(BT T₁) ↦ (BT T₂)`, construct a parabolic `p ∈ Module.End F S.V`
realising the conjugation `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p`.

Blueprint construction: `p = (h⁻¹)^∨ ⊕ id ⊕ h` on the decomposition
`V = L_1 ⊕ L_0 ⊕ V_0 ⊕ L_1' ⊕ L_0'`, where `(h⁻¹)^∨ : L_0 → L_0` is
the perfect-pairing dual of `h⁻¹` (using the `L1×L1'` perfect pairing).

The construction requires the perfect-pairing transpose on the L₀ block
plus the L₁⊕L₀ direct-sum decomposition of `E` (for assembling `p` on
the `E` block). Both pieces require additional `SliceSetup` machinery
(specifically, a Lagrangian condition aligning `L0` with `L0'` via
`λ`); the bare `SliceSetup` only gives `L0_isotropic` (`λ(L0, L0') = 0`),
not the perfect pairing on `L0 × L0'`.

Sorried until that infrastructure lands. -/
private theorem residual_levi_build (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂)
    (h : S.L0' ≃ₗ[F] S.L0') (_hh : ∀ u v, BT S T₂ (h u) (h v) = BT S T₁ u v) :
    ∃ (p : Module.End F S.V), IsParabolicElement S p ∧
      p ∘ₗ XST S Sₕ T₁ = XST S Sₕ T₂ ∘ₗ p := by
  -- BLOCKED: Requires the perfect-pairing dual `(h⁻¹)^∨ : L_0 → L_0` on
  -- the `L_0` block, which needs an extra Lagrangian condition not
  -- present in the bare `SliceSetup` (only `L0_isotropic` is given,
  -- not perfect pairing on `L0 × L0'`).
  -- After Tier S #1 (this round), `IsParabolicElement`'s 4th conjunct is
  -- `LinearMap.IsOrthogonal S.ambientForm p`, which is the genuine
  -- isometry condition; no longer a Tier D inheritance issue. The
  -- residual blocker is purely the perfect-pairing dual machinery.
  sorry

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
`residual_levi_build`, which capture the missing Levi-action machinery
as focused `sorry`s. -/
theorem pNormalForm_residual_orbit_iso
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' →ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0) (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂) :
    (∃ (p : Module.End F S.V), IsParabolicElement S p ∧
        p ∘ₗ XST S Sₕ T₁ = XST S Sₕ T₂ ∘ₗ p) ↔
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
