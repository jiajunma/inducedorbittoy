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
* `p` is an isometry of the ambient form (encoded as
  `IsAdjointPair S.ambientForm S.ambientForm p p`).

The third clause encodes "form-preserving" via the Mathlib pair-adjoint
predicate.  In the prover stage one may want to switch to a stronger
"is-an-isometry" predicate; for autoformalize we only need the abstract
shape. -/
def IsParabolicElement (p : Module.End F S.V) : Prop :=
  IsUnit p ∧ Submodule.map p S.flagE = S.flagE ∧
    Submodule.map p S.flagEV0 = S.flagEV0 ∧
    LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p

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
   uses `_hB : IsSkewB B` plus the conjugation formula
   `uD_conj_XCB`.

Both `Step 2` and `Step 3` rely on results from `Slice.lean` (`uD`,
`uD_conj_XCB`, `parametrizeX0PlusU_*`) which are themselves currently
`sorry`. Filling this theorem therefore depends on the upstream
`Slice.lean` block being completed first. -/
theorem pNormalForm
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B)
    (_hRank :
      Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0),
      IsSkewT S T ∧
        ∃ (p : Module.End F S.V), IsParabolicElement S p ∧
          p ∘ₗ XCB S C B = XST S Sₕ T ∘ₗ p := by
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

Both directions hinge on having a workable model of the parabolic action
on the residual block, which in turn requires the
`pNormalForm`/`Slice.lean` machinery to be in place. Deferred. -/
theorem pNormalForm_residual_orbit_iso
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' →ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0) (_hT₁ : IsSkewT S T₁) (_hT₂ : IsSkewT S T₂) :
    (∃ (p : Module.End F S.V), IsParabolicElement S p ∧
        p ∘ₗ XST S Sₕ T₁ = XST S Sₕ T₂ ∘ₗ p) ↔
      Bilinear.AreIsometric (BT S T₁) (BT S T₂) := by
  sorry

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
    (_hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.ker (XST S Sₕ T) = kerXST_submod S Sₕ T := by
  refine le_antisymm ?_ (kerXST_submod_le_ker S Sₕ T)
  -- Reverse inclusion: take `(e, v, e') ∈ ker XST`, push through what we can
  -- without iso/Lagrangian assumptions.
  intro x hx
  obtain ⟨e, v, e'⟩ := x
  rw [LinearMap.mem_ker, XST_apply] at hx
  -- Decompose the equation in the product `S.E × S.V0 × S.E'`.
  have hx1 : Cdual S (CST S Sₕ) v + (T (projL0' S e') : S.E) = 0 := by
    have := congrArg Prod.fst hx
    simpa using this
  have hx2 : S.X0 v + (Sₕ (projL1' S e') : S.V0) = 0 := by
    have := congrArg (Prod.fst ∘ Prod.snd) hx
    simpa using this
  -- From (hx2): `X0 v ∈ Vplus ∩ range X0 = ⊥`. So `X0 v = 0` and
  -- `Sₕ (projL1' e') = 0` in `S.V0`.
  have hX0v_in_Vplus : S.X0 v ∈ S.Vplus := by
    have hX : S.X0 v = -(Sₕ (projL1' S e') : S.V0) :=
      eq_neg_of_add_eq_zero_left hx2
    rw [hX]
    exact Submodule.neg_mem _ (Sₕ (projL1' S e')).2
  have hX0v_in_range : S.X0 v ∈ LinearMap.range S.X0 := ⟨v, rfl⟩
  have hX0v_zero : S.X0 v = 0 := by
    have hdisj : Disjoint S.Vplus (LinearMap.range S.X0) := S.isCompl.disjoint
    have : S.X0 v ∈ S.Vplus ⊓ LinearMap.range S.X0 :=
      ⟨hX0v_in_Vplus, hX0v_in_range⟩
    rw [hdisj.eq_bot] at this
    exact (Submodule.mem_bot F).mp this
  have hSh_zero : (Sₕ (projL1' S e') : S.V0) = 0 := by
    have : S.X0 v + (Sₕ (projL1' S e') : S.V0) = 0 := hx2
    rw [hX0v_zero, zero_add] at this
    exact this
  have hv_in_kerX0 : v ∈ LinearMap.ker S.X0 := hX0v_zero
  -- The remaining steps require Sₕ injectivity and Lagrangian conditions
  -- on `Cdual (CST Sₕ)` — left as a focused sorry.
  rw [kerXST_submod, Submodule.mem_prod, Submodule.mem_prod]
  refine ⟨trivial, ?_, ?_⟩
  · -- Goal: v ∈ ⊥. We have v ∈ ker X0 from `hv_in_kerX0`. Without
    -- additional structure (e.g. `c S = 0`), `v = 0` cannot be derived.
    sorry
  · -- Goal: e' ∈ map L0'.subtype (ker T). We have `Sₕ (projL1' e') = 0`,
    -- which (with Sₕ injective) would give projL1' e' = 0, hence
    -- e' ∈ L0'. Then `Cdual (CST Sₕ) v + T (e' as L0') = 0` with
    -- both summands in L1, L0 (Lagrangian) forces both 0, giving
    -- `e' as L0' ∈ ker T`.
    sorry

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
    (_hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (_hT : IsSkewT S T) :
    LinearMap.range (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) =
      imXST_submod S (Sₕ : S.L1' →ₗ[F] S.Vplus) T := by
  sorry

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
  rw [kernelImage_ker S _hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) T _hT]
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
