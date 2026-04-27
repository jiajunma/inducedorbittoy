import InducedOrbitToy.X0Geometry

/-!
# `lem:parametrize-x0-plus-u` and `lem:unipotent-conjugation`

Autoformalization of the two slice lemmas from
`references/blueprint_verified.md` (lines 56–173).

Informal companion: `.archon/informal/slice.md`.

This file exposes:
* `IsSkewB` — the skewness condition `λ(B u, v) + ε λ(B v, u) = 0` on
  `B : E' →ₗ[F] E`,
* `Cdual`, `Cdual_pairing_eq` — the transpose of `C : E' →ₗ[F] V₀` along
  the perfect pairing,
* `XCB`, `XST` — the operators parametrising `X₀ + 𝔲` and the special
  case `X_{S,T}`,
* `X0Lift` — the lift of `X₀` to the ambient `V`,
* `parametrizeX0PlusU_existence`, `parametrizeX0PlusU_uniqueness`
  (together implementing `lem:parametrize-x0-plus-u`),
* `uD`, `uD_isParabolic`, `uD_conj_XCB` — the unipotent endomorphism
  `u_D` and its key properties (`lem:unipotent-conjugation`).

All proof bodies are `sorry`; some `noncomputable def`s use term-mode
`sorry` until the prover stage fills them in.
-/

namespace InducedOrbitToy

open LinearMap

variable {F : Type*} [Field F]

/-! ## The skewness condition on `B : E' →ₗ[F] E` -/

/-- The skewness condition required of `B : E' →ₗ[F] E` in
`lem:parametrize-x0-plus-u`: `λ(B u, v) + ε · λ(B v, u) = 0`. -/
def IsSkewB (S : SliceSetup F) (B : S.E' →ₗ[F] S.E) : Prop :=
  ∀ u v : S.E', S.lambda (B u) v + S.eps * S.lambda (B v) u = 0

/-! ## Dual transpose `Cdual : V₀ →ₗ[F] E` -/

/-- The pairing `S.lambda` is a perfect pairing in the Mathlib sense
(`LinearMap.IsPerfPair`).  This is a packaging lemma extracting the
typeclass instance from the project's `IsPerfectPairing` predicate. -/
private theorem lambda_isPerfPair (S : SliceSetup F) :
    S.lambda.IsPerfPair := by
  obtain ⟨hinjL, hinjR, hdim⟩ := S.paired.isPerfect
  -- `Module.Dual F S.E'` has the same finrank as `S.E'`, hence as `S.E`.
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

/-- For `C : E' →ₗ[F] V₀`, the dual transpose `Cdual S C : V₀ →ₗ[F] E`
is the unique linear map characterised by
`λ (Cdual S C v) e' = - B₀ v (C e')` for all `v : V₀`, `e' : E'`.

Constructed via the perfect pairing `S.lambda.toPerfPair`: the assignment
`v ↦ -(formV0 v ∘ₗ C) : V₀ →ₗ[F] Module.Dual F E'` is composed with the
inverse perfect-pairing equivalence to land in `S.E`. -/
noncomputable def Cdual (S : SliceSetup F) (_C : S.E' →ₗ[F] S.V0) :
    S.V0 →ₗ[F] S.E :=
  haveI := lambda_isPerfPair S
  S.lambda.toPerfPair.symm.toLinearMap.comp
    (-(_C.dualMap.comp S.formV0))

/-- Defining identity for `Cdual`: `λ (Cdual v) e' = - B₀ v (C e')`. -/
theorem Cdual_pairing_eq (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate)
    (C : S.E' →ₗ[F] S.V0) (v : S.V0) (e' : S.E') :
    S.lambda (Cdual S C v) e' = - S.formV0 v (C e') := by
  haveI := lambda_isPerfPair S
  -- Unfold `Cdual` to see its underlying perfect-pairing-inverse construction.
  show S.lambda
        (S.lambda.toPerfPair.symm
          ((-(C.dualMap.comp S.formV0)) v)) e' = _
  -- `S.lambda` evaluated on the inverse perfect-pairing image is the original
  -- functional, by `LinearMap.apply_symm_toPerfPair_self`.
  rw [S.lambda.apply_symm_toPerfPair_self]
  -- The remaining functional is `-(C.dualMap (S.formV0 v))` applied to `e'`,
  -- which is `-(S.formV0 v (C e'))` by `LinearMap.dualMap_apply`.
  simp [LinearMap.dualMap_apply]

/-! ## Lift of `X₀` to the ambient `V = E × V₀ × E'` -/

/-- Lift of `S.X0 : V₀ →ₗ[F] V₀` to the ambient `V = E × V₀ × E'`,
acting as `X₀` on the `V₀` summand and as `0` on `E` and `E'`. -/
noncomputable def X0Lift (S : SliceSetup F) : Module.End F S.V :=
  (LinearMap.inr F S.paired.E (S.V0 × S.paired.E')) ∘ₗ
    (LinearMap.inl F S.V0 S.paired.E') ∘ₗ S.X0 ∘ₗ
    (LinearMap.fst F S.V0 S.paired.E') ∘ₗ
    (LinearMap.snd F S.paired.E (S.V0 × S.paired.E'))

/-! ## The operator `XCB` parametrised by `(C, B)` -/

/-- For `C : E' →ₗ[F] V₀` and `B : E' →ₗ[F] E`, the operator
`X_{C,B} : V →ₗ[F] V` defined block-wise on the decomposition
`V = E × V₀ × E'` by
`(e, v, e') ↦ (Cdual v + B e', X₀ v + C e', 0)`. -/
noncomputable def XCB (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) :
    S.V →ₗ[F] S.V :=
  -- First component:  Cdual ∘ projV0  +  B ∘ projE'
  -- Second component: X₀ ∘ projV0     +  C ∘ projE'
  -- Third component:  0
  let projE  : S.V →ₗ[F] S.paired.E :=
    LinearMap.fst F S.paired.E (S.V0 × S.paired.E')
  let projV0 : S.V →ₗ[F] S.V0 :=
    LinearMap.fst F S.V0 S.paired.E' ∘ₗ
      LinearMap.snd F S.paired.E (S.V0 × S.paired.E')
  let projE' : S.V →ₗ[F] S.paired.E' :=
    LinearMap.snd F S.V0 S.paired.E' ∘ₗ
      LinearMap.snd F S.paired.E (S.V0 × S.paired.E')
  let _ := projE
  let inE   : S.paired.E →ₗ[F] S.V :=
    LinearMap.inl F S.paired.E (S.V0 × S.paired.E')
  let inV0  : S.V0 →ₗ[F] S.V :=
    LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
      LinearMap.inl F S.V0 S.paired.E'
  inE ∘ₗ ((Cdual S C) ∘ₗ projV0 + B ∘ₗ projE') +
    inV0 ∘ₗ (S.X0 ∘ₗ projV0 + C ∘ₗ projE')

/-! ## The special case `X_{S,T}` -/

/-- Project `E' → L1'` along `L0'` using the complementary decomposition
`S.isComplL'`. -/
noncomputable def projL1' (S : SliceSetup F) : S.paired.E' →ₗ[F] S.L1' :=
  Submodule.linearProjOfIsCompl S.L1' S.L0' S.isComplL'

/-- Project `E' → L0'` along `L1'` using the complementary decomposition
`S.isComplL'`. -/
noncomputable def projL0' (S : SliceSetup F) : S.paired.E' →ₗ[F] S.L0' :=
  Submodule.linearProjOfIsCompl S.L0' S.L1' S.isComplL'.symm

/-- The component `C_{S,T} : E' →ₗ[F] V₀`: extend `Sₕ : L1' →ₗ[F] Vplus`
by zero on `L0'`, then embed `Vplus ↪ V₀`. -/
noncomputable def CST (S : SliceSetup F)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) : S.paired.E' →ₗ[F] S.V0 :=
  S.Vplus.subtype ∘ₗ Sₕ ∘ₗ projL1' S

/-- The component `B_{S,T} : E' →ₗ[F] E`: extend `T : L0' →ₗ[F] L0` by
zero on `L1'`, then embed `L0 ↪ E`. -/
noncomputable def BST (S : SliceSetup F)
    (T : S.L0' →ₗ[F] S.L0) : S.paired.E' →ₗ[F] S.paired.E :=
  S.L0.subtype ∘ₗ T ∘ₗ projL0' S

/-- The special case `X_{S,T} := X_{C_{S,T}, B_{S,T}}` from the
blueprint. -/
noncomputable def XST (S : SliceSetup F)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) :
    S.V →ₗ[F] S.V :=
  XCB S (CST S Sₕ) (BST S T)

/-! ## `lem:parametrize-x0-plus-u` -/

/-- Pointwise formula for `XCB`: it is the standard block-matrix
formula on `V = E × V₀ × E'`. -/
private lemma XCB_apply (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (e : S.paired.E) (v : S.V0) (e' : S.paired.E') :
    XCB S C B (e, v, e')
      = (Cdual S C v + B e', S.X0 v + C e', (0 : S.paired.E')) := by
  unfold XCB
  simp

/-- Pointwise formula for `X0Lift`. -/
private lemma X0Lift_apply (S : SliceSetup F)
    (e : S.paired.E) (v : S.V0) (e' : S.paired.E') :
    X0Lift S (e, v, e') = (0, S.X0 v, (0 : S.paired.E')) := by
  unfold X0Lift
  simp

/-- Pointwise formula for `XCB - X0Lift`: the V₀-part is just `C e'`. -/
private lemma XCB_sub_X0Lift_apply (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (e : S.paired.E) (v : S.V0) (e' : S.paired.E') :
    (XCB S C B - X0Lift S) (e, v, e')
      = (Cdual S C v + B e', C e', (0 : S.paired.E')) := by
  rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
  ext <;> simp

/-- `X_{C,B}` lies in `X₀ + 𝔲` for any admissible `(C, B)`. -/
theorem parametrizeX0PlusU_mem (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_hB : IsSkewB S B) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- vanishes on `flagE`
    intro x hx
    obtain ⟨e, v, e'⟩ := x
    rcases hx with ⟨_, hv, he'⟩
    have hv0 : v = 0 := by simpa using hv
    have he'0 : e' = 0 := by simpa using he'
    show (XCB S C B - X0Lift S) (e, v, e') = 0
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply, hv0, he'0]
    simp
  · -- maps `flagEV0` into `flagE`
    intro x hx
    obtain ⟨e, v, e'⟩ := x
    rcases hx with ⟨_, _, he'⟩
    have he'0 : e' = 0 := by simpa using he'
    show (XCB S C B - X0Lift S) (e, v, e') ∈ S.flagE
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply, he'0]
    refine ⟨trivial, ?_, ?_⟩ <;> simp
  · -- maps everything into `flagEV0`
    intro x
    obtain ⟨e, v, e'⟩ := x
    show (XCB S C B - X0Lift S) (e, v, e') ∈ S.flagEV0
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
    refine ⟨trivial, trivial, ?_⟩
    simp
  · -- IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)
    intro x y
    obtain ⟨e₁, v₁, e₁'⟩ := x
    obtain ⟨e₂, v₂, e₂'⟩ := y
    rw [XCB_sub_X0Lift_apply, XCB_sub_X0Lift_apply]
    simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_add,
      LinearMap.add_apply, map_zero, mul_zero, add_zero, zero_add]
    rw [Cdual_pairing_eq S _hNondeg C v₁ e₂',
        Cdual_pairing_eq S _hNondeg C v₂ e₁']
    have hε := S.epsSymm
    have hε2 : S.eps * S.eps = 1 := by
      rcases S.epsValid with h | h <;> simp [h]
    have hskewB := _hB e₁' e₂'
    have hSym : S.formV0 v₂ (C e₁') = S.eps * S.formV0 (C e₁') v₂ := hε _ _
    linear_combination hskewB - S.eps * hSym
      - S.formV0 (C e₁') v₂ * hε2

/-- Existence in `lem:parametrize-x0-plus-u`: every `Y ∈ X₀ + 𝔲`
is of the form `X_{C,B}` for some admissible `(C, B)`.

The 4th conjunct of `UnipotentRadical S` (skew-adjointness w.r.t.
`S.ambientForm`) is what forces `(α, γ) ↦ α = Cdual γ` and
`IsSkewB β` on the V₀→E and E'→E blocks of `Y`, ensuring the candidate
`(C, B) := (projV0 ∘ Y ∘ inE', projE ∘ Y ∘ inE')` actually returns a
member of the image of `(C, B) ↦ XCB C B - X0Lift`. -/
theorem parametrizeX0PlusU_existence (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate)
    (Y : Module.End F S.V) (_hY : Y ∈ UnipotentRadical S) :
    ∃ (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E),
      IsSkewB S B ∧ XCB S C B - X0Lift S = Y := by
  -- Canonical candidates extracted from the block decomposition of `Y`.
  let inE' : S.paired.E' →ₗ[F] S.V :=
    (LinearMap.inr F S.paired.E (S.V0 × S.paired.E')) ∘ₗ
      (LinearMap.inr F S.V0 S.paired.E')
  let projE  : S.V →ₗ[F] S.paired.E :=
    LinearMap.fst F S.paired.E (S.V0 × S.paired.E')
  let projV0 : S.V →ₗ[F] S.V0 :=
    (LinearMap.fst F S.V0 S.paired.E') ∘ₗ
      (LinearMap.snd F S.paired.E (S.V0 × S.paired.E'))
  -- Destructure `Y ∈ UnipotentRadical S` to its four conjuncts.
  obtain ⟨hflagE, hflagEV0, hAll, hSkewY⟩ := _hY
  refine ⟨projV0 ∘ₗ Y ∘ₗ inE', projE ∘ₗ Y ∘ₗ inE', ?_, ?_⟩
  · -- IsSkewB B for `B := projE ∘ Y ∘ inE'`: the (E', E')-block of the
    -- skew-adjointness identity `hSkewY (0, 0, u) (0, 0, v)` collapses
    -- the `B₀(_,_)` and `λ(_,0)`/`λ(0,_)` terms, leaving exactly
    -- `λ((Y(0,0,u)).1, v) + ε · λ((Y(0,0,v)).1, u) = 0`.
    intro u v
    show S.lambda ((projE ∘ₗ Y ∘ₗ inE') u) v
        + S.eps * S.lambda ((projE ∘ₗ Y ∘ₗ inE') v) u = 0
    have h := hSkewY (0, 0, u) (0, 0, v)
    simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
      LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
    -- After simp, `h` matches the goal (up to `(projE ∘ₗ Y ∘ₗ inE') u
    --   = (Y (0, 0, u)).1`, which is definitional).
    show S.paired.pairing (Y (0, 0, u)).1 v
        + S.eps * S.paired.pairing (Y (0, 0, v)).1 u = 0
    exact h
  · -- The equality `XCB S C B - X0Lift S = Y`.
    apply LinearMap.ext
    rintro ⟨e, v, e'⟩
    -- Y vanishes on `flagE`.
    have hY_e0 : Y (e, 0, 0) = 0 :=
      hflagE _ ⟨trivial, Submodule.zero_mem _, Submodule.zero_mem _⟩
    -- Decompose `(e, v, e') = (e, 0, 0) + (0, v, 0) + (0, 0, e')`.
    have hsum : ((e, v, e') : S.V) = (e, 0, 0) + (0, v, 0) + (0, 0, e') := by
      ext <;> simp
    have hY_sum : Y (e, v, e') = Y (0, v, 0) + Y (0, 0, e') := by
      rw [hsum, map_add, map_add, hY_e0]; abel
    -- `Y (0, v, 0) ∈ flagE`: V₀ and E' components are 0.
    have hY_v_flagE : Y (0, v, 0) ∈ S.flagE :=
      hflagEV0 _ ⟨trivial, trivial, Submodule.zero_mem _⟩
    obtain ⟨_, hY_v_V0, hY_v_E'⟩ := hY_v_flagE
    have hY_v_V0_eq : (Y (0, v, 0)).2.1 = 0 := by
      simpa [Submodule.mem_bot] using hY_v_V0
    have hY_v_E'_eq : (Y (0, v, 0)).2.2 = 0 := by
      simpa [Submodule.mem_bot] using hY_v_E'
    -- `Y (0, 0, e') ∈ flagEV0`: E' component is 0.
    have hY_e'_flagEV0 : Y (0, 0, e') ∈ S.flagEV0 := hAll _
    obtain ⟨_, _, hY_e'_E'⟩ := hY_e'_flagEV0
    have hY_e'_E'_eq : (Y (0, 0, e')).2.2 = 0 := by
      simpa [Submodule.mem_bot] using hY_e'_E'
    -- The V₀-block of `Y` applied to `(0, 0, e'')` is exactly `C e''`
    -- (this is the definition of `C := projV0 ∘ₗ Y ∘ₗ inE'`).
    have hC_eq : ∀ e'' : S.paired.E',
        (projV0 ∘ₗ Y ∘ₗ inE') e'' = (Y (0, 0, e'')).2.1 := by
      intro e''
      simp [projV0, inE', LinearMap.comp_apply]
    -- The E-block of `Y` on `V₀`: `(Y (0, v, 0)).1 = Cdual S C v`.
    -- Proof via the perfect pairing: it suffices to show the two sides
    -- pair to the same value with every `e'' : S.paired.E'`.
    have hY_v_E_eq : (Y (0, v, 0)).1 = Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v := by
      apply S.paired.isPerfect.1
      apply LinearMap.ext
      intro e''
      have h := hSkewY (0, v, 0) (0, 0, e'')
      simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
        LinearMap.zero_apply, mul_zero, add_zero, zero_add] at h
      -- `h : S.paired.pairing (Y(0,v,0)).1 e''
      --        + S.formV0 v (Y(0,0,e'')).2.1 = 0`
      rw [Cdual_pairing_eq S _hNondeg, hC_eq]
      linear_combination h
    -- Reduce LHS via `XCB_apply` and `X0Lift_apply`.
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply, hY_sum]
    -- Decompose into (E, V₀, E') components.
    refine Prod.mk.injEq .. |>.mpr
      ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
    · -- E component: `Cdual C v + B e' - 0 = (Y(0,v,0)).1 + (Y(0,0,e')).1`.
      -- Use `hY_v_E_eq` and `B e' = (Y(0,0,e')).1`.
      have hB_eq : (projE ∘ₗ Y ∘ₗ inE') e' = (Y (0, 0, e')).1 := by
        simp [projE, inE', LinearMap.comp_apply]
      show Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v + (projE ∘ₗ Y ∘ₗ inE') e' - 0
          = (Y (0, v, 0)).1 + (Y (0, 0, e')).1
      rw [sub_zero, hB_eq, ← hY_v_E_eq]
    · -- V₀ component: `X0 v + (projV0 ∘ Y ∘ inE') e' - X0 v
      --   = (Y (0, v, 0)).2.1 + (Y (0, 0, e')).2.1`.
      simp only [hY_v_V0_eq, zero_add]
      simp [projV0, inE', LinearMap.comp_apply]
    · -- E' component: `0 - 0 = (Y (0, v, 0)).2.2 + (Y (0, 0, e')).2.2`.
      simp [hY_v_E'_eq, hY_e'_E'_eq]

/-- Uniqueness in `lem:parametrize-x0-plus-u`: the parameters `(C, B)`
attached to `Y ∈ X₀ + 𝔲` are determined by `Y`. -/
theorem parametrizeX0PlusU_uniqueness (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate)
    (C C' : S.E' →ₗ[F] S.V0) (B B' : S.E' →ₗ[F] S.E)
    (_hB : IsSkewB S B) (_hB' : IsSkewB S B')
    (h : XCB S C B = XCB S C' B') :
    C = C' ∧ B = B' := by
  -- Probe both sides at `(0, 0, e')` for arbitrary `e' : E'`.
  have hprobe : ∀ e' : S.paired.E',
      (XCB S C B) ((0 : S.paired.E), (0 : S.V0), e')
        = (XCB S C' B') ((0 : S.paired.E), (0 : S.V0), e') := by
    intro e'; rw [h]
  refine ⟨?_, ?_⟩
  · -- C = C' from the V₀-component
    apply LinearMap.ext
    intro e'
    have hpr := hprobe e'
    rw [XCB_apply, XCB_apply] at hpr
    -- hpr : (Cdual 0 + B e', X0 0 + C e', 0) = (Cdual 0 + B' e', X0 0 + C' e', 0)
    have h2 := congrArg (fun x => x.2.1) hpr
    simpa using h2
  · -- B = B' from the E-component (after using C = C')
    apply LinearMap.ext
    intro e'
    have hpr := hprobe e'
    rw [XCB_apply, XCB_apply] at hpr
    have h1 := congrArg (fun x => x.1) hpr
    simpa using h1

/-! ## `lem:unipotent-conjugation` — the operator `u_D` -/

/-- For `D : E' →ₗ[F] V₀`, the operator `u_D : V →ₗ[F] V` defined
block-wise by
`(e, v, e') ↦ (e + Cdual D v + ½ Cdual D (D e'), v + D e', e')`.

The factor `½` is encoded as the field inverse `(2 : F)⁻¹`; downstream
theorems requiring the formula to behave correctly carry an explicit
`(2 : F) ≠ 0` hypothesis. -/
noncomputable def uD (S : SliceSetup F) (_D : S.E' →ₗ[F] S.V0) :
    Module.End F S.V :=
  let projE  : S.V →ₗ[F] S.paired.E :=
    LinearMap.fst F S.paired.E (S.V0 × S.paired.E')
  let projV0 : S.V →ₗ[F] S.V0 :=
    LinearMap.fst F S.V0 S.paired.E' ∘ₗ
      LinearMap.snd F S.paired.E (S.V0 × S.paired.E')
  let projE' : S.V →ₗ[F] S.paired.E' :=
    LinearMap.snd F S.V0 S.paired.E' ∘ₗ
      LinearMap.snd F S.paired.E (S.V0 × S.paired.E')
  let inE   : S.paired.E →ₗ[F] S.V :=
    LinearMap.inl F S.paired.E (S.V0 × S.paired.E')
  let inV0  : S.V0 →ₗ[F] S.V :=
    LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
      LinearMap.inl F S.V0 S.paired.E'
  let inE'  : S.paired.E' →ₗ[F] S.V :=
    LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
      LinearMap.inr F S.V0 S.paired.E'
  inE ∘ₗ (projE + (Cdual S _D) ∘ₗ projV0 +
            (2 : F)⁻¹ • ((Cdual S _D) ∘ₗ _D ∘ₗ projE')) +
    inV0 ∘ₗ (projV0 + _D ∘ₗ projE') +
    inE' ∘ₗ projE'

/-- Pointwise formula for `uD`. -/
private lemma uD_apply (S : SliceSetup F) (D : S.E' →ₗ[F] S.V0)
    (e : S.paired.E) (v : S.V0) (e' : S.paired.E') :
    uD S D (e, v, e')
      = (e + Cdual S D v + (2 : F)⁻¹ • Cdual S D (D e'),
          v + D e', e') := by
  unfold uD
  simp

/-- `Cdual` is linear in its `C` argument: `Cdual (-C) = -(Cdual C)`. -/
private lemma Cdual_neg (S : SliceSetup F) (C : S.E' →ₗ[F] S.V0) :
    Cdual S (-C) = -(Cdual S C) := by
  haveI := lambda_isPerfPair S
  unfold Cdual
  -- Both sides equal `S.lambda.toPerfPair.symm.toLinearMap` composed with
  -- the same dual functional, up to sign manipulations.
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.neg_apply,
    LinearEquiv.coe_coe]
  -- Push the negation in `-(Cdual S C v)` through `S.lambda.toPerfPair.symm`.
  rw [← map_neg S.lambda.toPerfPair.symm]
  -- Now both sides are `lambda.toPerfPair.symm` applied to dual functionals;
  -- it suffices to check equality of the functionals.
  congr 1
  ext e'
  simp [LinearMap.dualMap_apply]

/-- The inverse of `uD S D` is `uD S (-D)` (under the standing
hypotheses). -/
theorem uD_neg_inverse (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    (uD S D) ∘ₗ (uD S (-D)) = LinearMap.id := by
  have hhalf : (2 : F)⁻¹ + (2 : F)⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ hChar]
  apply LinearMap.ext
  rintro ⟨e, v, e'⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [uD_apply S (-D) e v e', uD_apply S D]
  -- Push `Cdual (-D) = -(Cdual D)` and distribute.
  rw [Cdual_neg]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩⟩
  · -- E component
    simp only [LinearMap.neg_apply, LinearMap.map_add, LinearMap.map_neg,
      neg_neg]
    -- After distribution the goal is a `S.E`-module identity controlled by
    -- the scalar identity `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`.
    have key :
        ((2 : F)⁻¹ : F) • (Cdual S D) (D e') +
              ((2 : F)⁻¹ : F) • (Cdual S D) (D e')
          = (Cdual S D) (D e') := by
      rw [← add_smul, hhalf, one_smul]
    linear_combination (norm := abel_nf) key
  · -- V0 component: (v + (-D) e') + D e' = v
    rw [LinearMap.neg_apply]
    abel
  -- E' component handled by `rfl` in the outer `Prod.mk.injEq`.

/-- `u_D` is parabolic: it is an isometry of the ambient form and
preserves the flag `0 ≤ E ≤ E ⊕ V₀ ≤ V`.

The isometry conjunct is encoded as
`LinearMap.IsAdjointPair S.ambientForm S.ambientForm (uD D) (uD (-D))`,
which (via `uD_neg_inverse`) is equivalent to
`B (u_D x) (u_D y) = B (x, y)` — the blueprint statement.  Direct
expansion uses `Cdual_pairing_eq`, the ε-symmetry of `S.formV0`, and
`(2 : F)⁻¹ + (2 : F)⁻¹ = 1`. -/
theorem uD_isParabolic (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    LinearMap.IsAdjointPair S.ambientForm S.ambientForm
        (uD S D) (uD S (-D)) ∧
      Submodule.map (uD S D) S.flagE ≤ S.flagE ∧
      Submodule.map (uD S D) S.flagEV0 ≤ S.flagEV0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- IsAdjointPair: B (uD D x) y = B x (uD (-D) y) for all x, y.
    -- Direct expansion: write `uD D` and `uD (-D)` block-wise via
    -- `uD_apply`, distribute through the bilinear `ambientForm`, and
    -- apply `Cdual_pairing_eq` to each `λ(Cdual D v, e')` term.  The
    -- resulting identity in `B₀` and `λ` closes via ε-symmetry,
    -- `ε² = 1`, and `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`.
    intro x y
    obtain ⟨e₁, v₁, e₁'⟩ := x
    obtain ⟨e₂, v₂, e₂'⟩ := y
    rw [uD_apply S D e₁ v₁ e₁', uD_apply S (-D) e₂ v₂ e₂', Cdual_neg]
    simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, LinearMap.map_add,
      LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, LinearMap.neg_apply, LinearMap.map_neg, neg_neg]
    rw [Cdual_pairing_eq S _hNondeg D v₁ e₂',
        Cdual_pairing_eq S _hNondeg D (D e₁') e₂',
        Cdual_pairing_eq S _hNondeg D v₂ e₁',
        Cdual_pairing_eq S _hNondeg D (D e₂') e₁']
    have hε := S.epsSymm
    have hε2 : S.eps * S.eps = 1 := by
      rcases S.epsValid with h | h <;> simp [h]
    have hC : S.formV0 v₂ (D e₁') = S.eps * S.formV0 (D e₁') v₂ := hε _ _
    have hD' : S.formV0 (D e₂') (D e₁') = S.eps * S.formV0 (D e₁') (D e₂') :=
      hε _ _
    linear_combination
      (-S.eps) * hC + (S.eps * (2 : F)⁻¹) * hD'
        + (S.formV0 (D e₁') (D e₂') * (2 : F)⁻¹ - S.formV0 (D e₁') v₂) * hε2
  · -- `u_D` maps `flagE` into itself.
    rintro x ⟨⟨e, v, e'⟩, hin, rfl⟩
    rcases hin with ⟨_, hv, he'⟩
    have hv0 : v = 0 := by simpa using hv
    have he'0 : e' = 0 := by simpa using he'
    rw [uD_apply, hv0, he'0]
    refine ⟨trivial, ?_, ?_⟩ <;> simp
  · -- `u_D` maps `flagEV0` into itself.
    rintro x ⟨⟨e, v, e'⟩, hin, rfl⟩
    rcases hin with ⟨_, _, he'⟩
    have he'0 : e' = 0 := by simpa using he'
    rw [uD_apply, he'0]
    refine ⟨trivial, trivial, ?_⟩
    simp

/-- A version of `Cdual_pairing_eq` with no `Nondegenerate` hypothesis,
suitable for internal use. -/
private lemma Cdual_pairing (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (v : S.V0) (e' : S.paired.E') :
    S.lambda (Cdual S C v) e' = - S.formV0 v (C e') := by
  haveI := lambda_isPerfPair S
  show S.lambda
        (S.lambda.toPerfPair.symm
          ((-(C.dualMap.comp S.formV0)) v)) e' = _
  rw [S.lambda.apply_symm_toPerfPair_self]
  simp [LinearMap.dualMap_apply]

/-- The "twisted" identity `Cdual D ∘ X₀ = -Cdual (X₀ ∘ D)`, which
expresses the compatibility of `Cdual` with the skew-adjoint `X₀`. -/
private lemma Cdual_X0_apply (S : SliceSetup F) (D : S.E' →ₗ[F] S.V0)
    (v : S.V0) :
    (Cdual S D) (S.X0 v) = -((Cdual S (S.X0 ∘ₗ D)) v) := by
  haveI := lambda_isPerfPair S
  apply S.lambda.toPerfPair.injective
  apply LinearMap.ext
  intro e'
  rw [LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply]
  rw [Cdual_pairing]
  rw [show S.lambda (-((Cdual S (S.X0 ∘ₗ D)) v)) e'
        = -(S.lambda ((Cdual S (S.X0 ∘ₗ D)) v) e')
        from by rw [LinearMap.map_neg, LinearMap.neg_apply]]
  rw [Cdual_pairing]
  -- LHS: -S.formV0 (S.X0 v) (D e')
  -- RHS: -(-S.formV0 v ((S.X0 ∘ₗ D) e')) = S.formV0 v (S.X0 (D e'))
  -- Use S.skew: S.formV0 (S.X0 v) (D e') + S.formV0 v (S.X0 (D e')) = 0
  have hskew := S.skew v (D e')
  show -S.formV0 (S.X0 v) (D e') = -(-S.formV0 v ((S.X0 ∘ₗ D) e'))
  rw [LinearMap.comp_apply]
  linear_combination -hskew

/-- `ε² = 1` from the `epsValid` disjunct. -/
private lemma eps_sq_eq_one (S : SliceSetup F) : S.eps * S.eps = 1 := by
  rcases S.epsValid with h | h <;> simp [h]

/-- Conjugation formula: `u_D · X_{C,B} · u_D⁻¹ = X_{C', B'}` for the
explicit parameters `C' = C - X₀ ∘ D` and
`B' = B + Cdual D ∘ C - Cdual C ∘ D - Cdual D ∘ X₀ ∘ D`.

The skewness condition on `B'` is part of the conclusion. -/
theorem uD_conj_XCB (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (hB : IsSkewB S B) :
    ∃ (C' : S.E' →ₗ[F] S.V0) (B' : S.E' →ₗ[F] S.E),
      IsSkewB S B' ∧
      (uD S D) ∘ₗ (XCB S C B) ∘ₗ (uD S (-D)) = XCB S C' B' := by
  -- The blueprint formulas:
  let C' : S.E' →ₗ[F] S.V0 := C - S.X0 ∘ₗ D
  let B' : S.E' →ₗ[F] S.E :=
    B + (Cdual S D) ∘ₗ C - (Cdual S C) ∘ₗ D - (Cdual S D) ∘ₗ S.X0 ∘ₗ D
  refine ⟨C', B', ?_, ?_⟩
  · -- IsSkewB B'.  Apply `S.lambda` and reduce via `Cdual_pairing`.
    intro u v
    -- Pointwise expand.
    show S.lambda (B' u) v + S.eps * S.lambda (B' v) u = 0
    -- Expand `B'(u)` and `B'(v)`.
    have hB'u :
        B' u = B u + Cdual S D (C u) - Cdual S C (D u) - Cdual S D (S.X0 (D u)) := by
      simp [B', LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply]
    have hB'v :
        B' v = B v + Cdual S D (C v) - Cdual S C (D v) - Cdual S D (S.X0 (D v)) := by
      simp [B', LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.comp_apply]
    rw [hB'u, hB'v]
    -- Distribute λ and use Cdual_pairing on each Cdual term.
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
      Cdual_pairing]
    -- Now everything is in terms of `B0 = S.formV0` and `λ(B u, v)`.
    -- Use ε-symmetry of S.formV0.
    have hε := S.epsSymm
    have hε2 := eps_sq_eq_one S
    have hskewB := hB u v
    have hskewX0 := S.skew (D u) (D v)
    -- Goal:
    --   (λ(B u, v) - B0(C u, D v) + B0(D u, C v) + B0(X0 (D u), D v))
    --   + ε ((λ(B v, u) - B0(C v, D u) + B0(D v, C u) + B0(X0 (D v), D u))) = 0
    --
    -- Expand and use ε² = 1.  Each ε * (- B0 a b) becomes - B0 b a, and the
    -- B0 cancellations and S.skew at (D u, D v) close the goal.
    --
    -- Concretely: rewrite `S.formV0 a b = S.eps * S.formV0 b a` for swapped pairs.
    have hCv_Du : S.formV0 (C v) (D u) = S.eps * S.formV0 (D u) (C v) := hε _ _
    have hDv_Cu : S.formV0 (D v) (C u) = S.eps * S.formV0 (C u) (D v) := hε _ _
    have hX0Dv_Du : S.formV0 (S.X0 (D v)) (D u) = S.eps * S.formV0 (D u) (S.X0 (D v)) :=
      hε _ _
    -- Substitute in goal and finish via `linear_combination`.
    -- See the textual proof in this comment block for the derivation:
    -- G = hskewB + hskewX0 + (-ε)*hCv_Du + ε*hDv_Cu + ε*hX0Dv_Du
    --     + (B0(Cu, Dv) - B0(Du, Cv) + B0(Du, X0(Dv))) * (eps² - 1)
    linear_combination
      hskewB + hskewX0
        + (-S.eps) * hCv_Du
        + S.eps * hDv_Cu
        + S.eps * hX0Dv_Du
        + ((S.formV0 (C u) (D v)) - (S.formV0 (D u) (C v))
            + (S.formV0 (D u) (S.X0 (D v)))) * hε2
  · -- The conjugation equation.  Block-matrix calculation on
    -- `V = E × V₀ × E'`.
    -- Helper: `Cdual` is additive in its `C` argument.
    have Cdual_add : ∀ (C₁ C₂ : S.E' →ₗ[F] S.V0),
        Cdual S (C₁ + C₂) = Cdual S C₁ + Cdual S C₂ := by
      intro C₁ C₂
      haveI := lambda_isPerfPair S
      apply LinearMap.ext
      intro w
      apply S.lambda.toPerfPair.injective
      apply LinearMap.ext
      intro e''
      rw [LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply]
      rw [LinearMap.add_apply, map_add, LinearMap.add_apply,
        Cdual_pairing, Cdual_pairing, Cdual_pairing]
      simp [LinearMap.add_apply]
      ring
    -- Helper: `Cdual` is subtractive.
    have Cdual_sub_apply : ∀ (C₁ C₂ : S.E' →ₗ[F] S.V0) (w : S.V0),
        Cdual S (C₁ - C₂) w = Cdual S C₁ w - Cdual S C₂ w := by
      intro C₁ C₂ w
      have h : C₁ - C₂ = C₁ + (-C₂) := by abel
      rw [h, Cdual_add, Cdual_neg]
      simp [LinearMap.add_apply, LinearMap.neg_apply, sub_eq_add_neg]
    apply LinearMap.ext
    rintro ⟨e, v, e'⟩
    simp only [LinearMap.comp_apply]
    rw [uD_apply S (-D) e v e']
    rw [Cdual_neg]
    rw [XCB_apply]
    rw [uD_apply]
    rw [XCB_apply]
    -- Now both sides are big tuples; show component-wise.
    refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩⟩
    · -- E component.
      have hX0 : (Cdual S D) (S.X0 v) = -((Cdual S (S.X0 ∘ₗ D)) v) :=
        Cdual_X0_apply S D v
      -- Unfold the local `let`s for `C'` and `B'`.
      show _ = (Cdual S (C - S.X0 ∘ₗ D)) v
                + (B + Cdual S D ∘ₗ C - Cdual S C ∘ₗ D
                    - Cdual S D ∘ₗ S.X0 ∘ₗ D) e'
      rw [Cdual_sub_apply]
      simp only [LinearMap.map_zero, smul_zero, add_zero,
        LinearMap.map_add, LinearMap.map_neg,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.neg_apply]
      rw [hX0]
      abel
    · -- V0 component.
      show _ + _ = _ + (C - S.X0 ∘ₗ D) e'
      simp only [LinearMap.map_zero, add_zero,
        LinearMap.map_add, LinearMap.map_neg,
        LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.neg_apply]
      abel
    -- E' component: handled by `rfl` in `refine`.

/-! ## Levi-action machinery (Round 6 additive layer)

Block-diagonal embeddings of `GL(E')` and `G_0` (isometry group of
`formV0`) into the parabolic, plus the conjugation transformation of
`XCB`. Used by `NormalForm.lean` (Round 7) for `pNormalForm_witnesses`,
`residual_levi_extract`, `residual_levi_build`. -/

/-! ### Section 6.1 — Dual transpose on `E` -/

/-- For `g : S.E' →ₗ[F] S.E'`, the **dual transpose** `g^∨ : S.E →ₗ[F] S.E`
under the perfect pairing `S.lambda`. Defined by the universal property
`λ(g^∨ e, e') = λ(e, g e')`.

This packages `LinearMap.IsPerfPair`'s round-trip: given `e : S.E`, the
functional `e' ↦ S.lambda e (g e')` is in `Module.Dual F S.E'`, which
the perfect pairing identifies with `S.E`. -/
noncomputable def lambdaDualE (S : SliceSetup F)
    (g : S.E' →ₗ[F] S.E') : S.E →ₗ[F] S.E :=
  haveI := lambda_isPerfPair S
  S.lambda.toPerfPair.symm.toLinearMap.comp (g.dualMap.comp S.lambda)

/-- Defining identity for `lambdaDualE`. -/
theorem lambdaDualE_pairing_eq (S : SliceSetup F)
    (g : S.E' →ₗ[F] S.E') (e : S.E) (e' : S.E') :
    S.lambda (lambdaDualE S g e) e' = S.lambda e (g e') := by
  haveI := lambda_isPerfPair S
  show S.lambda
        (S.lambda.toPerfPair.symm
          ((g.dualMap.comp S.lambda) e)) e' = _
  rw [S.lambda.apply_symm_toPerfPair_self]
  simp [LinearMap.dualMap_apply]

/-- The dual transpose preserves identity. -/
theorem lambdaDualE_id (S : SliceSetup F) :
    lambdaDualE S (LinearMap.id : S.E' →ₗ[F] S.E') = LinearMap.id := by
  apply LinearMap.ext
  intro e
  apply S.paired.isPerfect.1
  apply LinearMap.ext
  intro e'
  rw [lambdaDualE_pairing_eq]
  rfl

/-- The dual transpose is contravariant in composition. -/
theorem lambdaDualE_comp (S : SliceSetup F)
    (g₁ g₂ : S.E' →ₗ[F] S.E') :
    lambdaDualE S (g₁ ∘ₗ g₂) =
      lambdaDualE S g₂ ∘ₗ lambdaDualE S g₁ := by
  apply LinearMap.ext
  intro e
  apply S.paired.isPerfect.1
  apply LinearMap.ext
  intro e'
  -- Goal: S.lambda (lambdaDualE S (g₁ ∘ₗ g₂) e) e' = S.lambda ((lambdaDualE S g₂ ∘ₗ lambdaDualE S g₁) e) e'
  show S.lambda (lambdaDualE S (g₁ ∘ₗ g₂) e) e'
      = S.lambda (lambdaDualE S g₂ (lambdaDualE S g₁ e)) e'
  rw [lambdaDualE_pairing_eq, lambdaDualE_pairing_eq, lambdaDualE_pairing_eq]
  rfl

/-- `lambdaDualE` of an iso composed with its inverse (E' side first). -/
private lemma lambdaDualE_symm_comp (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') :
    lambdaDualE S (d.symm : S.E' →ₗ[F] S.E') ∘ₗ
        lambdaDualE S (d : S.E' →ₗ[F] S.E')
      = LinearMap.id := by
  rw [← lambdaDualE_comp]
  have hdd : (d : S.E' →ₗ[F] S.E') ∘ₗ (d.symm : S.E' →ₗ[F] S.E')
      = LinearMap.id := by
    ext e''; simp
  rw [hdd, lambdaDualE_id]

/-- `lambdaDualE` of an iso composed with its inverse (E side first). -/
private lemma lambdaDualE_comp_symm (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') :
    lambdaDualE S (d : S.E' →ₗ[F] S.E') ∘ₗ
        lambdaDualE S (d.symm : S.E' →ₗ[F] S.E')
      = LinearMap.id := by
  rw [← lambdaDualE_comp]
  have hdd : (d.symm : S.E' →ₗ[F] S.E') ∘ₗ (d : S.E' →ₗ[F] S.E')
      = LinearMap.id := by
    ext e''; simp
  rw [hdd, lambdaDualE_id]

/-! ### Section 6.2 — Levi block embeddings -/

/-- The Levi `GL(E')` block: for an iso `d : S.E' ≃ₗ[F] S.E'`, the action
on `S.V = S.E × S.V0 × S.E'` is `((d⁻¹)^∨, id_{V0}, d)`. -/
noncomputable def leviGL_E (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') : Module.End F S.V :=
  LinearMap.inl F S.E (S.V0 × S.E')
      ∘ₗ lambdaDualE S (d.symm : S.E' →ₗ[F] S.E')
      ∘ₗ LinearMap.fst F S.E (S.V0 × S.E') +
    LinearMap.inr F S.E (S.V0 × S.E')
      ∘ₗ (LinearMap.inl F S.V0 S.E'
            ∘ₗ LinearMap.fst F S.V0 S.E'
            ∘ₗ LinearMap.snd F S.E (S.V0 × S.E')) +
    LinearMap.inr F S.E (S.V0 × S.E')
      ∘ₗ (LinearMap.inr F S.V0 S.E'
            ∘ₗ (d : S.E' →ₗ[F] S.E')
            ∘ₗ LinearMap.snd F S.V0 S.E'
            ∘ₗ LinearMap.snd F S.E (S.V0 × S.E'))

/-- The Levi `G_0` block: for `g : S.V0 ≃ₗ[F] S.V0`, the action on
`S.V` is `(id_E, g, id_{E'})`. The definition does not depend on `g`
being an isometry; only the parabolicity proof does. -/
noncomputable def leviGL_V0 (S : SliceSetup F)
    (g : S.V0 ≃ₗ[F] S.V0) : Module.End F S.V :=
  LinearMap.inl F S.E (S.V0 × S.E')
      ∘ₗ LinearMap.fst F S.E (S.V0 × S.E') +
    LinearMap.inr F S.E (S.V0 × S.E')
      ∘ₗ (LinearMap.inl F S.V0 S.E' ∘ₗ (g : S.V0 →ₗ[F] S.V0)
            ∘ₗ LinearMap.fst F S.V0 S.E'
            ∘ₗ LinearMap.snd F S.E (S.V0 × S.E')) +
    LinearMap.inr F S.E (S.V0 × S.E')
      ∘ₗ (LinearMap.inr F S.V0 S.E'
            ∘ₗ LinearMap.snd F S.V0 S.E'
            ∘ₗ LinearMap.snd F S.E (S.V0 × S.E'))

/-- Pointwise formula for `leviGL_E`. -/
theorem leviGL_E_apply (S : SliceSetup F) (d : S.E' ≃ₗ[F] S.E')
    (e : S.E) (v : S.V0) (e' : S.E') :
    leviGL_E S d (e, v, e') =
      (lambdaDualE S (d.symm : S.E' →ₗ[F] S.E') e, v, d e') := by
  unfold leviGL_E
  simp

/-- Pointwise formula for `leviGL_V0`. -/
theorem leviGL_V0_apply (S : SliceSetup F) (g : S.V0 ≃ₗ[F] S.V0)
    (e : S.E) (v : S.V0) (e' : S.E') :
    leviGL_V0 S g (e, v, e') = (e, g v, e') := by
  unfold leviGL_V0
  simp

/-! ### Section 6.3 — Inverses -/

/-- `leviGL_E d.symm ∘ leviGL_E d = id`. -/
theorem leviGL_E_symm_inverse (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') :
    leviGL_E S d.symm ∘ₗ leviGL_E S d = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨e, v, e'⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [leviGL_E_apply, leviGL_E_apply]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨rfl, ?_⟩⟩
  · -- E component: lambdaDualE S d.symm.symm (lambdaDualE S d.symm e) = e
    -- (d.symm.symm = d definitionally)
    show lambdaDualE S ((d.symm).symm : S.E' →ₗ[F] S.E')
            (lambdaDualE S (d.symm : S.E' →ₗ[F] S.E') e) = e
    have h := lambdaDualE_comp_symm S d
    have := congrArg (fun (f : S.E →ₗ[F] S.E) => f e) h
    simpa using this
  · -- E' component: d.symm (d e') = e'
    show d.symm (d e') = e'
    simp

/-- `leviGL_V0 g.symm ∘ leviGL_V0 g = id`. -/
theorem leviGL_V0_symm_inverse (S : SliceSetup F)
    (g : S.V0 ≃ₗ[F] S.V0) :
    leviGL_V0 S g.symm ∘ₗ leviGL_V0 S g = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨e, v, e'⟩
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [leviGL_V0_apply, leviGL_V0_apply]
  refine Prod.mk.injEq .. |>.mpr ⟨rfl, Prod.mk.injEq .. |>.mpr ⟨?_, rfl⟩⟩
  show g.symm (g v) = v
  simp

/-! ### Section 6.4 — Parabolicity -/

/-- `leviGL_E d` is in the parabolic. -/
theorem leviGL_E_isParabolic (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') :
    IsUnit (leviGL_E S d) ∧
      Submodule.map (leviGL_E S d) S.flagE = S.flagE ∧
      Submodule.map (leviGL_E S d) S.flagEV0 = S.flagEV0 ∧
      LinearMap.IsOrthogonal S.ambientForm (leviGL_E S d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- IsUnit (leviGL_E S d): use the symm inverse with d.symm.
    -- leviGL_E_symm_inverse S d.symm : leviGL_E S d.symm.symm ∘ₗ leviGL_E S d.symm = id.
    -- d.symm.symm = d definitionally.
    have hsymm := leviGL_E_symm_inverse S d.symm
    have h : leviGL_E S d * leviGL_E S d.symm = 1 := hsymm
    exact (Units.mkOfMulEqOne _ _ h).isUnit
  · -- Submodule.map (leviGL_E d) flagE = flagE
    apply le_antisymm
    · rintro x ⟨⟨e, v, e'⟩, hin, rfl⟩
      rcases hin with ⟨_, hv, he'⟩
      have hv0 : v = 0 := by simpa using hv
      have he'0 : e' = 0 := by simpa using he'
      rw [leviGL_E_apply, hv0, he'0]
      refine ⟨trivial, ?_, ?_⟩ <;> simp
    · rintro ⟨e, v, e'⟩ ⟨_, hv, he'⟩
      have hv0 : v = 0 := by simpa using hv
      have he'0 : e' = 0 := by simpa using he'
      refine ⟨(lambdaDualE S (d : S.E' →ₗ[F] S.E') e, 0, 0), ?_, ?_⟩
      · refine ⟨trivial, ?_, ?_⟩ <;> simp
      · rw [leviGL_E_apply]
        refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
        · -- lambdaDualE d.symm (lambdaDualE d e) = e
          have h := lambdaDualE_symm_comp S d
          have := congrArg (fun (f : S.E →ₗ[F] S.E) => f e) h
          simpa using this
        · simp [hv0]
        · rw [he'0]; simp
  · -- Submodule.map (leviGL_E d) flagEV0 = flagEV0
    apply le_antisymm
    · rintro x ⟨⟨e, v, e'⟩, hin, rfl⟩
      rcases hin with ⟨_, _, he'⟩
      have he'0 : e' = 0 := by simpa using he'
      rw [leviGL_E_apply, he'0]
      refine ⟨trivial, trivial, ?_⟩
      simp
    · rintro ⟨e, v, e'⟩ ⟨_, _, he'⟩
      have he'0 : e' = 0 := by simpa using he'
      refine ⟨(lambdaDualE S (d : S.E' →ₗ[F] S.E') e, v, 0), ?_, ?_⟩
      · refine ⟨trivial, trivial, ?_⟩; simp
      · rw [leviGL_E_apply]
        refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨rfl, ?_⟩⟩
        · have h := lambdaDualE_symm_comp S d
          have := congrArg (fun (f : S.E →ₗ[F] S.E) => f e) h
          simpa using this
        · rw [he'0]; simp
  · -- LinearMap.IsOrthogonal S.ambientForm (leviGL_E S d)
    intro x y
    obtain ⟨e₁, v₁, e₁'⟩ := x
    obtain ⟨e₂, v₂, e₂'⟩ := y
    rw [leviGL_E_apply, leviGL_E_apply]
    simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply]
    rw [lambdaDualE_pairing_eq, lambdaDualE_pairing_eq]
    simp

/-- `leviGL_V0 g` is in the parabolic, when `g` is a `formV0`-isometry. -/
theorem leviGL_V0_isParabolic (S : SliceSetup F)
    (g : S.V0 ≃ₗ[F] S.V0)
    (hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v) :
    IsUnit (leviGL_V0 S g) ∧
      Submodule.map (leviGL_V0 S g) S.flagE = S.flagE ∧
      Submodule.map (leviGL_V0 S g) S.flagEV0 = S.flagEV0 ∧
      LinearMap.IsOrthogonal S.ambientForm (leviGL_V0 S g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsymm := leviGL_V0_symm_inverse S g.symm
    have h : leviGL_V0 S g * leviGL_V0 S g.symm = 1 := hsymm
    exact (Units.mkOfMulEqOne _ _ h).isUnit
  · -- map flagE = flagE
    apply le_antisymm
    · rintro x ⟨⟨e, v, e'⟩, hin, rfl⟩
      rcases hin with ⟨_, hv, he'⟩
      have hv0 : v = 0 := by simpa using hv
      have he'0 : e' = 0 := by simpa using he'
      rw [leviGL_V0_apply, hv0, he'0]
      refine ⟨trivial, ?_, ?_⟩ <;> simp
    · rintro ⟨e, v, e'⟩ ⟨_, hv, he'⟩
      have hv0 : v = 0 := by simpa using hv
      have he'0 : e' = 0 := by simpa using he'
      refine ⟨(e, 0, 0), ?_, ?_⟩
      · refine ⟨trivial, ?_, ?_⟩ <;> simp
      · rw [leviGL_V0_apply]
        refine Prod.mk.injEq .. |>.mpr ⟨rfl, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
        · simp [hv0]
        · rw [he'0]
  · -- map flagEV0 = flagEV0
    apply le_antisymm
    · rintro x ⟨⟨e, v, e'⟩, hin, rfl⟩
      rcases hin with ⟨_, _, he'⟩
      have he'0 : e' = 0 := by simpa using he'
      rw [leviGL_V0_apply, he'0]
      refine ⟨trivial, trivial, ?_⟩
      simp
    · rintro ⟨e, v, e'⟩ ⟨_, _, he'⟩
      have he'0 : e' = 0 := by simpa using he'
      refine ⟨(e, g.symm v, 0), ?_, ?_⟩
      · refine ⟨trivial, trivial, ?_⟩; simp
      · rw [leviGL_V0_apply]
        refine Prod.mk.injEq .. |>.mpr ⟨rfl, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
        · simp
        · rw [he'0]
  · -- IsOrthogonal
    intro x y
    obtain ⟨e₁, v₁, e₁'⟩ := x
    obtain ⟨e₂, v₂, e₂'⟩ := y
    rw [leviGL_V0_apply, leviGL_V0_apply]
    simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply]
    rw [hg]

/-! ### Section 6.5 — Conjugation transformation of `XCB` -/

/-- Compatibility of `lambdaDualE` and `Cdual`: precomposing `Cdual S C`
with `lambdaDualE S g` corresponds to postcomposing `C` with `g`. -/
private lemma lambdaDualE_Cdual (S : SliceSetup F)
    (g : S.E' →ₗ[F] S.E') (C : S.E' →ₗ[F] S.V0) (v : S.V0) :
    lambdaDualE S g (Cdual S C v) = Cdual S (C ∘ₗ g) v := by
  apply S.paired.isPerfect.1
  apply LinearMap.ext
  intro e''
  rw [lambdaDualE_pairing_eq, Cdual_pairing, Cdual_pairing]
  rfl

/-- Levi-conjugation of `XCB` on `E'`: `leviGL_E d ∘ XCB(C, B) =
XCB(C ∘ d⁻¹, (d⁻¹)^∨ ∘ B ∘ d⁻¹) ∘ leviGL_E d`. -/
theorem leviGL_E_conj_XCB (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E')
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) :
    leviGL_E S d ∘ₗ XCB S C B =
      XCB S (C ∘ₗ (d.symm : S.E' →ₗ[F] S.E'))
            (lambdaDualE S (d.symm : S.E' →ₗ[F] S.E')
              ∘ₗ B ∘ₗ (d.symm : S.E' →ₗ[F] S.E'))
        ∘ₗ leviGL_E S d := by
  apply LinearMap.ext
  rintro ⟨e, v, e'⟩
  simp only [LinearMap.comp_apply]
  rw [XCB_apply, leviGL_E_apply, leviGL_E_apply, XCB_apply]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · -- E component
    show lambdaDualE S (d.symm : S.E' →ₗ[F] S.E') (Cdual S C v + B e')
        = Cdual S (C ∘ₗ (d.symm : S.E' →ₗ[F] S.E')) v
            + (lambdaDualE S (d.symm : S.E' →ₗ[F] S.E')
                ∘ₗ B ∘ₗ (d.symm : S.E' →ₗ[F] S.E')) (d e')
    rw [LinearMap.map_add, lambdaDualE_Cdual]
    simp [LinearMap.comp_apply]
  · -- V0 component
    show S.X0 v + C e' = S.X0 v + (C ∘ₗ (d.symm : S.E' →ₗ[F] S.E')) (d e')
    simp [LinearMap.comp_apply]
  · -- E' component: d 0 = 0
    simp

/-- Levi-conjugation of `XCB` on `V0`: when `g` commutes with `S.X0`
**and** the `g`-image of `C` agrees pairwise with `C` w.r.t. `formV0`,
`leviGL_V0 g ∘ XCB(C, B) = XCB(g ∘ C, B) ∘ leviGL_V0 g`.

The `formV0`-isometry hypothesis on `g` is sufficient to derive the
pairwise condition `hgC` (specialise `hg u v := S.formV0 (g u) (g v) =
S.formV0 u v` to `(v, C e'')`). For maximum reusability we keep `hgC`
explicit and stated in `LinearMap`-coerced form. -/
theorem leviGL_V0_conj_XCB (S : SliceSetup F)
    (g : S.V0 ≃ₗ[F] S.V0)
    (hgX : (g : S.V0 →ₗ[F] S.V0) ∘ₗ S.X0
            = S.X0 ∘ₗ (g : S.V0 →ₗ[F] S.V0))
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (hgC : ∀ v e'',
        S.formV0 (g v)
            ((g : S.V0 →ₗ[F] S.V0) (C e''))
          = S.formV0 v (C e'')) :
    leviGL_V0 S g ∘ₗ XCB S C B =
      XCB S ((g : S.V0 →ₗ[F] S.V0) ∘ₗ C) B ∘ₗ leviGL_V0 S g := by
  apply LinearMap.ext
  rintro ⟨e, v, e'⟩
  simp only [LinearMap.comp_apply]
  rw [XCB_apply, leviGL_V0_apply, leviGL_V0_apply, XCB_apply]
  refine Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · -- E component: Cdual S C v + B e' = Cdual S (g ∘ C) (g v) + B e'
    -- (Cdual is invariant under the simultaneous (g, g ∘ C)-shift by hgC.)
    have hC : Cdual S C v = Cdual S ((g : S.V0 →ₗ[F] S.V0) ∘ₗ C) (g v) := by
      apply S.paired.isPerfect.1
      apply LinearMap.ext
      intro e''
      rw [Cdual_pairing, Cdual_pairing, LinearMap.comp_apply]
      rw [hgC]
    rw [hC]
  · -- V0 component: g (X0 v + C e') = X0 (g v) + (g ∘ C) e'
    show (g : S.V0 →ₗ[F] S.V0) (S.X0 v + C e')
        = S.X0 ((g : S.V0 →ₗ[F] S.V0) v)
            + ((g : S.V0 →ₗ[F] S.V0) ∘ₗ C) e'
    rw [LinearMap.map_add]
    have hgXv := congrArg (fun (f : S.V0 →ₗ[F] S.V0) => f v) hgX
    simp only [LinearMap.comp_apply] at hgXv
    rw [hgXv]
    rfl
  · -- E' component
    rfl

/-! ### Section 6.6 — Levi/unipotent decomposition (deferred)

The structural Levi/unipotent decomposition `parabolic_decompose`:
every `IsParabolicElement` factors as `uD D ∘ leviGL_E d ∘ leviGL_V0 g₀`.

Per Round 6 plan (`PROGRESS.md` lines 110–113 and `informal/levi.md`
§6.6), this theorem is the hardest piece of Round 6 and is **deferred**
to Round 7. The proof outline (informal/levi.md §6.6) extracts `g₀` from
the action on `flagEV0 / flagE ≃ V0`, `(d⁻¹)^∨` from the action on
`flagE = E`, and `D` from the residual off-diagonal mass via
`parametrizeX0PlusU_uniqueness`.

The formal proof is sketched below as `parabolic_decompose` carrying
a `sorry` with a one-line gap explanation. Round 7's NormalForm prover
may either close it here in `Slice.lean` (additively) or work around it
for `residual_levi_extract` only by using `parametrizeX0PlusU_uniqueness`
+ the `leviGL_*_isParabolic` machinery directly. -/

/-- Levi/unipotent decomposition of a parabolic element. Deferred to
Round 7 (see preceding comment block).

**Gap:** The full proof requires (a) descending `p` to a quotient
`flagEV0 / flagE ≃ V0` to extract the `g₀ : V0 ≃ V0` block, (b) reading
off `(d⁻¹)^∨` from the action of `p` on `flagE = E` using the
`Submodule.map p S.flagE = S.flagE` conjunct of `IsParabolicElement`,
and (c) inverting `parametrizeX0PlusU_uniqueness` on `p ∘ₗ
(leviGL_E d ∘ₗ leviGL_V0 g)⁻¹` to recover the unipotent residue. Each
step is several dozen lines, so it is best handled in Round 7 alongside
the `residual_levi_extract` consumer. -/
theorem parabolic_decompose (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (p : Module.End F S.V)
    (_hpUnit : IsUnit p)
    (_hpFlagE : Submodule.map p S.flagE = S.flagE)
    (_hpFlagEV0 : Submodule.map p S.flagEV0 = S.flagEV0)
    (_hpIso : LinearMap.IsOrthogonal S.ambientForm p) :
    ∃ (D : S.E' →ₗ[F] S.V0) (d : S.E' ≃ₗ[F] S.E')
      (g : S.V0 ≃ₗ[F] S.V0)
      (_ : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v),
      p = uD S D ∘ₗ leviGL_E S d ∘ₗ leviGL_V0 S g := by
  sorry

end InducedOrbitToy
