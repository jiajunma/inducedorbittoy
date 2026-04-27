import InducedOrbitToy.Basic

/-!
# `lem:x0-geometry`

Autoformalization of `lem:x0-geometry` from
`references/blueprint_verified.md` (lines 1–55).

Informal statement.  Let `V0` be a finite-dimensional `F`-vector space carrying
an `ε`-symmetric bilinear form `B`, let `X0 : V0 →ₗ[F] V0` be skew-adjoint with
respect to `B`, and let `Vplus` be a complement of `Im X0` in `V0`.  Then

* `(Im X0)⊥ = ker X0`,
* `dim (V0 / Im X0) = dim (ker X0) =: c`,
* the quotient map identifies `Vplus` with `V0 / Im X0`,
* the induced pairing `Vplus × ker X0 → F` is perfect, and
* for any isomorphism `T : L1' ≃ Vplus`, the dual map
  `T^∨` restricts to an isomorphism `ker X0 ≃ L1`.

The signatures below consume a bundled `(S : X0Setup F)` from
`InducedOrbitToy.Basic`, which packages the form `S.formV0`, the skew-adjoint
endomorphism `S.X0`, the chosen complement `S.Vplus`, and the supporting
hypotheses (`S.epsValid`, `S.epsSymm`, `S.skew`, `S.isCompl`).  Only the
non-degeneracy of `S.formV0` is taken as an explicit hypothesis (it is not
part of `X0Setup`).  The kernel-dimension constant `c S` from
`InducedOrbitToy.Basic` is reused throughout.
-/

namespace InducedOrbitToy

open LinearMap

variable {F : Type*} [Field F]

/-! ### Inclusion `ker X0 ≤ (Im X0)⊥` -/

/-- For any skew-adjoint `S.X0` with respect to `S.formV0`, the kernel of
`S.X0` is contained in the `S.formV0`-orthogonal of the range of `S.X0`. -/
theorem ker_le_orthogonal_range (S : X0Setup F) :
    LinearMap.ker S.X0 ≤ S.formV0.orthogonal (LinearMap.range S.X0) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rcases hy with ⟨z, rfl⟩
  change S.formV0 (S.X0 z) x = 0
  have hskew := S.skew z x
  have hx0 : S.X0 x = 0 := hx
  rw [hx0, map_zero] at hskew
  simpa using hskew

/-! ### `(Im X0)⊥ = ker X0` -/

/-- If `S.formV0` is non-degenerate (and the bundled `ε`-symmetry and
skew-adjointness hold via `S`), then the orthogonal complement of `Im S.X0`
equals `ker S.X0`. -/
theorem orthogonal_range_eq_ker (S : X0Setup F)
    (hnondeg : S.formV0.Nondegenerate) :
    S.formV0.orthogonal (LinearMap.range S.X0) = LinearMap.ker S.X0 := by
  have href : S.formV0.IsRefl := by
    intro x y hxy
    have h := S.epsSymm y x
    simpa [hxy] using h
  have hle : LinearMap.ker S.X0 ≤ S.formV0.orthogonal (LinearMap.range S.X0) :=
    ker_le_orthogonal_range S
  symm
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have horth :=
    LinearMap.BilinForm.finrank_orthogonal hnondeg href (LinearMap.range S.X0)
  have hrank := LinearMap.finrank_range_add_finrank_ker S.X0
  omega

/-! ### Dimension equality `dim (V0 / Im X0) = dim (ker X0)` -/

/-- Rank–nullity in disguise: the quotient by the range has the same finite
dimension as the kernel. -/
theorem finrank_quotient_range_eq_finrank_ker (S : X0Setup F) :
    Module.finrank F (S.V0 ⧸ LinearMap.range S.X0)
      = Module.finrank F (LinearMap.ker S.X0) := by
  exact (c_eq_finrank_quotient S).symm

/-- The fixed complement `S.Vplus` of `Im S.X0` has dimension equal to `c S`. -/
theorem finrank_Vplus_eq_c (S : X0Setup F) :
    Module.finrank F S.Vplus = c S := by
  let e : (S.V0 ⧸ LinearMap.range S.X0) ≃ₗ[F] S.Vplus :=
    Submodule.quotientEquivOfIsCompl (LinearMap.range S.X0) S.Vplus S.isCompl.symm
  calc
    Module.finrank F S.Vplus = Module.finrank F (S.V0 ⧸ LinearMap.range S.X0) :=
      (LinearEquiv.finrank_eq e).symm
    _ = c S := (c_eq_finrank_quotient S).symm

/-! ### `Vplus ≃ V0 / Im X0` via the quotient map -/

/-- The inclusion `S.Vplus ↪ S.V0` followed by the quotient by `Im S.X0` is a
linear equivalence onto `S.V0 / Im S.X0`. -/
noncomputable def VplusEquivQuotientRange (S : X0Setup F) :
    S.Vplus ≃ₗ[F] (S.V0 ⧸ LinearMap.range S.X0) :=
  (Submodule.quotientEquivOfIsCompl
    (LinearMap.range S.X0) S.Vplus S.isCompl.symm).symm

/-! ### Perfect pairing `Vplus × ker X0 → F`. -/

/-- The bilinear map `S.Vplus × ker S.X0 → F` obtained by restricting `S.formV0`. -/
noncomputable def vplusKerPairing (S : X0Setup F) :
    S.Vplus →ₗ[F] (LinearMap.ker S.X0) →ₗ[F] F :=
  S.formV0.domRestrict₁₂ S.Vplus (LinearMap.ker S.X0)

/-- The induced pairing `S.Vplus × ker S.X0 → F` is a perfect pairing, under
the hypotheses of `lem:x0-geometry`. -/
theorem vplusKerPairing_isPerfPair (S : X0Setup F)
    (hnondeg : S.formV0.Nondegenerate) :
    (vplusKerPairing S).IsPerfPair := by
  have href : S.formV0.IsRefl := by
    intro x y hxy
    have h := S.epsSymm y x
    simpa [hxy] using h
  have hortheq : S.formV0.orthogonal (LinearMap.range S.X0) = LinearMap.ker S.X0 :=
    orthogonal_range_eq_ker S hnondeg
  have horthorth :
      S.formV0.orthogonal (LinearMap.ker S.X0) = LinearMap.range S.X0 := by
    have hoo := LinearMap.BilinForm.orthogonal_orthogonal hnondeg href
      (LinearMap.range S.X0)
    rw [hortheq] at hoo
    exact hoo
  apply LinearMap.IsPerfPair.of_injective
  · -- Left injectivity of `vplusKerPairing`.
    rw [injective_iff_map_eq_zero]
    intro v hv
    -- Unpack: for every `x ∈ ker S.X0`, `S.formV0 v x = 0`.
    have h0 : ∀ x : LinearMap.ker S.X0,
        S.formV0 (v : S.V0) (x : S.V0) = 0 := by
      intro x
      have hcong := congrArg (fun f => f x) hv
      simpa [vplusKerPairing] using hcong
    -- By reflexivity, also `S.formV0 x v = 0`, so `v ∈ orth (ker X0)`.
    have hv_mem : (v : S.V0) ∈ S.formV0.orthogonal (LinearMap.ker S.X0) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have h1 : S.formV0 (v : S.V0) n = 0 := h0 ⟨n, hn⟩
      exact href _ _ h1
    rw [horthorth] at hv_mem
    -- `v ∈ Vplus ⊓ range X0 = ⊥`, so `v = 0`.
    have hbot : (S.Vplus ⊓ LinearMap.range S.X0 : Submodule F S.V0) = ⊥ :=
      S.isCompl.disjoint.eq_bot
    have hmem :
        (v : S.V0) ∈ (S.Vplus ⊓ LinearMap.range S.X0 : Submodule F S.V0) :=
      ⟨v.2, hv_mem⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  · -- Right injectivity of `vplusKerPairing` (via the flip).
    rw [injective_iff_map_eq_zero]
    intro x hx
    -- Unpack: for every `v ∈ Vplus`, `S.formV0 v x = 0`.
    have h0 : ∀ v : S.Vplus,
        S.formV0 (v : S.V0) (x : S.V0) = 0 := by
      intro v
      have hcong := congrArg (fun f => f v) hx
      simpa [vplusKerPairing, LinearMap.flip_apply] using hcong
    -- For every `y ∈ S.V0`, `S.formV0 y x = 0` (decompose `y` via `Vplus ⊕ range X0`).
    have hall : ∀ y : S.V0, S.formV0 y (x : S.V0) = 0 := by
      intro y
      have htop : S.Vplus ⊔ LinearMap.range S.X0 = ⊤ :=
        S.isCompl.codisjoint.eq_top
      have hy : y ∈ S.Vplus ⊔ LinearMap.range S.X0 := by
        rw [htop]; trivial
      rw [Submodule.mem_sup] at hy
      obtain ⟨v, hv, r, hr, rfl⟩ := hy
      have hxker : (x : S.V0) ∈ LinearMap.ker S.X0 := x.2
      have hxin : (x : S.V0) ∈ S.formV0.orthogonal (LinearMap.range S.X0) :=
        ker_le_orthogonal_range S hxker
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxin
      have hr_orth : S.formV0 r (x : S.V0) = 0 := hxin r hr
      have hv_orth : S.formV0 v (x : S.V0) = 0 := h0 ⟨v, hv⟩
      simp [LinearMap.add_apply, hv_orth, hr_orth]
    -- Right-separating gives `(x : V0) = 0`.
    have hx0 : (x : S.V0) = 0 := hnondeg.2 (x : S.V0) hall
    exact Subtype.ext hx0

/-! ### `T^∨ : ker X0 ≃ L1` for any iso `T : L1' ≃ Vplus` -/

/-- Setup for the final assertion of `lem:x0-geometry`.  We assume an auxiliary
finite-dimensional pair `(E, E')` with a perfect pairing `lambda` together with
Lagrangian-style decompositions `L1 ⊕ L0 = E` and `L1' ⊕ L0' = E'`.

The dual transpose `T^∨ : S.V0 →ₗ[F] E` of an isomorphism `T : L1' ≃ S.Vplus`
is characterised pointwise by `lambda (T^∨ v) a' = - S.formV0 v (T a')`; the
precise construction is part of the prover stage. -/
structure DualTransposeData
    (S : X0Setup F)
    {E E' : Type*} [AddCommGroup E] [Module F E]
    [AddCommGroup E'] [Module F E']
    (lambda : E →ₗ[F] E' →ₗ[F] F)
    (L1 : Submodule F E) (L1' : Submodule F E')
    (T : L1' →ₗ[F] S.Vplus) where
  /-- The dual transpose `T^∨ : S.V0 →ₗ[F] E`. -/
  Tdual : S.V0 →ₗ[F] E
  /-- Defining identity: `lambda (T^∨ v) a' = - S.formV0 v (T a')`. -/
  pairing_eq :
    ∀ (v : S.V0) (a' : L1'),
      lambda (Tdual v) (a' : E') = - S.formV0 v ((T a' : S.Vplus) : S.V0)
  /-- The dual transpose sends `ker X₀` into the chosen summand `L1`. -/
  Tdual_mem_L1 :
    ∀ w : LinearMap.ker S.X0, Tdual (w : S.V0) ∈ L1
  /-- The chosen summand `L1` has the expected dimension `c S`. -/
  finrank_L1_eq : Module.finrank F L1 = c S

/-- Under the hypotheses of `lem:x0-geometry`, the dual transpose `T^∨` of an
isomorphism `T : L1' ≃ₗ S.Vplus` restricts to an isomorphism
`ker S.X0 ≃ₗ L1`. -/
theorem sDual_restrict_ker_isIso (S : X0Setup F)
    (hnondeg : S.formV0.Nondegenerate)
    {E E' : Type*} [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    [AddCommGroup E'] [Module F E'] [FiniteDimensional F E']
    (lambda : E →ₗ[F] E' →ₗ[F] F) (_hlambda : lambda.IsPerfPair)
    (L1 : Submodule F E) (L1' : Submodule F E')
    (_hL1' : Module.finrank F L1' = c S)
    (T : L1' ≃ₗ[F] S.Vplus)
    (D : DualTransposeData S lambda L1 L1' (T : L1' →ₗ[F] S.Vplus)) :
    ∃ φ : (LinearMap.ker S.X0) ≃ₗ[F] L1,
      ∀ w : LinearMap.ker S.X0,
        ((φ w : E)) = D.Tdual ((w : S.V0)) := by
  classical
  have hperf : (vplusKerPairing S).IsPerfPair :=
    vplusKerPairing_isPerfPair S hnondeg
  have href : S.formV0.IsRefl := fun x y hxy => by
    have h := S.epsSymm y x
    simpa [hxy] using h
  -- Composite map `f := D.Tdual ∘ subtype : ker S.X0 →ₗ E`.
  set f : (LinearMap.ker S.X0) →ₗ[F] E :=
    D.Tdual ∘ₗ (LinearMap.ker S.X0).subtype with hfdef
  -- Step A: `f` is injective.
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hwval : D.Tdual ((w : S.V0)) = 0 := by
      simpa [hfdef] using hw
    -- Use `D.pairing_eq` and `T` surjective onto `Vplus`.
    have h_pair : ∀ v : S.Vplus, S.formV0 (w : S.V0) (v : S.V0) = 0 := by
      intro v
      have hp := D.pairing_eq (w : S.V0) (T.symm v)
      rw [hwval, map_zero, LinearMap.zero_apply] at hp
      simp at hp
      -- After `simp`, `hp : (S.formV0 ↑w) ↑v = 0`.
      exact hp
    have h_pair' : ∀ v : S.Vplus, S.formV0 (v : S.V0) (w : S.V0) = 0 := fun v =>
      href _ _ (h_pair v)
    -- Right injectivity of the perfect pair `vplusKerPairing` finishes.
    have hflip_inj : Function.Injective (vplusKerPairing S).flip :=
      hperf.bijective_right.1
    apply hflip_inj
    ext v
    simp only [LinearMap.flip_apply, vplusKerPairing,
      LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply, map_zero]
    exact h_pair' v
  -- Step B: `D.Tdual` maps `ker S.X0` into `L1`.
  have h_in_L1 : ∀ w : LinearMap.ker S.X0, D.Tdual (w : S.V0) ∈ L1 :=
    D.Tdual_mem_L1
  -- Step C: `dim L1 = c S`.
  have h_dim_L1 : Module.finrank F L1 = c S :=
    D.finrank_L1_eq
  -- Step D: cod-restrict `f` to land in `L1`.
  have hf_in_L1 : ∀ w : LinearMap.ker S.X0, f w ∈ L1 := by
    intro w
    simpa [hfdef] using h_in_L1 w
  let g : (LinearMap.ker S.X0) →ₗ[F] L1 := LinearMap.codRestrict L1 f hf_in_L1
  have hg_inj : Function.Injective g := by
    intro w₁ w₂ hw
    apply hf_inj
    have h := congrArg (Subtype.val) hw
    simpa [g] using h
  have hg_dim : Module.finrank F (LinearMap.ker S.X0) = Module.finrank F L1 := by
    rw [h_dim_L1]; rfl
  refine ⟨g.linearEquivOfInjective hg_inj hg_dim, ?_⟩
  intro w
  have hgw : (g w : E) = f w := by
    simp [g, LinearMap.codRestrict_apply]
  have happ : (g.linearEquivOfInjective hg_inj hg_dim) w = g w :=
    LinearMap.linearEquivOfInjective_apply hg_inj hg_dim w
  rw [happ]
  rw [hgw]
  simp [hfdef]

/-! ### Aggregate statement of `lem:x0-geometry` -/

/-- Bundled conclusion of `lem:x0-geometry`: the orthogonal/kernel coincidence,
the dimension equality, and the perfect pairing.  The dual-transpose part is
stated separately as `sDual_restrict_ker_isIso`. -/
theorem x0Geometry (S : X0Setup F)
    (hnondeg : S.formV0.Nondegenerate) :
    S.formV0.orthogonal (LinearMap.range S.X0) = LinearMap.ker S.X0
      ∧ Module.finrank F (S.V0 ⧸ LinearMap.range S.X0)
          = Module.finrank F (LinearMap.ker S.X0)
      ∧ Module.finrank F S.Vplus = c S
      ∧ (vplusKerPairing S).IsPerfPair := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact orthogonal_range_eq_ker S hnondeg
  · exact finrank_quotient_range_eq_finrank_ker S
  · exact finrank_Vplus_eq_c S
  · exact vplusKerPairing_isPerfPair S hnondeg

end InducedOrbitToy
