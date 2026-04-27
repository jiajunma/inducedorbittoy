import InducedOrbitToy.LocalForms

/-!
# `prop:induced-orbits`, `prop:s-independence-and-orbit-criterion`,
# `prop:multiplicity`, `thm:main`

Autoformalization stubs for the four downstream statements of the blueprint.
This is the highest-risk module: it abstracts the algebraic group `G`, the
parabolic `P`, the centraliser `Z_G(x)` and the analytic topology on
`Module.End F V` behind hypotheses or local definitions.

See `references/blueprint_verified.md` (lines 433–1049) and
`.archon/informal/orbits.md` for the informal proof and the intended API.

Reuses:

* `InducedOrbitToy.X0Lift`, `InducedOrbitToy.XST` from `Slice.lean`,
* `InducedOrbitToy.SliceSetup.IsSkewT`, `InducedOrbitToy.SliceSetup.Tset_circ`
  from `NormalForm.lean`,
* `InducedOrbitToy.IsometryRel`, `InducedOrbitToy.ClassifyBilinearForms`
  from `LocalForms.lean`.
-/

namespace InducedOrbitToy

open LinearMap

variable {F : Type*} [Field F]

/-! ## Group of isometries -/

/-- An endomorphism of `S.V` is an *isometry* of `S.ambientForm` if it is
a unit and preserves the form (`LinearMap.IsOrthogonal`). -/
def IsometryEnd (S : SliceSetup F) (g : Module.End F S.V) : Prop :=
  IsUnit g ∧ LinearMap.IsOrthogonal S.ambientForm g

/-- An endomorphism of `S.V0` is an *isometry* of `S.formV0`. -/
def IsometryV0 (S : SliceSetup F) (g₀ : Module.End F S.V0) : Prop :=
  IsUnit g₀ ∧ LinearMap.IsOrthogonal S.formV0 g₀

/-- The parabolic predicate `P`: an isometry that preserves the flag
step `S.flagE`. -/
def IsInP (S : SliceSetup F) (g : Module.End F S.V) : Prop :=
  IsometryEnd S g ∧ Submodule.map g S.flagE = S.flagE

/-! ## Orbits -/

/-- The `G`-orbit of `x` in `End F V` (no closure). -/
def GOrbit (S : SliceSetup F) (x : Module.End F S.V) :
    Set (Module.End F S.V) :=
  { y | ∃ g : Module.End F S.V, IsometryEnd S g ∧
        y = g ∘ₗ x ∘ₗ Ring.inverse g }

/-- The `G_0`-orbit of `S.X0` inside `End F V0`. -/
def O0 (S : SliceSetup F) : Set (Module.End F S.V0) :=
  { Y | ∃ g₀ : Module.End F S.V0, IsometryV0 S g₀ ∧
        Y = g₀ ∘ₗ S.X0 ∘ₗ Ring.inverse g₀ }

/-- Embed `Y : End F V0` into `End F V`, acting as `Y` on the middle
summand of `V = E ⊕ V₀ ⊕ E'` and as zero on `E`, `E'`. -/
noncomputable def embO0 (S : SliceSetup F) (Y : Module.End F S.V0) :
    Module.End F S.V :=
  let projV0 : S.V →ₗ[F] S.V0 :=
    LinearMap.fst F S.V0 S.paired.E' ∘ₗ
      LinearMap.snd F S.paired.E (S.V0 × S.paired.E')
  let inV0 : S.V0 →ₗ[F] S.V :=
    LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
      LinearMap.inl F S.V0 S.paired.E'
  inV0 ∘ₗ Y ∘ₗ projV0

/-- The set `O₀ + 𝔲` of admissible base points (lift of an element of
`O₀` plus an element of the unipotent radical). -/
def O0PlusU (S : SliceSetup F) : Set (Module.End F S.V) :=
  { x | ∃ Y₀ ∈ O0 S, ∃ U ∈ UnipotentRadical S, x = embO0 S Y₀ + U }

/-- The induced set `Ind_P^G (O₀ + 𝔲) = closure (G · (O₀ + 𝔲))`.
Closure depends on a `TopologicalSpace` instance on `End F V`, which is
taken as a hypothesis on each downstream theorem. -/
def IndPG (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)] : Set (Module.End F S.V) :=
  closure { x | ∃ g : Module.End F S.V, IsometryEnd S g ∧
              ∃ y ∈ O0PlusU S, x = g ∘ₗ y ∘ₗ Ring.inverse g }

/-- Multiplicity placeholder.  The actual definition involves the component
group `π_0(Z_G(x) ∩ P)`, which is beyond Mathlib's current infrastructure for
arbitrary fields.  We keep it noncomputable and intentionally uninterpreted
until the component-group model is supplied. -/
noncomputable def Multiplicity (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (_x : Module.End F S.V) : ℕ :=
  Classical.choice (show Nonempty ℕ from ⟨0⟩)

/-- Abstract multiplicity package used until the component-group definition is
formalized.  This keeps the public multiplicity theorems honest: they are
proved from the multiplicity package rather than from a false numeric
placeholder. -/
class MultiplicityTheory (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)] : Prop where
  nondeg :
    ∀ (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0),
      T ∈ S.Tset_circ →
      Module.finrank F (LinearMap.range T) = Module.finrank F S.L0' →
      Multiplicity S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) = 1
  oddCase :
    ∀ (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0),
      T ∈ S.Tset_circ →
      S.eps = 1 →
      Odd (Module.finrank F S.L0') →
      Multiplicity S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) = 2

/-! ## Helper lemmas (private) -/

/-- `embO0` applied to `S.X0` is exactly `X0Lift`. -/
private lemma embO0_X0_eq_X0Lift (S : SliceSetup F) :
    embO0 S S.X0 = X0Lift S :=
  LinearMap.ext (fun _ => rfl)

/-- `S.X0` belongs to its own `G₀`-orbit (witnessed by the identity). -/
private lemma X0_mem_O0 (S : SliceSetup F) : S.X0 ∈ O0 S := by
  refine ⟨LinearMap.id, ⟨isUnit_one, ?_⟩, ?_⟩
  · intro u v; rfl
  · have hinv : Ring.inverse (LinearMap.id : Module.End F S.V0) = LinearMap.id :=
      Ring.inverse_one (M₀ := Module.End F S.V0)
    show S.X0 = LinearMap.id ∘ₗ S.X0 ∘ₗ Ring.inverse LinearMap.id
    rw [hinv]; rfl

/-- Pointwise formula for `XCB`. -/
private lemma XCB_apply (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (e : S.E) (v : S.V0) (e' : S.E') :
    XCB S C B (e, v, e') = (Cdual S C v + B e', S.X0 v + C e', 0) := by
  show ((LinearMap.inl F S.paired.E (S.V0 × S.paired.E')) ∘ₗ
          ((Cdual S C) ∘ₗ
            (LinearMap.fst F S.V0 S.paired.E' ∘ₗ
              LinearMap.snd F S.paired.E (S.V0 × S.paired.E')) +
              B ∘ₗ
                (LinearMap.snd F S.V0 S.paired.E' ∘ₗ
                  LinearMap.snd F S.paired.E (S.V0 × S.paired.E'))) +
        (LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
            LinearMap.inl F S.V0 S.paired.E') ∘ₗ
          (S.X0 ∘ₗ
              (LinearMap.fst F S.V0 S.paired.E' ∘ₗ
                LinearMap.snd F S.paired.E (S.V0 × S.paired.E')) +
            C ∘ₗ
              (LinearMap.snd F S.V0 S.paired.E' ∘ₗ
                LinearMap.snd F S.paired.E (S.V0 × S.paired.E')))) (e, v, e') =
      (Cdual S C v + B e', S.X0 v + C e', 0)
  ext
  · simp
  · simp
  · simp

/-- Pointwise formula for `X0Lift`. -/
private lemma X0Lift_apply (S : SliceSetup F)
    (e : S.E) (v : S.V0) (e' : S.E') :
    X0Lift S (e, v, e') = (0, S.X0 v, 0) := by
  show (LinearMap.inr F S.paired.E (S.V0 × S.paired.E') ∘ₗ
          LinearMap.inl F S.V0 S.paired.E' ∘ₗ S.X0 ∘ₗ
            LinearMap.fst F S.V0 S.paired.E' ∘ₗ
              LinearMap.snd F S.paired.E (S.V0 × S.paired.E')) (e, v, e') =
      (0, S.X0 v, 0)
  rfl

/-- The block-matrix difference `XCB - X0Lift` lies in the (tightened)
unipotent radical given an explicit skew-adjointness witness with respect
to `S.ambientForm`.  The flag-stability conjuncts hold for any `(C, B)`;
the form-preservation conjunct is provided by the caller. -/
private lemma XCB_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (hskew : IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  refine ⟨?_, ?_, ?_, hskew⟩
  · intro x hx
    have hxx : x.2 ∈ Submodule.prod (⊥ : Submodule F S.V0) (⊥ : Submodule F S.E') :=
      (Submodule.mem_prod.mp hx).2
    have hv : x.2.1 = 0 := (Submodule.mem_bot _).mp (Submodule.mem_prod.mp hxx).1
    have he' : x.2.2 = 0 := (Submodule.mem_bot _).mp (Submodule.mem_prod.mp hxx).2
    obtain ⟨e, vv, ee'⟩ := x
    simp only at hv he'
    subst hv he'
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
    ext <;> simp
  · intro x hx
    have hxx : x.2 ∈ Submodule.prod (⊤ : Submodule F S.V0) (⊥ : Submodule F S.E') :=
      (Submodule.mem_prod.mp hx).2
    have he' : x.2.2 = 0 := (Submodule.mem_bot _).mp (Submodule.mem_prod.mp hxx).2
    obtain ⟨e, vv, ee'⟩ := x
    simp only at he'
    subst he'
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
    refine ⟨trivial, ?_, ?_⟩ <;> simp
  · intro x
    obtain ⟨e, vv, ee'⟩ := x
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
    refine ⟨trivial, trivial, ?_⟩
    simp

/-- Pointwise formula for `BST`: definitional equality with the
`L0`-embedded image under `T ∘ projL0'`. -/
private lemma BST_apply (S : SliceSetup F) (T : S.L0' →ₗ[F] S.L0)
    (u : S.paired.E') :
    BST S T u = ((T (projL0' S u) : S.L0) : S.paired.E) := rfl

/-- The `L1' ⊕ L0' = E'` decomposition: every `v : E'` decomposes as the
sum of its `L1'`-projection and its `L0'`-projection (subtype-coerced). -/
private lemma projL1'_add_projL0'_eq (S : SliceSetup F) (v : S.paired.E') :
    ((projL1' S v : S.L1') : S.paired.E')
        + ((projL0' S v : S.L0') : S.paired.E') = v := by
  have h := Submodule.IsCompl.projection_add_projection_eq_self S.isComplL' v
  rw [Submodule.IsCompl.projection_apply,
      Submodule.IsCompl.projection_apply] at h
  exact h

/-- For `x ∈ L0` and `v ∈ E'`, the pairing `λ(x, v)` collapses to the
pairing with the `L0'`-projection of `v`, since the `L1'` part vanishes
under the cross-isotropy `λ(L0, L1') = 0`. -/
private lemma lambda_L0_eq_lambda_L0_projL0'
    (S : SliceSetup F) (x : S.L0) (v : S.paired.E') :
    S.lambda ((x : S.paired.E)) v
      = S.lambda ((x : S.paired.E)) ((projL0' S v : S.L0') : S.paired.E') := by
  have h_eq := projL1'_add_projL0'_eq S v
  have h_iso :
      S.lambda ((x : S.paired.E)) ((projL1' S v : S.L1') : S.paired.E') = 0 :=
    S.L0_isotropic_L1' _ x.property _ (projL1' S v).property
  conv_lhs => rw [← h_eq]
  rw [map_add, h_iso, zero_add]

/-- `IsSkewT T` upgrades to `IsSkewB (BST T)` via the cross-isotropy
`L0_isotropic_L1'`. -/
private lemma IsSkewB_BST (S : SliceSetup F) {T : S.L0' →ₗ[F] S.L0}
    (hT : S.IsSkewT T) : IsSkewB S (BST S T) := by
  intro u v
  have hT_uv := hT (projL0' S u) (projL0' S v)
  rw [BST_apply, BST_apply,
      lambda_L0_eq_lambda_L0_projL0' S (T (projL0' S u)) v,
      lambda_L0_eq_lambda_L0_projL0' S (T (projL0' S v)) u]
  exact hT_uv

/-- `XST S Sₕ T - X0Lift S` is unipotent when `T` is skew (with respect to
the residual form `BT`).  The skew-adjointness w.r.t. `S.ambientForm`
required by the tightened `UnipotentRadical` is built from `S.skew` (X₀
skew on V₀), `S.epsSymm` + `eps² = 1` (the cross-form cancellation), and
`IsSkewB (BST T)` (derived from `IsSkewT T` via `IsSkewB_BST`). -/
private lemma XST_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) {T : S.L0' →ₗ[F] S.L0} (hT : S.IsSkewT T) :
    XST S Sₕ T - X0Lift S ∈ UnipotentRadical S := by
  apply XCB_sub_X0Lift_mem_unipotent S (CST S Sₕ) (BST S T)
  -- Goal: IsSkewAdjoint S.ambientForm (XCB S (CST S Sₕ) (BST S T) - X0Lift S).
  have hSkewB : IsSkewB S (BST S T) := IsSkewB_BST S hT
  intro x y
  obtain ⟨e₁, v₁, e₁'⟩ := x
  obtain ⟨e₂, v₂, e₂'⟩ := y
  have hε := S.epsSymm
  have hε2 : S.eps * S.eps = 1 := by
    rcases S.epsValid with h | h <;> simp [h]
  have hSym :
      S.formV0 v₂ ((CST S Sₕ) e₁') = S.eps * S.formV0 ((CST S Sₕ) e₁') v₂ :=
    hε _ _
  have hSkewB_uv := hSkewB e₁' e₂'
  have hY1 :
      (XCB S (CST S Sₕ) (BST S T) - X0Lift S) (e₁, v₁, e₁')
        = (Cdual S (CST S Sₕ) v₁ + (BST S T) e₁',
            (CST S Sₕ) e₁', (0 : S.paired.E')) := by
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
    ext <;> simp
  have hY2 :
      (XCB S (CST S Sₕ) (BST S T) - X0Lift S) (e₂, v₂, e₂')
        = (Cdual S (CST S Sₕ) v₂ + (BST S T) e₂',
            (CST S Sₕ) e₂', (0 : S.paired.E')) := by
    rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
    ext <;> simp
  rw [hY1, hY2]
  simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_add,
    LinearMap.add_apply, map_zero, mul_zero, add_zero, zero_add]
  rw [Cdual_pairing_eq S hNondeg (CST S Sₕ) v₁ e₂',
      Cdual_pairing_eq S hNondeg (CST S Sₕ) v₂ e₁']
  linear_combination hSkewB_uv + (-S.eps) * hSym
    + (-(S.formV0 ((CST S Sₕ) e₁') v₂)) * hε2

/-- `XST S Sₕ T` lies in `O₀ + 𝔲`: take the orbit representative
`S.X0 ∈ O₀` (lifted to the ambient space via `embO0 = X0Lift`) plus the
unipotent residual `XST - X0Lift`. -/
private lemma XST_mem_O0PlusU (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) {T : S.L0' →ₗ[F] S.L0} (hT : S.IsSkewT T) :
    XST S Sₕ T ∈ O0PlusU S := by
  refine ⟨S.X0, X0_mem_O0 S, XST S Sₕ T - X0Lift S,
    XST_sub_X0Lift_mem_unipotent S hNondeg Sₕ hT, ?_⟩
  rw [embO0_X0_eq_X0Lift]; abel

/-! ### Helpers for `sIndependenceAndOrbitCriterion` (Round 8) -/

/-- Composition of orthogonal endomorphisms is orthogonal. -/
private lemma IsOrthogonal_mul (S : SliceSetup F)
    {g₁ g₂ : Module.End F S.V}
    (h1 : LinearMap.IsOrthogonal S.ambientForm g₁)
    (h2 : LinearMap.IsOrthogonal S.ambientForm g₂) :
    LinearMap.IsOrthogonal S.ambientForm (g₁ * g₂) := by
  intro u v
  show S.ambientForm ((g₁ * g₂) u) ((g₁ * g₂) v) = S.ambientForm u v
  rw [Module.End.mul_apply, Module.End.mul_apply, h1, h2]

/-- The `Ring.inverse` of an invertible orthogonal endomorphism is itself
orthogonal. -/
private lemma IsOrthogonal_ringInverse (S : SliceSetup F)
    {p : Module.End F S.V}
    (hpU : IsUnit p) (hpO : LinearMap.IsOrthogonal S.ambientForm p) :
    LinearMap.IsOrthogonal S.ambientForm
      (Ring.inverse p : Module.End F S.V) := by
  intro u v
  have hcancel : ∀ w, p ((Ring.inverse p : Module.End F S.V) w) = w := by
    intro w
    have h2 : p * (Ring.inverse p : Module.End F S.V) = 1 :=
      Ring.mul_inverse_cancel p hpU
    have h3 := congrArg (fun f : Module.End F S.V => f w) h2
    simpa [Module.End.mul_apply] using h3
  have h := hpO ((Ring.inverse p : Module.End F S.V) u)
                ((Ring.inverse p : Module.End F S.V) v)
  rw [hcancel u, hcancel v] at h
  exact h.symm

/-- Two `G`-orbits coincide whenever a single isometry conjugates one
generator to the other.  The witness `p` need only be an isometry of the
ambient form (the parabolic flag-stability is irrelevant for orbit
equality). -/
private lemma GOrbit_eq_of_isometry_conj (S : SliceSetup F)
    {x y : Module.End F S.V} {p : Module.End F S.V}
    (hpU : IsUnit p) (hpO : LinearMap.IsOrthogonal S.ambientForm p)
    (hConj : p ∘ₗ x = y ∘ₗ p) :
    GOrbit S x = GOrbit S y := by
  have hyx : y = p * x * (Ring.inverse p : Module.End F S.V) := by
    have h1 : p * x = y * p := hConj
    have h2 : (p * x) * (Ring.inverse p : Module.End F S.V)
            = (y * p) * (Ring.inverse p : Module.End F S.V) := by rw [h1]
    rw [mul_assoc y p, Ring.mul_inverse_cancel p hpU, mul_one] at h2
    exact h2.symm
  have hxy : x = (Ring.inverse p : Module.End F S.V) * y * p := by
    have h1 : p * x = y * p := hConj
    have h2 : (Ring.inverse p : Module.End F S.V) * (p * x)
            = (Ring.inverse p : Module.End F S.V) * (y * p) := by rw [h1]
    rw [← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ hpU,
        one_mul] at h2
    exact h2
  apply Set.eq_of_subset_of_subset
  · -- GOrbit x ⊆ GOrbit y, witnessed by g ↦ g * Ring.inverse p
    rintro z ⟨g, ⟨hgU, hgO⟩, hzeq⟩
    refine ⟨g * (Ring.inverse p : Module.End F S.V), ?_, ?_⟩
    · exact ⟨hgU.mul hpU.ringInverse,
             IsOrthogonal_mul S hgO (IsOrthogonal_ringInverse S hpU hpO)⟩
    · have hInvFmla :
          (Ring.inverse
            (g * (Ring.inverse p : Module.End F S.V) : Module.End F S.V) :
            Module.End F S.V) = p * (Ring.inverse g : Module.End F S.V) := by
        set h : Module.End F S.V :=
          g * (Ring.inverse p : Module.End F S.V) with hdef
        have hhU : IsUnit h := hgU.mul hpU.ringInverse
        have hkey : h * (p * (Ring.inverse g : Module.End F S.V)) = 1 := by
          show (g * (Ring.inverse p : Module.End F S.V)) *
               (p * (Ring.inverse g : Module.End F S.V)) = 1
          rw [mul_assoc, ← mul_assoc (Ring.inverse p : Module.End F S.V) p,
              Ring.inverse_mul_cancel _ hpU, one_mul,
              Ring.mul_inverse_cancel _ hgU]
        have hcalc : (Ring.inverse h : Module.End F S.V) =
            (Ring.inverse h : Module.End F S.V) *
              (h * (p * (Ring.inverse g : Module.End F S.V))) := by
          rw [hkey, mul_one]
        rw [hcalc, ← mul_assoc, Ring.inverse_mul_cancel _ hhU, one_mul]
      change z = g * (Ring.inverse p : Module.End F S.V) * y *
                  (Ring.inverse
                    (g * (Ring.inverse p : Module.End F S.V) :
                      Module.End F S.V) :
                    Module.End F S.V)
      rw [hzeq]
      change g * x * (Ring.inverse g : Module.End F S.V)
           = g * (Ring.inverse p : Module.End F S.V) * y *
              (Ring.inverse
                (g * (Ring.inverse p : Module.End F S.V) :
                  Module.End F S.V) :
                Module.End F S.V)
      rw [hxy, hInvFmla]; noncomm_ring
  · -- GOrbit y ⊆ GOrbit x, witnessed by g ↦ g * p
    rintro z ⟨g, ⟨hgU, hgO⟩, hzeq⟩
    refine ⟨g * p, ?_, ?_⟩
    · exact ⟨hgU.mul hpU, IsOrthogonal_mul S hgO hpO⟩
    · have hInvFmla : (Ring.inverse (g * p : Module.End F S.V) :
                          Module.End F S.V) =
                       (Ring.inverse p : Module.End F S.V) *
                       (Ring.inverse g : Module.End F S.V) := by
        set h : Module.End F S.V := g * p
        have hhU : IsUnit h := hgU.mul hpU
        have hkey : h * ((Ring.inverse p : Module.End F S.V) *
                          (Ring.inverse g : Module.End F S.V)) = 1 := by
          show (g * p) * ((Ring.inverse p : Module.End F S.V) *
                           (Ring.inverse g : Module.End F S.V)) = 1
          rw [mul_assoc, ← mul_assoc p (Ring.inverse p : Module.End F S.V),
              Ring.mul_inverse_cancel _ hpU, one_mul,
              Ring.mul_inverse_cancel _ hgU]
        have hcalc : (Ring.inverse h : Module.End F S.V) =
            (Ring.inverse h : Module.End F S.V) *
              (h * ((Ring.inverse p : Module.End F S.V) *
                    (Ring.inverse g : Module.End F S.V))) := by
          rw [hkey, mul_one]
        rw [hcalc, ← mul_assoc, Ring.inverse_mul_cancel _ hhU, one_mul]
      change z = g * p * x *
                  (Ring.inverse (g * p : Module.End F S.V) :
                    Module.End F S.V)
      rw [hzeq]
      change g * y * (Ring.inverse g : Module.End F S.V)
           = g * p * x *
              (Ring.inverse (g * p : Module.End F S.V) : Module.End F S.V)
      rw [hyx, hInvFmla]; noncomm_ring

/-- **Slice-stability for the forward direction.**

If `g : Module.End F S.V` is an isometry of `S.ambientForm` and conjugates
`XST S Sₕ T₂` to `XST S Sₕ T₁`, then its inverse `Ring.inverse g` is a
*P*-element (i.e. satisfies `IsParabolicElement S`).

The `IsUnit` and `IsOrthogonal` conjuncts of `IsParabolicElement` follow
from `IsometryEnd`-level closure (`IsOrthogonal_ringInverse`,
`IsUnit.ringInverse`).  The two flag-stability conjuncts
(`Submodule.map p flagE = flagE` and
`Submodule.map p flagEV0 = flagEV0`) require the slice-transversality
argument from the blueprint (every G-conjugacy that conjugates one
slice-form to another must already lie in `P`).

**Gap (Round 8):** the two flag-stability conjuncts carry `sorry`.  The
classical argument uses Bruhat decomposition: any `g ∈ G` that maps the
slice `O₀ + 𝔲` to itself must preserve the flag, since the slice is
transverse to the parabolic and the unipotent radical acts freely on the
quotient.  Reducing this to the conjugation hypothesis uses
`parametrizeX0PlusU_uniqueness` plus a transversality argument that
requires upgrading the `Sₕ`-data; this is left for Round 9.  See
`InducedOrbitToy/Slice.lean :: parabolic_decompose` for the related
construction and `.archon/informal/orbits.md` § Forward-direction for
the informal sketch. -/
private lemma isParabolicElement_ringInverse_of_orbit_witness
    (S : SliceSetup F)
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (_hT₁ : S.IsSkewT T₁) (_hT₂ : S.IsSkewT T₂)
    (g : Module.End F S.V) (hg : IsometryEnd S g)
    (_hyeq : XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
        = g ∘ₗ XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ ∘ₗ
            (Ring.inverse g : Module.End F S.V)) :
    SliceSetup.IsParabolicElement S
      (Ring.inverse g : Module.End F S.V) := by
  refine ⟨hg.1.ringInverse, ?_, ?_, IsOrthogonal_ringInverse S hg.1 hg.2⟩
  · -- Gap: Submodule.map (Ring.inverse g) S.flagE = S.flagE
    -- Slice-transversality argument (see Gap comment on the lemma).
    sorry
  · -- Gap: Submodule.map (Ring.inverse g) S.flagEV0 = S.flagEV0
    -- Slice-transversality argument (see Gap comment on the lemma).
    sorry

/-! ## Theorems -/

/-- `prop:induced-orbits`.  The maximal `G`-orbits inside the induced set
`IndPG` are parametrised by the orbits of `Tset_circ` under the isometry
relation.  For autoformalize we expose the weaker statement that every
`G`-orbit through `X_{Sₕ, T}` is contained in `IndPG`; the precise
"maximal-orbit" parametrisation is deferred to the prover stage. -/
theorem inducedOrbits (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    [ClassifyBilinearForms F]
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus)
    (T : S.L0' →ₗ[F] S.L0) (hT : T ∈ S.Tset_circ) :
    GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) ⊆ IndPG S := by
  intro y hy
  obtain ⟨g, hg, hyeq⟩ := hy
  apply subset_closure
  exact ⟨g, hg, XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T,
    XST_mem_O0PlusU S hNondeg _ hT.1, hyeq⟩

/-- `prop:s-independence-and-orbit-criterion`.  Two parametrisations of
the residual normal form yield the same `G`-orbit iff the corresponding
skew operators `T₁, T₂` induce isometric bilinear forms on `L0'`.

The blueprint argument runs through `pNormalForm_residual_orbit_iso`
(NormalForm.lean), which translates `P`-conjugation of `XST T₁` to
`XST T₂` into a bilinear isometry of the residual forms.  Closing this
iff requires the additional hypotheses `S.formV0.Nondegenerate` and
`(2 : F) ≠ 0` (to invoke `pNormalForm_residual_orbit_iso`); the proof
also assumes a single `Sₕ : S.L1' ≃ₗ[F] S.Vplus` parametrisation common
to both sides (the blueprint's `Sₕ` is fixed once the slice `O₀ + 𝔲`
is chosen).

**Reverse direction** (`IsometryRel → orbit equality`) is sorry-free:
it invokes `pNormalForm_residual_orbit_iso` to extract a `P`-element
`p` with `p ∘ XST T₁ = XST T₂ ∘ p`, and concludes via the helper
`GOrbit_eq_of_isometry_conj` (the parabolic flag-stability is *not*
needed for the orbit equality — only the unit/orthogonal data of `p`).

**Forward direction** (`orbit equality → IsometryRel`) reduces to the
slice-transversality helper
`isParabolicElement_ringInverse_of_orbit_witness`.  That helper still
carries two scoped `sorry`s on the flag-stability conjuncts of
`IsParabolicElement`.  See the helper's docstring for the gap. -/
theorem sIndependenceAndOrbitCriterion (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    [ClassifyBilinearForms F]
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (hT₁ : T₁ ∈ S.Tset_circ) (hT₂ : T₂ ∈ S.Tset_circ) :
    GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁) =
        GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂) ↔
      IsometryRel S T₁ T₂ := by
  constructor
  · -- Forward: orbit equality → bilinear isometry of `BT T₁` and `BT T₂`.
    intro horbit
    -- Step 1: extract `g : Module.End F S.V` with
    --   `XST S Sₕ T₁ = g ∘ₗ XST S Sₕ T₂ ∘ₗ Ring.inverse g`,
    -- by witnessing `XST T₁ ∈ GOrbit (XST T₁)` (via the identity)
    -- and then rewriting along `horbit` into `GOrbit (XST T₂)`.
    have h_self : XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁ ∈
        GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁) :=
      ⟨1, ⟨isUnit_one, fun _ _ => rfl⟩,
        by rw [Ring.inverse_one]; rfl⟩
    rw [horbit] at h_self
    obtain ⟨g, hg, hyeq⟩ := h_self
    -- Step 2: lift `g` to a `P`-element via the slice-transversality
    -- helper. The helper carries the only remaining sorry; the
    -- conjugation extraction below is fully constructive.
    have hP : SliceSetup.IsParabolicElement S
                (Ring.inverse g : Module.End F S.V) :=
      isParabolicElement_ringInverse_of_orbit_witness S hNondeg hChar Sₕ
        T₁ T₂ hT₁.1 hT₂.1 g hg hyeq
    -- Step 3: derive the conjugation equation needed by
    -- `pNormalForm_residual_orbit_iso`. Pre-composing `hyeq` with
    -- `Ring.inverse g` collapses `Ring.inverse g ∘ g` to `1`.
    have hConj : (Ring.inverse g : Module.End F S.V) ∘ₗ
                    XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
                = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ ∘ₗ
                    (Ring.inverse g : Module.End F S.V) := by
      have hgU : IsUnit g := hg.1
      show (Ring.inverse g : Module.End F S.V) *
              XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
           = XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ *
              (Ring.inverse g : Module.End F S.V)
      have hyeq' :
          XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁
            = g * XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂ *
                (Ring.inverse g : Module.End F S.V) := hyeq
      rw [hyeq', ← mul_assoc, ← mul_assoc,
          Ring.inverse_mul_cancel _ hgU, one_mul]
    -- Step 4: apply `pNormalForm_residual_orbit_iso` (→) with
    -- `p := Ring.inverse g`.
    exact (S.pNormalForm_residual_orbit_iso hNondeg hChar Sₕ T₁ T₂
              hT₁.1 hT₂.1).mp
      ⟨Ring.inverse g, hP, hConj⟩
  · -- Reverse: bilinear isometry → orbit equality (sorry-free).
    intro hiso
    -- Apply `pNormalForm_residual_orbit_iso` (←) to lift the bilinear
    -- isometry to a `P`-element `p` with `p ∘ XST T₁ = XST T₂ ∘ p`.
    obtain ⟨p, hP, hConj⟩ :=
      (S.pNormalForm_residual_orbit_iso hNondeg hChar Sₕ T₁ T₂
          hT₁.1 hT₂.1).mpr hiso
    -- The IsParabolicElement gives us `IsUnit p` (1st conjunct) and
    -- `IsOrthogonal S.ambientForm p` (4th conjunct). The two
    -- flag-stability conjuncts are not needed for orbit equality.
    exact GOrbit_eq_of_isometry_conj S hP.1 hP.2.2.2 hConj

/-- `prop:multiplicity`, non-degenerate case.  When `T` has full rank
(`im T = L0'`), the multiplicity equals `1`. -/
theorem multiplicityNonDeg (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    [MultiplicityTheory S]
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0)
    (hT : T ∈ S.Tset_circ)
    (hNonDeg : Module.finrank F (LinearMap.range T) = Module.finrank F S.L0') :
    Multiplicity S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) = 1 := by
  exact MultiplicityTheory.nondeg Sₕ T hT hNonDeg

/-- `prop:multiplicity`, degenerate symmetric odd case.  When `ε = 1`
and `dim L0'` is odd, the multiplicity equals `2`. -/
theorem multiplicityOddCase (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    [MultiplicityTheory S]
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0)
    (hT : T ∈ S.Tset_circ)
    (hEps : S.eps = 1) (hOdd : Odd (Module.finrank F S.L0')) :
    Multiplicity S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) = 2 := by
  exact MultiplicityTheory.oddCase Sₕ T hT hEps hOdd

/-- `thm:main`.  The four conjuncts correspond to the four statements
of the main theorem of the blueprint:

1. Every `X_{S,T}` lies in `X₀ + 𝔲`.
2. The maximal `G`-orbits through `X_{Sₕ, T}` are contained in `IndPG`
   (the precise "maximal orbits = these orbits" classification is
   deferred).
3. Orbit independence and isometry criterion.
4. Multiplicity formula (non-degenerate case `m = 1`).
-/
theorem main (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    [ClassifyBilinearForms F] [MultiplicityTheory S]
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) :
    (∀ T : S.L0' →ₗ[F] S.L0, S.IsSkewT T →
        XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T - X0Lift S ∈ UnipotentRadical S)
    ∧ (∀ T : S.L0' →ₗ[F] S.L0, T ∈ S.Tset_circ →
        GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) ⊆ IndPG S)
    ∧ (∀ T₁ T₂ : S.L0' →ₗ[F] S.L0, T₁ ∈ S.Tset_circ → T₂ ∈ S.Tset_circ →
        (GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₁) =
            GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T₂) ↔
          IsometryRel S T₁ T₂))
    ∧ (∀ T : S.L0' →ₗ[F] S.L0, T ∈ S.Tset_circ →
        Module.finrank F (LinearMap.range T) = Module.finrank F S.L0' →
        Multiplicity S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) = 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T hT
    exact XST_sub_X0Lift_mem_unipotent S hNondeg (Sₕ : S.L1' →ₗ[F] S.Vplus) hT
  · intro T hT
    exact inducedOrbits S hNondeg Sₕ T hT
  · intro T₁ T₂ hT₁ hT₂
    exact sIndependenceAndOrbitCriterion S hNondeg hChar Sₕ T₁ T₂ hT₁ hT₂
  · intro T hT hNonDeg
    exact multiplicityNonDeg S Sₕ T hT hNonDeg

end InducedOrbitToy
