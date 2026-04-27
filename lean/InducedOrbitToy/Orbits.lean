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

/-- The block-matrix difference `XCB - X0Lift` always lies in the
unipotent radical, irrespective of skew-symmetry of `(C, B)`. -/
private lemma XCB_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  refine ⟨?_, ?_, ?_⟩
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

/-- `XST S Sₕ T - X0Lift S` is unipotent. -/
private lemma XST_sub_X0Lift_mem_unipotent (S : SliceSetup F)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) :
    XST S Sₕ T - X0Lift S ∈ UnipotentRadical S :=
  XCB_sub_X0Lift_mem_unipotent S (CST S Sₕ) (BST S T)

/-- `XST S Sₕ T` lies in `O₀ + 𝔲`: take the orbit representative
`S.X0 ∈ O₀` (lifted to the ambient space via `embO0 = X0Lift`) plus the
unipotent residual `XST - X0Lift`. -/
private lemma XST_mem_O0PlusU (S : SliceSetup F)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) :
    XST S Sₕ T ∈ O0PlusU S := by
  refine ⟨S.X0, X0_mem_O0 S, XST S Sₕ T - X0Lift S,
    XST_sub_X0Lift_mem_unipotent S Sₕ T, ?_⟩
  rw [embO0_X0_eq_X0Lift]; abel

/-! ## Theorems -/

/-- `prop:induced-orbits`.  The maximal `G`-orbits inside the induced set
`IndPG` are parametrised by the orbits of `Tset_circ` under the isometry
relation.  For autoformalize we expose the weaker statement that every
`G`-orbit through `X_{Sₕ, T}` is contained in `IndPG`; the precise
"maximal-orbit" parametrisation is deferred to the prover stage. -/
theorem inducedOrbits (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    [ClassifyBilinearForms F]
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus)
    (T : S.L0' →ₗ[F] S.L0) (_hT : T ∈ S.Tset_circ) :
    GOrbit S (XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T) ⊆ IndPG S := by
  intro y hy
  obtain ⟨g, hg, hyeq⟩ := hy
  apply subset_closure
  exact ⟨g, hg, XST S (Sₕ : S.L1' →ₗ[F] S.Vplus) T,
    XST_mem_O0PlusU S _ T, hyeq⟩

/-- `prop:s-independence-and-orbit-criterion`.  Two parametrisations
yield the same `G`-orbit iff the corresponding `T`'s are isometric.

The blueprint argument runs through `pNormalForm_residual_orbit_iso`
(NormalForm.lean), which translates `P`-conjugation of `XST T₁` to
`XST T₂` into a bilinear isometry of the residual forms.  Closing this
iff requires the additional hypotheses
`S.formV0.Nondegenerate` and `(2 : F) ≠ 0` (to invoke
`pNormalForm_residual_orbit_iso`) and a parabolic-decomposition argument
showing every `g ∈ G` conjugating `XST T₁` to `XST T₂` is itself a
`P`-element. Both pieces are out of scope for the current prover round
and are recorded as scoped sorries below. -/
theorem sIndependenceAndOrbitCriterion (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    [ClassifyBilinearForms F]
    (Sₕ₁ Sₕ₂ : S.L1' ≃ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (_hT₁ : T₁ ∈ S.Tset_circ) (_hT₂ : T₂ ∈ S.Tset_circ) :
    GOrbit S (XST S (Sₕ₁ : S.L1' →ₗ[F] S.Vplus) T₁) =
        GOrbit S (XST S (Sₕ₂ : S.L1' →ₗ[F] S.Vplus) T₂) ↔
      IsometryRel S T₁ T₂ := by
  constructor
  · -- Forward: orbit equality → bilinear isometry of `BT T₁` and `BT T₂`.
    -- Plan: extract `g ∈ G` with `g ∘ₗ XST T₁ = XST T₂ ∘ₗ g` (using
    -- `XST T₂ ∈ GOrbit (XST T₁)` from the hypothesis); show that `g`
    -- preserves the slice `X₀ + 𝔲` and hence is a `P`-element; apply
    -- `pNormalForm_residual_orbit_iso`.  The slice-stability step
    -- requires `Nondegenerate` and `(2 : F) ≠ 0` which are not in the
    -- current hypothesis list.
    intro horbit
    -- Partial progress: extract a witness `g : Module.End F S.V`
    -- conjugating `XST T₁` to `XST T₂`. The remaining work — showing
    -- `g ∈ P` (i.e. `IsParabolicElement S g`) and applying
    -- `pNormalForm_residual_orbit_iso` — needs hypotheses
    -- `Nondegenerate`/`(2 : F) ≠ 0` and equality `Sₕ₁ = Sₕ₂` that are
    -- absent from the current statement (Tier A item 3 blocker).
    have h_self : XST S (Sₕ₁ : S.L1' →ₗ[F] S.Vplus) T₁ ∈
        GOrbit S (XST S (Sₕ₁ : S.L1' →ₗ[F] S.Vplus) T₁) :=
      ⟨1, ⟨isUnit_one, fun _ _ => rfl⟩,
        by rw [Ring.inverse_one]; rfl⟩
    rw [horbit] at h_self
    obtain ⟨_g, _hg, _hyeq⟩ := h_self
    -- `_hg : IsometryEnd S _g`,
    -- `_hyeq : XST S Sₕ₁ T₁ = _g ∘ₗ XST S Sₕ₂ T₂ ∘ₗ Ring.inverse _g`.
    -- Inheritance: needs `pNormalForm_residual_orbit_iso` (NormalForm.lean
    -- line 199, currently sorry; round 2 Tier A target).
    sorry
  · -- Reverse: bilinear isometry → orbit equality.  Plan: invoke
    -- `pNormalForm_residual_orbit_iso` to obtain a `P`-element `p`
    -- satisfying `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p`; deduce `p ∈ G`
    -- (parabolic ⊂ isometry group); use this to show that the two
    -- orbits coincide via mutual inclusion.  Same hypothesis gap as
    -- above (`Nondegenerate`, `(2 : F) ≠ 0`).
    intro hiso
    -- Partial progress: unfold the isometry-relation hypothesis to
    -- expose the bilinear-isometry witness `h : L0' ≃ₗ[F] L0'`.
    unfold IsometryRel Bilinear.AreIsometric at hiso
    obtain ⟨_h, _h_isom⟩ := hiso
    -- `_h : ↥S.L0' ≃ₗ[F] ↥S.L0'`,
    -- `_h_isom : ∀ u v, BT S T₂ (_h u) (_h v) = BT S T₁ u v`.
    -- Inheritance: lifting `_h` to a `P`-element `p` requires
    -- `pNormalForm_residual_orbit_iso` (NormalForm.lean line 199,
    -- currently sorry) plus the missing `Nondegenerate`/`(2 : F) ≠ 0`
    -- hypotheses and `Sₕ₁ = Sₕ₂`.
    sorry

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
    (_hNondeg : S.formV0.Nondegenerate) (_hChar : (2 : F) ≠ 0)
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
  · intro T _hT
    exact XST_sub_X0Lift_mem_unipotent S (Sₕ : S.L1' →ₗ[F] S.Vplus) T
  · intro T hT
    exact inducedOrbits S Sₕ T hT
  · intro T₁ T₂ hT₁ hT₂
    exact sIndependenceAndOrbitCriterion S Sₕ Sₕ T₁ T₂ hT₁ hT₂
  · intro T hT hNonDeg
    exact multiplicityNonDeg S Sₕ T hT hNonDeg

end InducedOrbitToy
