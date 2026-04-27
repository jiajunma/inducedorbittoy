import Mathlib

/-!
Foundational setup for the induced-orbit toy formalization.

See `references/blueprint_verified.md` and `references/formalization_plan.md`.

This file exposes only the algebraic data shared by every later module:

* `IsEpsSymm`, `IsSkewAdjoint`, `IsPerfectPairing`, `IsPaired`, `IsIsotropic`
  predicates (`Section Predicates` / `Section Pairing`),
* `PairedSpaces`, `X0Setup`, `SliceSetup` structures bundling the data of
  `lem:x0-geometry` and `lem:parametrize-x0-plus-u`,
* `c`, `c_eq_finrank_quotient` (placeholder identity, proved later),
* `SliceSetup.V`, `SliceSetup.ambientForm`, `SliceSetup.flagE`,
  `SliceSetup.flagEV0` (the ambient direct sum and the flag
  `0 ≤ E ≤ E ⊕ V₀ ≤ V`),
* `IsParabolic`, `UnipotentRadical`.
-/

namespace InducedOrbitToy

/-! ## ε-symmetric and skew-adjoint predicates -/

section Predicates

variable {F V : Type*} [CommRing F] [AddCommGroup V] [Module F V]

/-- `B` is ε-symmetric: `B x y = ε * B y x` for all `x, y`. -/
def IsEpsSymm (B : LinearMap.BilinForm F V) (ε : F) : Prop :=
  ∀ x y : V, B x y = ε * B y x

/-- `X` is skew-adjoint with respect to `B`:
`B (X x) y + B x (X y) = 0` for all `x, y`. -/
def IsSkewAdjoint (B : LinearMap.BilinForm F V) (X : V →ₗ[F] V) : Prop :=
  ∀ x y : V, B (X x) y + B x (X y) = 0

end Predicates

/-! ## Perfect-pairing and isotropy predicates -/

section Pairing

variable {F E E' : Type*} [Field F]
  [AddCommGroup E] [Module F E] [AddCommGroup E'] [Module F E']

/-- A pairing `lambda : E →ₗ[F] E' →ₗ[F] F` is *perfect* if it is
non-degenerate on both sides and the two spaces have equal finite dimension. -/
def IsPerfectPairing (lambda : E →ₗ[F] E' →ₗ[F] F) : Prop :=
  Function.Injective lambda ∧ Function.Injective lambda.flip ∧
    Module.finrank F E = Module.finrank F E'

/-- Subspaces `S ≤ E` and `S' ≤ E'` are *paired* by `lambda` if the
restriction is non-degenerate on both sides and `S, S'` have equal
finite dimension. -/
def IsPaired (lambda : E →ₗ[F] E' →ₗ[F] F)
    (S : Submodule F E) (S' : Submodule F E') : Prop :=
  Module.finrank F S = Module.finrank F S' ∧
    (∀ x ∈ S, (∀ y ∈ S', lambda x y = 0) → x = 0) ∧
    (∀ y ∈ S', (∀ x ∈ S, lambda x y = 0) → y = 0)

/-- Subspaces `S ≤ E` and `S' ≤ E'` are *jointly isotropic* under
`lambda` if `lambda x y = 0` for every `x ∈ S` and `y ∈ S'`. -/
def IsIsotropic (lambda : E →ₗ[F] E' →ₗ[F] F)
    (S : Submodule F E) (S' : Submodule F E') : Prop :=
  ∀ x ∈ S, ∀ y ∈ S', lambda x y = 0

end Pairing

/-! ## Paired vector spaces `(E, E')` -/

/-- Two finite-dimensional vector spaces over `F` together with a perfect
pairing `E × E' → F`. -/
structure PairedSpaces (F : Type*) [Field F] where
  E : Type*
  [addCommGroupE : AddCommGroup E]
  [moduleE : Module F E]
  [finiteE : Module.Finite F E]
  E' : Type*
  [addCommGroupE' : AddCommGroup E']
  [moduleE' : Module F E']
  [finiteE' : Module.Finite F E']
  pairing : E →ₗ[F] E' →ₗ[F] F
  isPerfect : IsPerfectPairing pairing

attribute [instance] PairedSpaces.addCommGroupE PairedSpaces.moduleE
  PairedSpaces.finiteE PairedSpaces.addCommGroupE' PairedSpaces.moduleE'
  PairedSpaces.finiteE'

/-! ## The `X0` setup -/

/-- The data of `lem:x0-geometry`: a finite-dimensional `F`-vector space
`V₀` with an `ε`-symmetric bilinear form, a skew-adjoint endomorphism
`X₀`, and a chosen complement `V₊` to `range X₀`. -/
structure X0Setup (F : Type*) [Field F] where
  V0 : Type*
  [addCommGroupV0 : AddCommGroup V0]
  [moduleV0 : Module F V0]
  [finiteV0 : Module.Finite F V0]
  formV0 : LinearMap.BilinForm F V0
  eps : F
  epsValid : eps = 1 ∨ eps = -1
  epsSymm : IsEpsSymm formV0 eps
  X0 : V0 →ₗ[F] V0
  skew : IsSkewAdjoint formV0 X0
  Vplus : Submodule F V0
  isCompl : IsCompl Vplus (LinearMap.range X0)

attribute [instance] X0Setup.addCommGroupV0 X0Setup.moduleV0 X0Setup.finiteV0

/-- The integer `c := dim_F (ker X₀)`. -/
noncomputable def c {F : Type*} [Field F] (S : X0Setup F) : ℕ :=
  Module.finrank F (LinearMap.ker S.X0)

/-- Structural identity `c = dim (V₀ / Im X₀)`; placeholder until proved
in the `prover` stage. -/
theorem c_eq_finrank_quotient {F : Type*} [Field F] (S : X0Setup F) :
    c S = Module.finrank F (S.V0 ⧸ LinearMap.range S.X0) := by
  unfold c
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.range S.X0)
  have hrank := LinearMap.finrank_range_add_finrank_ker S.X0
  omega

/-! ## The slice setup -/

/-- The data of `lem:parametrize-x0-plus-u`: an `X0Setup`, a `PairedSpaces`
and a Lagrangian-style decomposition of `E`, `E'`:
* `L₁` is perfectly paired with `L₁'` and `L₀` is perfectly paired with
  `L₀'` (so `L₁ ⊕ L₀ = E` and `L₁' ⊕ L₀' = E'` are dual decompositions),
* the cross-pairings `λ(L₁, L₀') = 0` and `λ(L₀, L₁') = 0` vanish. -/
structure SliceSetup (F : Type*) [Field F] extends X0Setup F where
  paired : PairedSpaces F
  L1 : Submodule F paired.E
  L0 : Submodule F paired.E
  L1' : Submodule F paired.E'
  L0' : Submodule F paired.E'
  isComplL : IsCompl L1 L0
  isComplL' : IsCompl L1' L0'
  L1_paired : IsPaired paired.pairing L1 L1'
  L0_paired : IsPaired paired.pairing L0 L0'
  L1_isotropic_L0' : IsIsotropic paired.pairing L1 L0'
  L0_isotropic_L1' : IsIsotropic paired.pairing L0 L1'

namespace SliceSetup

variable {F : Type*} [Field F] (S : SliceSetup F)

/-- The first paired space (the "left" side of the pairing). -/
abbrev E : Type _ := S.paired.E

/-- The second paired space (the "right" side of the pairing). -/
abbrev E' : Type _ := S.paired.E'

/-- The pairing `λ : E →ₗ[F] E' →ₗ[F] F`. -/
abbrev lambda : S.paired.E →ₗ[F] S.paired.E' →ₗ[F] F := S.paired.pairing

/-- The ambient direct sum `V := E ⊕ V₀ ⊕ E'`. -/
abbrev V : Type _ := S.paired.E × S.V0 × S.paired.E'

/-- The inherited bilinear form on `V = E ⊕ V₀ ⊕ E'`:
`B((e₁, v₁, e₁'), (e₂, v₂, e₂')) = λ(e₁, e₂') + B₀(v₁, v₂) + ε · λ(e₂, e₁')`. -/
noncomputable def ambientForm : LinearMap.BilinForm F S.V :=
  LinearMap.mk₂ F
    (fun x y => S.paired.pairing x.1 y.2.2 + S.formV0 x.2.1 y.2.1
                  + S.eps * S.paired.pairing y.1 x.2.2)
    (by
      intro m₁ m₂ n
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring)
    (by
      intro c m n
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      ring)
    (by
      intro m n₁ n₂
      simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
      ring)
    (by
      intro c m n
      simp only [Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      ring)

/-- The first non-trivial step of the flag `0 ≤ E ≤ E ⊕ V₀ ≤ V`:
`E ↪ V` as `{(e, 0, 0) | e ∈ E}`. -/
def flagE : Submodule F S.V := Submodule.prod ⊤ (Submodule.prod ⊥ ⊥)

/-- The second non-trivial step of the flag: `(E ⊕ V₀) ↪ V` as
`{(e, v, 0) | e ∈ E, v ∈ V₀}`. -/
def flagEV0 : Submodule F S.V := Submodule.prod ⊤ (Submodule.prod ⊤ ⊥)

end SliceSetup

/-! ## Parabolic subspaces and the unipotent radical -/

/-- A subspace `P ≤ End F V` is *parabolic* (relative to the flag
`0 ≤ E ≤ E ⊕ V₀ ≤ V`) if every endomorphism in `P` stabilises both
`E` and `E ⊕ V₀`. -/
def IsParabolic {F : Type*} [Field F] (S : SliceSetup F)
    (P : Submodule F (Module.End F S.V)) : Prop :=
  ∀ f ∈ P, Submodule.map f S.flagE ≤ S.flagE ∧
            Submodule.map f S.flagEV0 ≤ S.flagEV0

/-- The unipotent radical `𝔲 = 𝔭 ∩ 𝔤 ≤ End F V`: maps that send each step
of the flag `0 ≤ E ≤ E ⊕ V₀ ≤ V` into the next-lower step *and* are
skew-adjoint with respect to `S.ambientForm`.

Concretely:
* `f` annihilates `E`,
* `f` sends `E ⊕ V₀` into `E`,
* `f` sends all of `V` into `E ⊕ V₀`,
* `f` is skew-adjoint w.r.t. `S.ambientForm` (the form-preservation
  condition that distinguishes `𝔲 = 𝔭 ∩ 𝔤` from the loose parabolic
  subspace `𝔭`). -/
noncomputable def UnipotentRadical {F : Type*} [Field F] (S : SliceSetup F) :
    Submodule F (Module.End F S.V) where
  carrier :=
    { f | (∀ x ∈ S.flagE, f x = 0) ∧
          (∀ x ∈ S.flagEV0, f x ∈ S.flagE) ∧
          (∀ x : S.V, f x ∈ S.flagEV0) ∧
          IsSkewAdjoint S.ambientForm f }
  zero_mem' :=
    ⟨fun _ _ => rfl,
     fun _ _ => Submodule.zero_mem _,
     fun _ => Submodule.zero_mem _,
     by
       intro x y
       simp [LinearMap.zero_apply, map_zero]⟩
  add_mem' := by
    rintro f g ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simp [LinearMap.add_apply, h1 x hx, h1' x hx]
    · intro x hx
      simpa [LinearMap.add_apply] using
        Submodule.add_mem _ (h2 x hx) (h2' x hx)
    · intro x
      simpa [LinearMap.add_apply] using
        Submodule.add_mem _ (h3 x) (h3' x)
    · intro x y
      have hf := h4 x y
      have hg := h4' x y
      simp only [LinearMap.add_apply, map_add, LinearMap.add_apply]
      linear_combination hf + hg
  smul_mem' := by
    rintro c f ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simp [LinearMap.smul_apply, h1 x hx]
    · intro x hx
      simpa [LinearMap.smul_apply] using
        Submodule.smul_mem _ c (h2 x hx)
    · intro x
      simpa [LinearMap.smul_apply] using
        Submodule.smul_mem _ c (h3 x)
    · intro x y
      have hf := h4 x y
      simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
      linear_combination c * hf

end InducedOrbitToy
