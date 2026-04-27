# Informal content for `InducedOrbitToy/NormalForm.lean`

Blueprint sections to formalize: `prop:p-normal-form` (lines 175–319) and
`prop:kernel-image` (lines 321–411) of `references/blueprint_verified.md`.

## Setting

Work over `(S : SliceSetup F)`. Reuse:

- `Basic.lean`: `SliceSetup`, `S.V`, `S.ambientForm`, `S.flagE`, `S.flagEV0`,
  `IsParabolic`, `UnipotentRadical`, `c S`.
- `Slice.lean` (Round 2): `IsSkewB`, `Cdual`, `XCB`, `XST`, `X0Lift`, `uD`,
  `uD_conj_XCB`.

If `Slice.lean` is not yet finalised, this file should still **compile** —
state the theorems below using the names exposed by `Slice.lean`. If the
prover for `NormalForm.lean` runs before `Slice.lean` is filled, it should
emit an explicit dependency comment and use placeholder hypotheses (see
"Fallback" below).

Assume `(hNondeg : S.formV0.Nondegenerate)` and `(hChar : (2 : F) ≠ 0)`
throughout.

## Definitions

### `Tset` — the set `𝒯` of skew operators on `(L0', L0)`

```
def IsSkewT (S : SliceSetup F) (T : S.L0' →ₗ[F] S.L0) : Prop :=
  ∀ u v : S.L0', S.lambda (T u : S.E) v + S.eps * S.lambda (T v : S.E) u = 0
```

Here `(T u : S.E)` is the composition with `S.L0.subtype` and
`S.L0' →ₗ[F] S.L0` is reformulated as a map `S.L0' → S.E` via the inclusion.

### `Tset_circ` — the locus of maximal-rank `T`

```
def Tset_circ (S : SliceSetup F) : Set (S.L0' →ₗ[F] S.L0) :=
  { T | IsSkewT S T ∧ Module.finrank F (LinearMap.range T) = MaximalRank S }
```

where `MaximalRank S : ℕ` matches the blueprint:

```
noncomputable def MaximalRank (S : SliceSetup F) : ℕ :=
  let l := Module.finrank F S.L0'
  if S.eps = 1 ∧ Odd l then l - 1 else l
```

(Use `decide`-friendly hypothesis or split by `S.epsValid`. For autoformalize,
you may state `MaximalRank` abstractly as `if h : S.eps = 1 ∧ Odd l then l - 1 else l`
and discharge case analyses in the prover stage.)

### `Cbar` — the quotient map `C : E' → V0/Im X0`

```
noncomputable def Cbar (S : SliceSetup F) (C : S.E' →ₗ[F] S.V0) :
    S.E' →ₗ[F] (S.V0 ⧸ LinearMap.range S.X0) :=
  (LinearMap.range S.X0).mkQ ∘ₗ C
```

## Theorem `prop:p-normal-form`

The blueprint statement says: under `rank Cbar = c`, `XCB` is `P`-conjugate
to some `XST` with `T ∈ 𝒯`. Decompose into three sub-claims (one for each
numbered item in the blueprint).

For autoformalization, `P-conjugacy` is encoded abstractly as: there exists
an invertible `p : Module.End F S.V` such that `p ∘ XCB ∘ p⁻¹ = XST` and `p`
preserves the flag (i.e. `IsParabolic S (Submodule.span F {p})` plus `p`
is a unit). Use the predicate `IsParabolicElement` defined locally:

```
def IsParabolicElement (S : SliceSetup F) (p : Module.End F S.V) : Prop :=
  IsUnit p ∧ Submodule.map p S.flagE = S.flagE ∧
    Submodule.map p S.flagEV0 = S.flagEV0 ∧
    LinearMap.BilinForm.IsAdjointPair S.ambientForm S.ambientForm p p
```

The third clause encodes "preserves the form" (the right adjoint pair via
`p` and itself); make this concrete using Mathlib's
`LinearMap.BilinForm.IsAdjointPair` API or specialise to "is an isometry."

### `pNormalForm`

```
theorem pNormalForm (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (hB : IsSkewB S B)
    (hRank : Module.finrank F (LinearMap.range (Cbar S C)) = c S.toX0Setup) :
    ∃ (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (hT : IsSkewT S T)
      (p : Module.End F S.V) (_ : IsParabolicElement S p),
        p ∘ₗ XCB S C B = XST S Sₕ T ∘ₗ p := by
  sorry
```

(Adjust `IsParabolicElement` to your final encoding. The point is that
**existence** of a `P`-conjugacy is the goal; the concrete `(Sₕ, T)` is
delivered as part of the `Exists`.)

### `pNormalForm_residual_orbit_iso`

The third numbered item ("Levi action is `T ↦ (h⁻¹)ᵛ T h`, so the orbit is
determined by the isometry class of `(L0', B_T)`"). In autoformalize, expose
this as a theorem connecting `(L0', B_T₁)` and `(L0', B_T₂)`:

```
theorem pNormalForm_residual_orbit_iso (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (Sₕ : S.L1' →ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0) (hT₁ : IsSkewT S T₁) (hT₂ : IsSkewT S T₂) :
    (∃ (p : Module.End F S.V) (_ : IsParabolicElement S p),
        p ∘ₗ XST S Sₕ T₁ = XST S Sₕ T₂ ∘ₗ p) ↔
      Bilinear.AreIsometric (BT S T₁) (BT S T₂) := by
  sorry
```

where `BT S T (u v : S.L0') : F := S.lambda (T u : S.E) v` and
`Bilinear.AreIsometric` is the Mathlib notion. If Mathlib does not expose
this exact name, define a local predicate

```
def AreIsometric {F V} [Field F] [AddCommGroup V] [Module F V]
    (b₁ b₂ : LinearMap.BilinForm F V) : Prop :=
  ∃ (h : V ≃ₗ[F] V), ∀ u v, b₂ (h u) (h v) = b₁ u v
```

## Theorem `prop:kernel-image`

```
theorem kernelImage_ker (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' →ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (hT : IsSkewT S T) :
    LinearMap.ker (XST S Sₕ T) = (Submodule.prod ⊤ (Submodule.prod ⊥
        (LinearMap.ker (T ∘ₗ S.L0'.subtype.codRestrict S.L0' (by simp)))))
        := by sorry
```

(Adjust the right-hand side so it equals `S.E ⊕ ker T` viewed inside `S.V`.
The cleanest way: build a submodule `kerXST_submod` once and write
`= kerXST_submod`.)

```
theorem kernelImage_im (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (hT : IsSkewT S T) :
    LinearMap.range (XST S Sₕ T) = imXST_submod S Sₕ T := by sorry
```

with `imXST_submod` defined to encode `(L1 ⊕ Im T) ⊕ V0` inside
`S.V = E × V0 × E'`.

```
theorem kernelImage_dim (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0) (hT : IsSkewT S T) :
    Module.finrank F (LinearMap.ker (XST S Sₕ T))
      = Module.finrank F S.E + (Module.finrank F S.L0' -
          Module.finrank F (LinearMap.range T)) := by sorry
```

## Fallback

If `Slice.lean` lacks any of the names referenced above (`XCB`, `XST`,
`Cdual`, `IsSkewB`, `X0Lift`), do **not** redefine them locally. Instead,
add `import InducedOrbitToy.Slice` at the top, leave a `/- TODO: depends on
Slice.lean's IsSkewB/XCB/XST -/` comment, and emit a `/- USER: -/` flag in
the file so the plan agent re-routes.

## Acceptance

`lake env lean InducedOrbitToy/NormalForm.lean` succeeds with only `sorry`
warnings, no errors, no axioms. The file may rely on `sorry`-bodied
definitions from `Slice.lean`.
