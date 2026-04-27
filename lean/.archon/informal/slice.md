# Informal content for `InducedOrbitToy/Slice.lean`

Blueprint sections to formalize: `lem:parametrize-x0-plus-u` (lines 56–119) and
`lem:unipotent-conjugation` (lines 121–173) of
`references/blueprint_verified.md`.

## Setting

Work over `(S : SliceSetup F)`. `S` already provides:

* `S.V0`, `S.X0`, `S.Vplus`, `S.formV0`, `S.eps`, `S.epsValid`, `S.epsSymm`,
  `S.skew`, `S.isCompl` (from `X0Setup`).
* `S.paired : PairedSpaces F`, with `S.E := S.paired.E`, `S.E' := S.paired.E'`,
  `S.lambda := S.paired.pairing`, and `S.paired.isPerfect`.
* Lagrangian decompositions `S.L1 ⊕ S.L0 = ⊤` (`S.E`) and
  `S.L1' ⊕ S.L0' = ⊤` (`S.E'`), with `S.L1_paired`, `S.L0_isotropic`,
  `S.isComplL`, `S.isComplL'`.
* `S.V := S.E × S.V0 × S.E'`, the ambient direct sum.
* `S.ambientForm : LinearMap.BilinForm F S.V`, definitionally
  `λ(e₁,e₂') + B₀(v₁,v₂) + ε · λ(e₂,e₁')`.
* `S.flagE`, `S.flagEV0` — the two non-trivial steps of the flag.
* `IsParabolic S P : Prop` and `UnipotentRadical S : Submodule F (Module.End F S.V)`.

For autoformalization purposes, also assume `S.formV0.Nondegenerate` as an
explicit `(hNondeg : S.formV0.Nondegenerate)` hypothesis on the main theorems —
the perfect-pairing claims need it.

## Objects to define

### `Cdual` — the transpose of `C : E' →ₗ[F] V0`

For `C : S.E' →ₗ[F] S.V0`, define `Cdual S C : S.V0 →ₗ[F] S.E` to be the unique
linear map satisfying `lambda (Cdual v) e' = - B₀ v (C e')` for every `v, e'`.

Mathlib hint. The pairing `S.paired.isPerfect` makes `S.lambda.flip` injective,
so `Module.Dual.eval`-type arguments produce a unique `Cdual`. Concretely use
`LinearMap.IsPerfPair`'s "every dual functional has a representative" API:
the map `v ↦ -B₀(v, C·)` is in `Module.Dual F S.E'`, and via `lambda` this
lifts to `S.E`. **For autoformalize, exposing `Cdual` as a `noncomputable def`
with a `sorry` body and a separate characterisation lemma `Cdual_pairing_eq`
(which is `sorry` for now) is acceptable.**

### `XCB` — the operator parametrised by `(C, B)`

For `C : S.E' →ₗ[F] S.V0` and `B : S.E' →ₗ[F] S.E` satisfying the skewness
condition `lambda (B u) v + ε · lambda (B v) u = 0`, define

```
XCB : S.V →ₗ[F] S.V
XCB (e + v + e') := Cdual v + B e' + X0 v + C e'
```

Concretely on the `Prod` ambient: `XCB (e, v, e') = (Cdual v + B e', X0 v + C e', 0)`.

Build it with `LinearMap.fst`/`snd`/`inl`/`inr` over `Prod`.

### `IsSkewB` — the skewness condition on `B`

```
def IsSkewB (S : SliceSetup F) (B : S.E' →ₗ[F] S.E) : Prop :=
  ∀ u v : S.E', S.lambda (B u) v + S.eps * S.lambda (B v) u = 0
```

### `XST` — the special case `X_{S,T}`

Take `Sₕ : S.L1' →ₗ[F] S.Vplus` (an isomorphism, but for the def we only need
a linear map) and `T : S.L0' →ₗ[F] S.L0`. Build `Cₛₜ : S.E' →ₗ[F] S.V0` from
`Sₕ` extended by zero on `L0'`, and `Bₛₜ : S.E' →ₗ[F] S.E` from `T` extended by
zero on `L1'`. Define `XST S Sₕ T := XCB S Cₛₜ Bₛₜ`.

For the `S.E' = S.L1' ⊕ S.L0'` decomposition, use `Submodule.linearProjOfIsCompl`
and the `IsCompl S.L1' S.L0'` hypothesis (`S.isComplL'`).

## Theorems to state

### `parametrizeX0PlusU_mem` (`X_{C,B} ∈ X0 + 𝔲`)

```
theorem parametrizeX0PlusU_mem (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (hB : IsSkewB S B) :
    XCB S C B - X0Lift S ∈ UnipotentRadical S := by
  sorry
```

Here `X0Lift S : Module.End F S.V` is the lift of `S.X0` to the ambient `S.V`
acting only on the `V0`-summand:

```
def X0Lift (S : SliceSetup F) : Module.End F S.V :=
  LinearMap.inr F S.E (S.V0 × S.E') ∘ₗ (LinearMap.inl F S.V0 S.E') ∘ₗ
    S.X0 ∘ₗ (LinearMap.snd F S.V0 S.E') ∘ₗ (LinearMap.snd F S.E (S.V0 × S.E'))
```

(or whatever cleaner formulation works). **Adjust the precise definition during
formalization — the spirit is "act by `X0` on the `V0`-summand and zero on
`E`, `E'`."**

### `parametrizeX0PlusU_uniqueness`

```
theorem parametrizeX0PlusU_uniqueness (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (Y : Module.End F S.V) (hY : Y ∈ UnipotentRadical S) :
    ∃! (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (_ : IsSkewB S B),
      XCB S C B - X0Lift S = Y := by
  sorry
```

(May be split into existence + uniqueness for cleanliness.)

### `unipotentEndomorphism_uD`

For `D : S.E' →ₗ[F] S.V0`, define

```
noncomputable def uD (S : SliceSetup F) (D : S.E' →ₗ[F] S.V0) : Module.End F S.V
```

with formula `(e + v + e') ↦ (e + Dᵛ v + ½ Dᵛ D e', v + D e', e')`. Note
the `½` requires `2` invertible in `F`. **For autoformalize, take
`(hChar : (2 : F) ≠ 0)` as a hypothesis** (or enforce `[CharZero F]` /
`[Invertible (2 : F)]`).

### `uD_isParabolic`

```
theorem uD_isParabolic (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    -- u_D preserves the form and the flag
    sorry  -- exact statement TBD; see below
```

Concretely the conclusion should bundle:
1. `LinearMap.compl₁₂ S.ambientForm (uD S D) (uD S D) = S.ambientForm`
   (preserves the form), and
2. `Submodule.map (uD S D) S.flagE ≤ S.flagE` and the analogous claim for
   `S.flagEV0` (preserves the flag).

A clean Mathlib-shaped statement is

```
theorem uD_isParabolic (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0) :
    LinearMap.BilinForm.IsAdjointPair S.ambientForm S.ambientForm
      (uD S D) (uD S D) ∧
      Submodule.map (uD S D) S.flagE ≤ S.flagE ∧
      Submodule.map (uD S D) S.flagEV0 ≤ S.flagEV0 := by
  sorry
```

### `uD_conj_XCB`

```
theorem uD_conj_XCB (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (D : S.E' →ₗ[F] S.V0)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (hB : IsSkewB S B) :
    -- u_D ∘ XCB ∘ u_D⁻¹ = X_{C - X0 D, B + Dᵛ C - Cᵛ D - Dᵛ X0 D}
    sorry
```

For autoformalize, the prover may state this conditionally on
`uD S D` being invertible (or just use the explicit inverse `uD S (-D)`).

## Key strategies

1. Use `S.V := S.E × S.V0 × S.E'` and the standard `Prod` API
   (`LinearMap.fst`, `LinearMap.snd`, `LinearMap.inl`, `LinearMap.inr`,
   `Prod.ext_iff`) for the block-matrix calculations.
2. For decomposing `S.E'` as `S.L1' ⊕ S.L0'`, use
   `Submodule.linearProjOfIsCompl` to project, and
   `Submodule.subtype` to embed. The same applies to `S.E = S.L1 ⊕ S.L0`.
3. The bilinear form `S.ambientForm` is already built in `Basic.lean`; reuse
   it, do not redefine.
4. Skewness lemmas should `unfold IsSkewAdjoint` once and then reduce to
   bilinear-form manipulations. The `S.skew` field provides the X0-skewness.

## What is NOT required for this round

- Filling any `sorry` body. Autoformalize stage only requires the file to
  compile with statements in place.
- Proving the conjugation formula in `uD_conj_XCB`. Just state it.
- Providing topology / closure structure on `S.V`. Defer to `Orbits.lean`.

## Acceptance

`lake env lean InducedOrbitToy/Slice.lean` succeeds with only `sorry`
warnings, no errors, no axioms. Aggregate `lake build` continues to succeed.
