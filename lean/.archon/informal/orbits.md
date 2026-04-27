# Informal content for `InducedOrbitToy/Orbits.lean`

Blueprint sections to formalize:
- `prop:induced-orbits` (lines 433–625)
- `prop:s-independence-and-orbit-criterion` (lines 627–684)
- `prop:multiplicity` (lines 686–800)
- `thm:main` (lines 802–1049, primarily the statement at lines 980–1038)

## Setting

Imports `InducedOrbitToy.LocalForms`. Reuses everything below up the chain.

This is the highest-risk module. Many of the blueprint's notions involve
infrastructure Mathlib does not expose for arbitrary fields:
- Algebraic groups (`G`, `G_0`, `P`).
- Identity components `H^∘` and component groups `π_0(H)`.
- Analytic topology on `𝔤` and orbit closures `\overline{G \cdot \Omega}`.

For autoformalize we **abstract these notions** as hypothesis bundles or
local definitions and **state the theorems abstractly**. Closing the proofs
is deferred far past the prover stage.

## Suggested local API

### Group of isometries `G`

```
def IsometryEnd (S : SliceSetup F) (g : Module.End F S.V) : Prop :=
  IsUnit g ∧ LinearMap.BilinForm.IsAdjointPair S.ambientForm S.ambientForm g g
```

Bundle into a `Submonoid` or `Subgroup` of `(Module.End F S.V)ˣ` if the
prover prefers a group-shaped object. The existing
`Mathlib.LinearAlgebra.QuadraticForm.Isometry` API may help; consult
`lean_leansearch "isometry bilinear form"` first.

### `G_0` — isometries of `(V0, formV0)`

```
def IsometryV0 (S : SliceSetup F) (g₀ : Module.End F S.V0) : Prop :=
  IsUnit g₀ ∧ LinearMap.BilinForm.IsAdjointPair S.formV0 S.formV0 g₀ g₀
```

### `P` — parabolic subgroup

```
def IsInP (S : SliceSetup F) (g : Module.End F S.V) : Prop :=
  IsometryEnd S g ∧ Submodule.map g S.flagE = S.flagE
```

(The blueprint's `P` only requires `g(E) = E`; preservation of the form
is part of being in `G`.)

### `O0` — the `G_0`-orbit of `X0`

```
def O0 (S : SliceSetup F) : Set (Module.End F S.V0) :=
  { Y | ∃ g₀ : Module.End F S.V0, IsometryV0 S g₀ ∧
        Y = g₀ ∘ₗ S.X0 ∘ₗ (Ring.inverse g₀) }
```

(Simplified — adjust to use `g₀ * X0 * g₀⁻¹` once `Ring.inverse` typechecks
or use `Units` directly.)

### Embedding `O0 ↪ End F V`

Define `embO0 S Y : Module.End F S.V` lifting `Y ∈ End F V0` to act only on
the `V0` summand of `S.V` (zero on `S.E` and `S.E'`). Reuse `X0Lift` from
`Slice.lean`'s style.

### `O0 + 𝔲`

```
def O0PlusU (S : SliceSetup F) : Set (Module.End F S.V) :=
  { x | ∃ Y₀ ∈ O0 S, ∃ U ∈ UnipotentRadical S, x = embO0 S Y₀ + U }
```

### `IndPG` — the induced set

For autoformalize, do **not** insist on the analytic topology. State the
induced set as the `G`-orbit closure abstractly:

```
def IndPG (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)] : Set (Module.End F S.V) :=
  closure { x | ∃ g : Module.End F S.V, IsometryEnd S g ∧
              ∃ y ∈ O0PlusU S, x = g ∘ₗ y ∘ₗ (Ring.inverse g) }
```

Take `[TopologicalSpace (Module.End F S.V)]` as a hypothesis on each
theorem (or as a section variable). **Do not** define a topology yourself.

### Centraliser `Z_G(x)`

```
def ZG (S : SliceSetup F) (x : Module.End F S.V) :
    Submonoid (Module.End F S.V) where
  carrier := { g | IsometryEnd S g ∧ g * x = x * g }
  -- + closure proofs
```

Use `Submonoid` (not `Subgroup`) at first; this matches working in
`Module.End F S.V` rather than units. Promote later if needed.

### Multiplicity `m(G·x, P)`

This requires `π_0(H)` (component group). Mathlib has limited support.
**Abstract this away**: define `Multiplicity` as a parameter:

```
def Multiplicity (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (x : Module.End F S.V) : ℕ :=
  Nat.card (ZG S x ⧸ ((ZG S x).subgroupOf (ZGcapP S x))) -- placeholder
```

If this becomes too painful, **simplify to a Prop**: state
`m(G·x, P) = n` as a hypothesis predicate and let the theorems take it as
a parameter. The plan agent will adjust during the prover stage.

## Theorems to state

### `inducedOrbits` (`prop:induced-orbits`)

```
theorem inducedOrbits (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (hClassify : ClassifyBilinearForms F)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) :
    -- The maximal G-orbits in IndPG S are exactly { G·X_{Sₕ,T} | T ∈ Tset_circ }
    sorry := by sorry
```

Frame the conclusion as a `Set.range` equality or a bijection between the
maximal-orbit set and `Tset_circ S / ~_isometry`. For autoformalize, simply
write a placeholder statement that compiles.

### `sIndependenceAndOrbitCriterion` (`prop:s-independence-and-orbit-criterion`)

```
theorem sIndependenceAndOrbitCriterion (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (hClassify : ClassifyBilinearForms F)
    (Sₕ₁ Sₕ₂ : S.L1' ≃ₗ[F] S.Vplus)
    (T₁ T₂ : S.L0' →ₗ[F] S.L0)
    (hT₁ : T₁ ∈ Tset_circ S) (hT₂ : T₂ ∈ Tset_circ S) :
    GOrbit S (XST S Sₕ₁ T₁) = GOrbit S (XST S Sₕ₂ T₂) ↔
      IsometryRel S T₁ T₂ := by
  sorry
```

with `GOrbit S x := { g ∘ₗ x ∘ₗ Ring.inverse g | g, IsometryEnd S g }`
defined locally.

### `multiplicity` (`prop:multiplicity`)

```
theorem multiplicityNonDeg (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0)
    (hT : T ∈ Tset_circ S)
    (hNonDeg : Module.finrank F (LinearMap.range T) = Module.finrank F S.L0') :
    Multiplicity S (XST S Sₕ T) = 1 := by
  sorry

theorem multiplicityOddCase (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (T : S.L0' →ₗ[F] S.L0)
    (hT : T ∈ Tset_circ S)
    (hEps : S.eps = 1) (hOdd : Odd (Module.finrank F S.L0')) :
    Multiplicity S (XST S Sₕ T) = 2 := by
  sorry
```

### `main` (`thm:main`)

The four assertions of `thm:main` are corollaries of the four theorems
above. State `main` as a conjunction (or a `structure MainConclusion` if
that compiles more cleanly):

```
theorem main (S : SliceSetup F)
    [TopologicalSpace (Module.End F S.V)]
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (hClassify : ClassifyBilinearForms F)
    (Sₕ : S.L1' ≃ₗ[F] S.Vplus) :
    -- (1) Every X_{S,T} ∈ X0 + 𝔲
    (∀ T, IsSkewT S T → XST S Sₕ T - X0Lift S ∈ UnipotentRadical S) ∧
    -- (2) Maximal G-orbits in IndPG = { G·X_{S,T} | T ∈ Tset_circ }
    True ∧  -- placeholder; restate from inducedOrbits
    -- (3) Orbit independence + isometry criterion
    True ∧  -- placeholder; restate from sIndependenceAndOrbitCriterion
    -- (4) Multiplicity formula
    True := by sorry  -- placeholder; restate from multiplicity
```

For a clean autoformalize, replace each `True` placeholder with the actual
conjunct extracted from the corresponding theorem above.

## What is NOT required for this round

- Proving anything. The prover stage will struggle even to formalize these
  notions without additional Mathlib infrastructure; the autoformalize stage
  only needs the file to compile.
- Defining the analytic topology on `Module.End F S.V`. Take it as a
  hypothesis.
- Implementing `Multiplicity` semantically — an opaque `ℕ`-valued function
  is fine.
- Correctness of the placeholder `True` conjuncts in `main`. Just compile.

## Acceptance

`lake env lean InducedOrbitToy/Orbits.lean` succeeds with only `sorry`
warnings, no errors, no axioms.

If the prover finds that the abstractions above are too inert (e.g. the
group / centraliser machinery resists statement), report back **with the
specific Mathlib lemmas missing** so the plan agent can re-route. Do
**not** silently introduce `axiom` declarations.
