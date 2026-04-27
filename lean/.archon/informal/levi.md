# Levi machinery for `InducedOrbitToy/Slice.lean` (Round 6)

This file specifies the additive Levi-action machinery that Round 6 must
add to `InducedOrbitToy/Slice.lean`. **No existing declaration in
`Slice.lean` should be edited.** The Levi machinery is purely new code,
appended after the existing `uD_conj_XCB` (currently around line 564
through end-of-file at line 679).

## Background and blueprint references

- `references/blueprint_verified.md` §`prop:p-normal-form`, lines 200–319.
  In particular: lines 276–278 give the block formula
  `m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` for `m = leviGL_E d ·
  leviGL_V0 g₀`.
- The Levi factor of the parabolic `P` decomposes as
  `M_P ≃ G_0 × GL(E')`, where `G_0 ⊂ GL(V_0)` is the isometry group of
  `formV0`. (Blueprint line 276 implicitly: `m` acts as `g_0` on `V_0`,
  `d` on `E'`, and `(d⁻¹)^∨` on `E`.)
- The "dual transpose `(d⁻¹)^∨ : E → E`" is computed via the perfect
  pairing `S.lambda : E →ₗ[F] E' →ₗ[F] F`. For `e : E`, the linear
  functional `S.lambda e ∘ d⁻¹ : E' → F` lifts back to a unique element
  of `E` via `S.paired.isPerfect`. That element is `(d⁻¹)^∨ e`.

## Machinery to add

The Round 6 prover must add the following declarations, in this order,
to `InducedOrbitToy/Slice.lean`. **Use the exact Lean signatures below**
— the Round 7 prover for `NormalForm.lean` will write proofs against
these signatures.

### Section 6.1 — Dual transpose on `E`

```lean
/-- For `g : S.E' →ₗ[F] S.E'`, the **dual transpose** `g^∨ : S.E →ₗ[F] S.E`
under the perfect pairing `S.lambda`. Defined by the universal property
`λ(g^∨ e, e') = λ(e, g e')`.

This packages `LinearMap.IsPerfPair`'s round-trip: given `e : S.E`, the
functional `e' ↦ S.lambda e (g e')` is in `Module.Dual F S.E'`, which
the perfect pairing identifies with `S.E`. -/
noncomputable def lambdaDualE (S : SliceSetup F)
    (g : S.E' →ₗ[F] S.E') : S.E →ₗ[F] S.E :=
  -- Hint: use `S.paired.isPerfect.toPerfPair.symm` composed with
  -- `LinearMap.flip` and `g`'s precomposition.
  sorry

/-- Defining identity for `lambdaDualE`. -/
theorem lambdaDualE_pairing_eq (S : SliceSetup F)
    (g : S.E' →ₗ[F] S.E') (e : S.E) (e' : S.E') :
    S.lambda (lambdaDualE S g e) e' = S.lambda e (g e') := by
  -- Hint: should be `apply_symm_toPerfPair_self` style.
  sorry

/-- The dual transpose preserves identity. -/
theorem lambdaDualE_id (S : SliceSetup F) :
    lambdaDualE S (LinearMap.id) = LinearMap.id := by
  sorry

/-- The dual transpose is contravariant in composition. -/
theorem lambdaDualE_comp (S : SliceSetup F)
    (g₁ g₂ : S.E' →ₗ[F] S.E') :
    lambdaDualE S (g₁ ∘ₗ g₂) = lambdaDualE S g₂ ∘ₗ lambdaDualE S g₁ := by
  sorry
```

### Section 6.2 — Levi block embeddings

```lean
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

/-- The Levi `G_0` block: for `g : S.V0 ≃ₗ[F] S.V0` preserving the form
`formV0`, the action on `S.V` is `(id_E, g, id_{E'})`. -/
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
```

(The exact RHS may need adjustment — use whatever cleanly produces the
block-diagonal action. The key acceptance criterion is the
`leviGL_E_apply` / `leviGL_V0_apply` lemmas below.)

```lean
/-- Pointwise formula for `leviGL_E`. -/
theorem leviGL_E_apply (S : SliceSetup F) (d : S.E' ≃ₗ[F] S.E')
    (e : S.E) (v : S.V0) (e' : S.E') :
    leviGL_E S d (e, v, e') =
      (lambdaDualE S (d.symm : S.E' →ₗ[F] S.E') e, v, d e') := by
  sorry

/-- Pointwise formula for `leviGL_V0`. -/
theorem leviGL_V0_apply (S : SliceSetup F) (g : S.V0 ≃ₗ[F] S.V0)
    (e : S.E) (v : S.V0) (e' : S.E') :
    leviGL_V0 S g (e, v, e') = (e, g v, e') := by
  sorry
```

### Section 6.3 — Inverses

```lean
/-- `leviGL_E` is multiplicative-inverse compatible:
`leviGL_E d.symm ∘ leviGL_E d = id`. -/
theorem leviGL_E_symm_inverse (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') :
    leviGL_E S d.symm ∘ₗ leviGL_E S d = LinearMap.id := by
  sorry

theorem leviGL_V0_symm_inverse (S : SliceSetup F)
    (g : S.V0 ≃ₗ[F] S.V0) :
    leviGL_V0 S g.symm ∘ₗ leviGL_V0 S g = LinearMap.id := by
  sorry
```

### Section 6.4 — Parabolicity

For `leviGL_V0` to be a parabolic element (preserving the ambient form),
`g` must be a `formV0`-isometry. Bake this into the hypothesis:

```lean
/-- `leviGL_E d` is in the parabolic. -/
theorem leviGL_E_isParabolic (S : SliceSetup F)
    (d : S.E' ≃ₗ[F] S.E') :
    IsParabolicElement S (leviGL_E S d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- IsUnit (leviGL_E d): use the symm inverse.
    sorry
  · -- Submodule.map (leviGL_E d) S.flagE = S.flagE
    -- (leviGL_E d preserves E ⊆ S.V because the E-block is bijective.)
    sorry
  · -- Submodule.map (leviGL_E d) S.flagEV0 = S.flagEV0
    -- (leviGL_E d preserves E ⊕ V0 ⊆ S.V because both blocks are
    -- bijective and the V0-block is the identity.)
    sorry
  · -- LinearMap.IsOrthogonal S.ambientForm (leviGL_E d)
    -- Use the defining identity of lambdaDualE: λ((d⁻¹)^∨ e₁, e₂') =
    -- λ(e₁, d⁻¹ e₂'); plug into the ambient form formula and the d
    -- on E' applied to e₁'.
    sorry

/-- `leviGL_V0 g` is in the parabolic, when `g` is a `formV0`-isometry. -/
theorem leviGL_V0_isParabolic (S : SliceSetup F)
    (g : S.V0 ≃ₗ[F] S.V0)
    (hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v) :
    IsParabolicElement S (leviGL_V0 S g) := by
  -- Same template; isometry of `S.ambientForm` reduces to `hg` on the
  -- V0 block (both other blocks are the identity).
  sorry
```

### Section 6.5 — Conjugation transformation of `XCB`

```lean
/-- Levi-conjugation of `XCB` on `E'` (blueprint line 278, restricted to
the `E'` factor): `leviGL_E d ∘ XCB(C, B) = XCB(C ∘ d⁻¹, (d⁻¹)^∨ ∘ B ∘ d⁻¹)
∘ leviGL_E d`. -/
theorem leviGL_E_conj_XCB (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (d : S.E' ≃ₗ[F] S.E')
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (hB : IsSkewB S B) :
    leviGL_E S d ∘ₗ XCB S C B =
      XCB S (C ∘ₗ (d.symm : S.E' →ₗ[F] S.E'))
            (lambdaDualE S (d.symm : S.E' →ₗ[F] S.E')
              ∘ₗ B ∘ₗ (d.symm : S.E' →ₗ[F] S.E'))
        ∘ₗ leviGL_E S d := by
  -- Direct block calculation via XCB_apply / leviGL_E_apply / Cdual_pairing_eq.
  sorry

/-- Levi-conjugation of `XCB` on `V0` (blueprint line 278, restricted to
the `V0` factor): `leviGL_V0 g ∘ XCB(C, B) = XCB(g ∘ C, B) ∘ leviGL_V0 g`,
when `g` is a `formV0`-isometry **and** commutes with `S.X0`. -/
theorem leviGL_V0_conj_XCB (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate)
    (g : S.V0 ≃ₗ[F] S.V0)
    (hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v)
    (hgX : g ∘ₗ (S.X0 : S.V0 →ₗ[F] S.V0) = S.X0 ∘ₗ (g : S.V0 →ₗ[F] S.V0))
    -- Wait — S.X0 : S.V0 →ₗ[F] S.V0, so this is g X0 = X0 g.
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E) (hB : IsSkewB S B) :
    leviGL_V0 S g ∘ₗ XCB S C B =
      XCB S ((g : S.V0 →ₗ[F] S.V0) ∘ₗ C) B ∘ₗ leviGL_V0 S g := by
  sorry
```

(The `hgX` hypothesis is needed because `Cdual` lands in `E` but the
`V0`-block of `XCB` involves `X0`. Whether this is generic or specialised
to `g = id` depends on what Round 7 actually needs. Round 7 may only
require `leviGL_E_conj_XCB` since `g₀` can sometimes be taken trivially.)

### Section 6.6 — Levi/unipotent decomposition (optional but recommended)

```lean
/-- Levi/unipotent decomposition of a parabolic element. Every element
of the parabolic factors as `uD D ∘ leviGL_E d ∘ leviGL_V0 g₀` for some
`D : E' →ₗ V0`, `d : E' ≃ₗ E'`, and `formV0`-isometry `g₀ : V0 ≃ₗ V0`.

This is the structural theorem used by `residual_levi_extract` in
`NormalForm.lean`. The proof extracts `g₀` from the action on
`flagEV0 / flagE ≃ V0`, `(d⁻¹)^∨` from the action on `flagE = E`, and
`D` from the residual off-diagonal mass. -/
theorem parabolic_decompose (S : SliceSetup F)
    (hNondeg : S.formV0.Nondegenerate) (hChar : (2 : F) ≠ 0)
    (p : Module.End F S.V) (hp : IsParabolicElement S p) :
    ∃ (D : S.E' →ₗ[F] S.V0) (d : S.E' ≃ₗ[F] S.E')
      (g : S.V0 ≃ₗ[F] S.V0)
      (_ : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v),
      p = uD S D ∘ₗ leviGL_E S d ∘ₗ leviGL_V0 S g := by
  sorry
```

**This is the hardest piece of Round 6.** If the Round 6 prover finds
`parabolic_decompose` intractable in one round, it can be deferred — the
prover should:

1. State the theorem with `sorry`.
2. Add a comment explaining the gap.
3. Move on. The Round 7 prover will then have to either prove
   `parabolic_decompose` itself (in `Slice.lean`, additively) or work
   around it for `residual_levi_extract` only.

The proof outline (for reference):

- **Step A (`g₀` extraction):** `p` preserves `flagE` and `flagEV0`. So
  `p` descends to `S.V / flagE` (which has `V0` as a quotient piece), and
  the action on `S.V0 ≃ flagEV0 / flagE` is some `g₀ : V0 ≃ V0`. The
  isometry conjunct of `IsParabolicElement` forces `g₀` to preserve
  `formV0`.
- **Step B (`(d⁻¹)^∨` extraction):** the action on `flagE = S.E` is
  some `δ : E ≃ E`. The isometry of `S.ambientForm` plus the Levi block
  formula forces `δ = (d⁻¹)^∨` for some `d : E' ≃ E'` (recovering `d`
  from `δ` via `lambdaDualE`'s injectivity).
- **Step C (residual `D`):** Set `m := leviGL_E d ∘ leviGL_V0 g`. Then
  `p ∘ m⁻¹` is in the unipotent radical (it acts trivially on the graded
  pieces). By `parametrizeX0PlusU_uniqueness` + the `uD` parametrisation,
  there exists a unique `D` with `p ∘ m⁻¹ = uD D`. Hence
  `p = uD D ∘ m`.

## Acceptance criteria for Round 6

- `lake env lean InducedOrbitToy/Slice.lean` compiles. New `sorry`s are
  acceptable on:
  - `parabolic_decompose` (if deferred — see above).
  - Any helper that the prover decides isn't load-bearing. The prover
    should annotate each remaining `sorry` with a one-line explanation.
- `lake build` is green. The 4 NormalForm/Orbits sorries from end of
  Round 5 must remain unchanged (do not edit those files).
- `#print axioms` on every newly-added theorem with a complete proof
  shows only `[propext, Classical.choice, Quot.sound]`.
- All existing `Slice.lean` declarations are byte-for-byte unchanged
  except for the additive append.

## Side notes

- The "(`g` commutes with `X0`)" hypothesis on `leviGL_V0_conj_XCB` may
  not be needed for Round 7's actual use of the lemma. If the prover
  finds it cleaner to state `leviGL_V0_conj_XCB` only for `g = id`
  (i.e. just `XCB(C, B) = XCB(C, B)`, trivially true), do that — Round 7
  will pick whichever specialisation it needs.
- `parabolic_decompose` may benefit from being stated with explicit
  `IsUnit (leviGL_E d)` plus `IsUnit (leviGL_V0 g hg)` witnesses bundled
  in. Use whichever shape is most ergonomic.
- For `leviGL_V0`, the definition does NOT depend on `hg` (the
  block-diagonal map is well-defined for any `g`). Only the *parabolicity*
  proof needs `hg`. So `leviGL_V0` is a function of `g` alone, and `hg`
  is a separate hypothesis at consumer sites. (This avoids the
  `Subtype` anti-pattern flagged in session 7's review.)
