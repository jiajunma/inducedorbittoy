# InducedOrbitToy/Slice.lean

## Round 2 (prover) — partial-progress refinement

**File assigned despite PROGRESS.md flagging as "do not retry until upstream
fix lands."** PROGRESS.md (Round 2 plan) lists the two remaining
`Slice.lean` sorries as Tier D (autoformalization statement bugs):

- `parametrizeX0PlusU_existence` (line 232) — `Basic.lean :: UnipotentRadical`
  is too loose; doesn't enforce skew-adjointness w.r.t. `S.ambientForm`.
- `uD_isParabolic` (line 391 / now 442) — `IsAdjointPair B B (uD D) (uD D)`
  asks for self-adjointness of `uD`, but `uD` is an *isometry* (the
  blueprint claim is `IsAdjointPair B B (uD D) (uD (-D))`).

Both statements are **mathematically false as autoformalized**, so closing
them outright is impossible. This round therefore refines the existing
scoped sorries to expose the precise obstructions and discharge every
sub-goal that *is* provable from the current data.

### Result

- File compiles in isolation
  (`lake env lean InducedOrbitToy/Slice.lean` — only the two documented
  `sorry` warnings, no errors).
- `lake build` for `InducedOrbitToy.Slice` is green (only `sorry`
  warnings). NormalForm.lean has a separate build error introduced by
  another agent's helper (`IsUnit.of_mul_eq_one _ _ h1` arity bug at
  line 151) — outside the scope of this prover.
- No `axiom` declarations introduced (`#print axioms` for
  `uD_conj_XCB` shows only `propext`, `Classical.choice`, `Quot.sound`;
  `parametrizeX0PlusU_existence` and `uD_isParabolic` additionally use
  `sorryAx`, as expected).
- All previously sorry-free declarations remain untouched.

## `parametrizeX0PlusU_existence` (line 232)

### Mathematical assessment (re-verified this round)

The hypothesis `_hY : Y ∈ UnipotentRadical S` unfolds to:

1. Y vanishes on `flagE` (i.e. on `(e, 0, 0)`),
2. Y maps `flagEV0` into `flagE` (i.e. `Y(e, v, 0) = (·, 0, 0)`),
3. Y maps all of `V` into `flagEV0` (i.e. the E'-component of `Y x` is 0).

So `Y(e, v, e') = (α₁(v) + β(e'), γ(e'), 0)` for some block components
`α₁ : V₀ →ₗ E`, `β : E' →ₗ E`, `γ : E' →ₗ V₀`. The required factorisation
`Y = XCB S C B - X0Lift S` forces `C = γ`, `B = β`, **and**
`α₁ = Cdual S γ`. The latter identity follows iff `Y` is skew-adjoint
w.r.t. `S.ambientForm`, which `UnipotentRadical S` does **not** enforce.

Similarly, `IsSkewB B = β` reduces to the `(E', E')`-block of the
skew-adjointness identity for `Y`, again unprovable from the loose
`UnipotentRadical`.

### Refinement applied this round

Replaced the bare scoped sorries with a structured proof that closes the
two provable Prod-component subgoals (V₀ and E'), exposing only the
genuinely false E-component as `sorry`. The first conjunct (`IsSkewB B`)
is also opened up by `intro u v` plus a `show` for the unfolded goal,
making the precise obligation visible to the next agent.

```lean
refine ⟨projV0 ∘ₗ Y ∘ₗ inE', projE ∘ₗ Y ∘ₗ inE', ?_, ?_⟩
· -- IsSkewB B (Tier D blocker)
  intro u v
  show S.lambda ((projE ∘ₗ Y ∘ₗ inE') u) v
      + S.eps * S.lambda ((projE ∘ₗ Y ∘ₗ inE') v) u = 0
  sorry
· -- The equality `XCB S C B - X0Lift S = Y`.
  apply LinearMap.ext
  rintro ⟨e, v, e'⟩
  obtain ⟨hflagE, hflagEV0, hAll⟩ := _hY
  -- Y vanishes on flagE; decompose the input.
  have hY_e0 : Y (e, 0, 0) = 0 := …
  have hsum  : ((e, v, e') : S.V) = (e, 0, 0) + (0, v, 0) + (0, 0, e') := …
  have hY_sum : Y (e, v, e') = Y (0, v, 0) + Y (0, 0, e') := …
  -- Y (0, v, 0) ∈ flagE so its V₀ and E' components vanish.
  have hY_v_V0_eq : (Y (0, v, 0)).2.1 = 0 := …
  have hY_v_E'_eq : (Y (0, v, 0)).2.2 = 0 := …
  -- Y (0, 0, e') ∈ flagEV0 so its E' component vanishes.
  have hY_e'_E'_eq : (Y (0, 0, e')).2.2 = 0 := …
  rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply, hY_sum]
  refine Prod.mk.injEq .. |>.mpr
    ⟨?_, Prod.mk.injEq .. |>.mpr ⟨?_, ?_⟩⟩
  · -- E component (Tier D blocker — needs `α₁ = Cdual S γ`).
    sorry
  · -- V₀ component: closes via `simp [projV0, inE']`.
    simp only [hY_v_V0_eq, zero_add]
    simp [projV0, inE', LinearMap.comp_apply]
  · -- E' component: closes via `simp [hY_v_E'_eq, hY_e'_E'_eq]`.
    simp [hY_v_E'_eq, hY_e'_E'_eq]
```

### Reusable structural facts proved inside this proof

These are now visible in the proof body and could be hoisted to private
helpers if the plan agent wants to reuse them in `pNormalForm` or
`Orbits.lean`:

- `Y ∈ UnipotentRadical S → Y (e, 0, 0) = 0`.
- `Y ∈ UnipotentRadical S → (Y (0, v, 0)).2.1 = 0` and `(Y (0, v, 0)).2.2 = 0`.
- `Y ∈ UnipotentRadical S → (Y (0, 0, e')).2.2 = 0`.
- `(0, 0, e') = inE' e'` definitionally (used in the `simp [projV0, inE']`
  step).

### What still requires upstream fix

To close the two remaining sorries, **`Basic.lean :: UnipotentRadical`
must be tightened** to a Lie subalgebra that *also* preserves
`S.ambientForm`. With that, the E-component identity
`Cdual S C v = (Y (0, v, 0)).1` and the IsSkewB obligation both become
provable by direct expansion of the skew-adjointness condition.

## `uD_isParabolic` (now line 442)

### Mathematical assessment (re-verified this round)

Pick `x = (0, v, 0)` and `y = (0, 0, e₁')`. Then:

- `uD D x = (Cdual D v, v, 0)`,
- `uD D y = (½ Cdual D (D e₁'), D e₁', e₁')`,
- `S.ambientForm (uD D x, y) = λ(Cdual D v, e₁')
       = -B₀(v, D e₁')` (by `Cdual_pairing_eq`),
- `S.ambientForm (x, uD D y) = B₀(v, D e₁')`.

Difference: `-2 · B₀(v, D e₁')`, non-zero in general. So the
`IsAdjointPair S.ambientForm S.ambientForm (uD D) (uD D)` conjunct is
**genuinely false** — it asserts self-adjointness but `uD` is an
isometry. The blueprint statement should read

```
LinearMap.IsAdjointPair S.ambientForm S.ambientForm (uD S D) (uD S (-D))
```

(equivalent to `B (uD D x, uD D y) = B (x, y)`).

### Refinement applied this round

Replaced the bare sorry with `intro x y` plus a docstring-level comment
giving the explicit witness for falsity, so the next agent can pick up
the precise obstruction.

```lean
· -- IsAdjointPair conjunct (Tier D — autoformalisation statement bug):
  -- For x = (0, v, 0), y = (0, 0, e₁'), the obstruction evaluates to
  -- −2 · S.formV0 v (D e₁'), which is non-zero in general. Replace the
  -- statement with `IsAdjointPair S.ambientForm S.ambientForm (uD D) (uD (-D))`.
  intro x y
  sorry
```

### What still requires upstream fix

The plan agent must rewrite the autoformalised statement to
`IsAdjointPair … (uD D) (uD (-D))` (matching the blueprint isometry
claim). Once that lands, the proof should be a direct expansion using
`Cdual_pairing_eq`, `S.epsSymm`, `eps_sq_eq_one`, and `S.skew` — exactly
the toolkit already used in `uD_conj_XCB` (which is sorry-free).

## Files touched

Only `InducedOrbitToy/Slice.lean`. No other `.lean` file modified.

## Diagnostic (final)

```
$ lake env lean InducedOrbitToy/Slice.lean
warning: InducedOrbitToy/Slice.lean:232:8: declaration uses `sorry`
warning: InducedOrbitToy/Slice.lean:442:8: declaration uses `sorry`
```

```
$ lake build  # for InducedOrbitToy.Slice
⚠ Built InducedOrbitToy.Slice (13s)
warning: InducedOrbitToy/Slice.lean:232:8: declaration uses `sorry`
warning: InducedOrbitToy/Slice.lean:442:8: declaration uses `sorry`
```

(Aggregate `lake build` currently fails on `NormalForm.lean` due to a
separate prover's helper-lemma arity bug at line 151 —
`IsUnit.of_mul_eq_one _ _ h1` — which is outside the scope of this
prover. Reported here for visibility only; do not edit `NormalForm.lean`.)

## Summary

| Sorry | Status before | Status after |
|---|---|---|
| `parametrizeX0PlusU_existence` IsSkewB B | bare scoped sorry, comment | structured: `intro u v; show …; sorry` exposing the unfolded goal |
| `parametrizeX0PlusU_existence` equality | bare scoped sorry, comment | structured: 2 of 3 Prod components closed (V₀ ✓, E' ✓); only E component sorry, with explicit obstruction stated |
| `uD_isParabolic` IsAdjointPair | bare scoped sorry, comment | structured: `intro x y; sorry` with explicit (x, y) falsity witness in the comment |

Net work: **0 sorries closed** (all three are genuinely false as stated;
upstream statement / data refactor required), **3 sub-obligations
discharged** (V₀ component, E' component of the equality; goal exposed
on the IsSkewB side), **0 axioms introduced**. The remaining sorries are
now narrowly scoped on the precise impossible obligation, with explicit
mathematical witnesses for the obstruction inline.

## Next steps (for plan agent)

1. **Tighten `UnipotentRadical`** in `Basic.lean` to additionally enforce
   `IsSkewAdjoint S.ambientForm Y`. Once landed, the IsSkewB sorry and
   E-component sorry of `parametrizeX0PlusU_existence` should both close
   by a direct expansion of `Cdual_pairing_eq` plus the new hypothesis.
2. **Rewrite the `uD_isParabolic` statement** to use
   `IsAdjointPair … (uD D) (uD (-D))` instead of `(uD D) (uD D)`. Then
   the remaining sorry closes by the same expansion already used in
   `uD_conj_XCB`.
3. The structural facts about `Y ∈ UnipotentRadical S`
   (vanishing on flagE, V₀ component vanishing on `(0, v, 0)`, E'
   component always vanishing) are now inline in the proof body — if
   reused elsewhere, hoist them to a `private lemma Y_block_structure`
   alongside the other helpers.
