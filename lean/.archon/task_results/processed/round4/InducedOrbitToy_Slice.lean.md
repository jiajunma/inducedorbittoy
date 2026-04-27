# InducedOrbitToy/Slice.lean — Round 4

## Summary

**Status: ALL OBJECTIVES MET.** Slice.lean is now sorry-free; only standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

- Closed both internal scoped sorries in `parametrizeX0PlusU_existence`
  (line 232 — Tier D, 2 internal sorries at the previous lines 256 and
  294).
- Cascaded the tightened (4-conjunct) `UnipotentRadical` from Basic.lean
  through `parametrizeX0PlusU_mem` (added the new IsSkewAdjoint conjunct
  to its proof).
- Added one private helper `XCB_sub_X0Lift_apply` (pointwise formula for
  the difference) — load-bearing for the new IsSkewAdjoint case in
  `parametrizeX0PlusU_mem` and useful for downstream consumers.

End-of-round `lake build` is **NOT yet green**: the only failures are in
`InducedOrbitToy/Orbits.lean` (sister prover's Round 4 objective —
`XCB_sub_X0Lift_mem_unipotent` at line ~189 still needs the 4th conjunct
discharged). NormalForm.lean continues to compile (modulo its 5 known
sorries — Round 5/6 work, untouched here).

## File compilation

`lake env lean InducedOrbitToy/Slice.lean` produces **no errors and no
warnings**. (Previously: 1 declaration-use `sorry` warning.)

## Theorem axiom hygiene (verified via `lean_verify`)

- `parametrizeX0PlusU_existence` → `[propext, Classical.choice, Quot.sound]`
- `parametrizeX0PlusU_mem` → `[propext, Classical.choice, Quot.sound]`

No new custom `axiom` declarations.

## Sorries closed

### `parametrizeX0PlusU_existence` (line 232) — Tier D / Tier S #2

Two internal scoped sorries closed:

- **IsSkewB B sorry (was line 256).** Specialise `hSkewY (0,0,u) (0,0,v)`
  (where `hSkewY` is the new 4th conjunct of `_hY`). Apply
  `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, map_zero,
   LinearMap.zero_apply, mul_zero, add_zero, zero_add]` to collapse all
  `B₀(_, 0)`, `B₀(0, _)`, `λ(_, 0)`, `λ(0, _)` terms. The remaining
  identity matches the goal definitionally via `(projE ∘ₗ Y ∘ₗ inE') u
  = (Y (0, 0, u)).1`, dispatched with a `show` + `exact h`.

- **E-component-of-equality sorry (was line 294).** New auxiliary
  hypothesis `hY_v_E_eq : (Y (0, v, 0)).1 = Cdual S (projV0 ∘ₗ Y ∘ₗ inE') v`
  proved by `S.paired.isPerfect.1` (left injectivity of the perfect
  pairing): pair both sides with each `e''`, use `Cdual_pairing_eq` on
  the RHS and `hSkewY (0, v, 0) (0, 0, e'')` (with the same simp set as
  above) on the LHS to reduce to the same `-S.formV0 v ((Y(0,0,e'')).2.1)`,
  closed by `linear_combination h`. Then the E-component goal reduces
  via `sub_zero` + `hB_eq : (projE ∘ₗ Y ∘ₗ inE') e' = (Y (0, 0, e')).1`
  + `← hY_v_E_eq`.

### `parametrizeX0PlusU_mem` (line 184) — Tier S #2 cascade

Pre-existing 3-conjunct refine extended to `refine ⟨?_, ?_, ?_, ?_⟩`,
adding the **IsSkewAdjoint S.ambientForm (XCB S C B - X0Lift S)** case:

1. Destructure `(e₁, v₁, e₁')` and `(e₂, v₂, e₂')`.
2. `rw [XCB_sub_X0Lift_apply, XCB_sub_X0Lift_apply]` (new helper).
3. `simp only` set: `SliceSetup.ambientForm`, `LinearMap.mk₂_apply`,
   `map_add`, `LinearMap.add_apply`, `map_zero`, `mul_zero`, `add_zero`,
   `zero_add`.
4. `rw [Cdual_pairing_eq …, Cdual_pairing_eq …]` on the two `λ(Cdual …)`
   atoms.
5. `linear_combination hskewB - S.eps * hSym - S.formV0 (C e₁') v₂ * hε2`
   where `hskewB := _hB e₁' e₂'`, `hSym := S.epsSymm v₂ (C e₁')`, and
   `hε2 := S.eps * S.eps = 1` from `S.epsValid`.

The `linear_combination` coefficients were derived from the textual
expansion: `λ(Be₁',e₂') + ε λ(Be₂',e₁') = 0` (skew-B), then absorb the
`B₀(Ce₁', v₂)` vs `ε² B₀(Ce₁', v₂)` discrepancy via `ε² = 1`.

## New helper added

```lean
/-- Pointwise formula for `XCB - X0Lift`: the V₀-part is just `C e'`. -/
private lemma XCB_sub_X0Lift_apply (S : SliceSetup F)
    (C : S.E' →ₗ[F] S.V0) (B : S.E' →ₗ[F] S.E)
    (e : S.paired.E) (v : S.V0) (e' : S.paired.E') :
    (XCB S C B - X0Lift S) (e, v, e')
      = (Cdual S C v + B e', C e', (0 : S.paired.E')) := by
  rw [LinearMap.sub_apply, XCB_apply, X0Lift_apply]
  ext <;> simp
```

## Statements changed

- **Docstring** of `parametrizeX0PlusU_existence` updated to remove the
  "loose UnipotentRadical" framing (no longer accurate after Tier S #2).
  The theorem signature is unchanged.
- **Body** of `parametrizeX0PlusU_existence` changed: `obtain` was 3-tuple,
  now 4-tuple `⟨hflagE, hflagEV0, hAll, hSkewY⟩ := _hY`; the obtain was
  also pulled to the top of the proof (before `refine`) so that
  `hSkewY` is in scope for the IsSkewB case.
- **Body** of `parametrizeX0PlusU_mem`: `refine ⟨?_, ?_, ?_⟩` →
  `refine ⟨?_, ?_, ?_, ?_⟩`; new IsSkewAdjoint case added.

No statement (theorem signature, definition body, or hypothesis list) of
any **other** declaration was touched. In particular, all of `Cdual`,
`Cdual_pairing_eq`, `XCB`, `XST`, `BST`, `CST`, `projL0'`, `projL1'`,
`uD`, `uD_isParabolic`, `uD_conj_XCB`, `Cdual_neg`, `Cdual_X0_apply`,
`Cdual_pairing`, `eps_sq_eq_one`, `lambda_isPerfPair`,
`uD_neg_inverse`, `uD_apply`, `XCB_apply`, `X0Lift_apply`,
`parametrizeX0PlusU_uniqueness` — **unchanged**.

## Mathlib lemmas used

- `LinearMap.sub_apply`, `LinearMap.add_apply`, `LinearMap.zero_apply`,
  `LinearMap.mk₂_apply`, `LinearMap.comp_apply`
- `map_zero`, `map_add` (linear-map versions)
- `Submodule.mem_bot`, `Submodule.zero_mem`
- `Prod.mk.injEq`
- `sub_zero`, `add_zero`, `zero_add`, `mul_zero`
- `linear_combination` tactic
- `S.paired.isPerfect.1` (left-injectivity component of `IsPerfectPairing`)

## Mid-round build state (cross-file, expected per PROGRESS.md)

- `InducedOrbitToy/Slice.lean`: ✅ green, 0 sorries, 0 warnings.
- `InducedOrbitToy/Basic.lean`: ✅ green (Tier S #2 + #3 landed).
- `InducedOrbitToy/X0Geometry.lean`: ✅ green (only the pre-existing
  unused-variable lint at 221:35).
- `InducedOrbitToy/LocalForms.lean`: ✅ green.
- `InducedOrbitToy/NormalForm.lean`: ✅ green (5 known sorries unchanged
  — Round 5/6 work).
- `InducedOrbitToy/Orbits.lean`: ❌ **expected** cascade error in
  `XCB_sub_X0Lift_mem_unipotent` (line ~189) — sister prover's Round 4
  objective. Plan agent will gate end-of-round build on that landing.

## Decision log

- **Why `linear_combination h` instead of `linarith` for the
  `(Y (0,v,0)).1 = Cdual …` step.** `linarith` works only on ordered
  fields; `F` is an arbitrary `Field` here. The closing identity
  `S.paired.pairing (Y(0,v,0)).1 e'' = -(S.formV0 v) (Y(0,0,e'')).2.1` is
  a pure linear-rearrangement consequence of `h`, so `linear_combination
  h` is the right tool.
- **Why the `obtain` was lifted to the top of the proof body.** The new
  `hSkewY` field of the 4-tuple destructure is needed in the IsSkewB
  conjunct (the *first* `?_` after `refine`). Lifting the destructure
  ahead of `refine` keeps the proof shape minimal and avoids duplicating
  the `obtain` in both sub-proofs.
- **Helper choice.** Placed `XCB_sub_X0Lift_apply` adjacent to the
  existing `XCB_apply` / `X0Lift_apply` helpers (lines 168–181 in the
  pre-edit file) for discoverability. It is `private` to match the
  convention of the existing `_apply` helpers.

## Next steps for plan agent

This file is **complete for Round 4**. Outstanding work in the project
is in:

- `Orbits.lean :: XCB_sub_X0Lift_mem_unipotent` /
  `XST_sub_X0Lift_mem_unipotent` (sister prover this round).
- Round 5+ tiers as enumerated in `task_pending.md`.
