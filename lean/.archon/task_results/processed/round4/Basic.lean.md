# InducedOrbitToy/Basic.lean

Round 4, Tier S #2 + Tier S #3 — both structural fixes applied as the
plan-agent specified. Basic.lean compiles in isolation with zero
diagnostics; no new axioms.

## Summary of changes

1. **`SliceSetup` (Tier S #3, line 131–142)** — replaced the single
   `L0_isotropic : IsIsotropic paired.pairing L0 L0'` field with the
   Lagrangian quartet:
   - `L0_paired : IsPaired paired.pairing L0 L0'`
   - `L1_isotropic_L0' : IsIsotropic paired.pairing L1 L0'`
   - `L0_isotropic_L1' : IsIsotropic paired.pairing L0 L1'`

   Plus the existing `L1_paired`. Docstring rewritten to describe the
   Lagrangian decomposition.

   **Audit**: `grep -rn L0_isotropic InducedOrbitToy/` showed only two
   *comment* references in `NormalForm.lean` (lines 344, 357) — no code
   uses the field. Safe to remove.

2. **`UnipotentRadical` (Tier S #2, line 216–264)** — added the 4th
   conjunct `IsSkewAdjoint S.ambientForm f` to the carrier predicate.
   Docstring rewritten ("`𝔲 = 𝔭 ∩ 𝔤`" framing). Closure proofs updated:

   - `zero_mem'` — now a 4-tuple; new conjunct discharged by
     `intro x y; simp [LinearMap.zero_apply, map_zero]`.
   - `add_mem'` — destructures `⟨h1, h2, h3, h4⟩` (and similarly for
     `g`); new conjunct discharged by:
     ```lean
     intro x y
     have hf := h4 x y
     have hg := h4' x y
     simp only [LinearMap.add_apply, map_add, LinearMap.add_apply]
     linear_combination hf + hg
     ```
   - `smul_mem'` — same shape; new conjunct discharged by:
     ```lean
     intro x y
     have hf := h4 x y
     simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
       smul_eq_mul]
     linear_combination c * hf
     ```

## Acceptance criteria checklist

- [x] `Basic.lean` compiles in isolation — verified via
  `lean_diagnostic_messages`, no errors/warnings.
- [x] `UnipotentRadical` has 4 conjuncts in the order the plan-agent
  specified: vanish-on-flagE, send-flagEV0-to-flagE, send-V-to-flagEV0,
  IsSkewAdjoint ambientForm.
- [x] `SliceSetup` has the 4 Lagrangian fields (`L1_paired`,
  `L0_paired`, `L1_isotropic_L0'`, `L0_isotropic_L1'`) — old
  `L0_isotropic` removed since unused in code.
- [x] No new `axiom`s — `lean_verify
  InducedOrbitToy.c_eq_finrank_quotient` returns
  `{"axioms":["propext","Classical.choice","Quot.sound"]}`.
- [x] `c_eq_finrank_quotient` (the only theorem) is unchanged and
  still compiles.

## Notable proof attempts and dead ends

### Attempt 1 (failed) — `linarith` for the IsSkewAdjoint closure

Initial attempt used `linarith` to close
`(B (f x)) y + (B (g x)) y + ((B x) (f y) + (B x) (g y)) = 0` from
`hf : (B (f x)) y + (B x) (f y) = 0` and
`hg : (B (g x)) y + (B x) (g y) = 0`.

**Result:** FAILED — `linarith` requires an ordered field; `F` here is
just a generic field. **Dead end:** do not use `linarith` over generic
`F : Type*` with `[Field F]`.

**Fix:** `linear_combination hf + hg` (and `linear_combination c * hf`
for the smul case). This is the canonical Mathlib idiom for closing
linear-equality goals over rings/fields.

### Lemmas actually used

- `LinearMap.zero_apply`, `LinearMap.add_apply`, `LinearMap.smul_apply`
- `map_zero`, `map_add`, `map_smul`
- `smul_eq_mul`
- `linear_combination` tactic

## Cross-file cascade (heads-up for sister provers)

Both Tier S #2 (UnipotentRadical) and Tier S #3 (SliceSetup) cascade:

- **`Slice.lean :: parametrizeX0PlusU_existence`** — its
  `_hY : Y ∈ UnipotentRadical S` destructure now needs to be
  `⟨hflagE, hflagEV0, hAll, hSkewY⟩` (4-tuple). The new `hSkewY` is
  what discharges the IsSkewB and E-component sorries.
- **`Orbits.lean :: XCB_sub_X0Lift_mem_unipotent` /
  `XST_sub_X0Lift_mem_unipotent`** — `refine ⟨…, ?_⟩` blocks now need
  a 4th branch proving `IsSkewAdjoint S.ambientForm (XCB C B - X0Lift S)`.
  The plan-agent's recommended Option A (add `(hskew : ...)` hypothesis
  to the helper) keeps the structure clean.
- **`NormalForm.lean`** — the comment references at lines 344, 357 to
  `L0_isotropic` are now stale; they will need a comment refresh in a
  future round but do not break compilation (they're just comments).

Mid-round `lake build` breakage in Slice.lean and Orbits.lean is
expected until those provers land their cascades.

## Confirmation

- `lake env lean InducedOrbitToy/Basic.lean` (via LSP diagnostics):
  **green, no errors, no warnings**.
- `#print axioms InducedOrbitToy.c_eq_finrank_quotient`:
  `[propext, Classical.choice, Quot.sound]`.
- No axiom declarations introduced.
- `lake build` (full repo): **expected mid-round breakage in
  Slice.lean / Orbits.lean** until those provers land their cascades;
  Basic.lean itself is fine.
