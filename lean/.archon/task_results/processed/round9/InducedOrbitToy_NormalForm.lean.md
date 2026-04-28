# InducedOrbitToy/NormalForm.lean — Round 9 Prover Report

## Round 9 status: PARTIAL — signature cascade landed, dim chain proved

`lake env lean InducedOrbitToy/NormalForm.lean` compiles with **one
declaration-use `sorry` warning** at line 197
(`pNormalForm_witnesses_aux`), unchanged from Round 8 in count, but
the body is now **structurally decomposed** into:

- Step 0 (sorry-free): `Sₕ : L1' ≃ Vplus` constructed via
  `LinearEquiv.ofFinrankEq`.
- Step 0.5 (sorry-free): full **dimension chain** for the d-construction
  (Cbar surjectivity, dim ker Cbar, dim L0', `dim L0' = dim ker Cbar`).
- Step 0.75 (sorry-free): `gL0 : L0' ≃ ker(Cbar S C)` and `K'`
  complement of `ker(Cbar)` are extracted.
- Step 1 (sorry): existential statement of the d-construction (alignment
  property), now reduced to assembling the iso and verifying alignment.
- Step 2 (sorry): D-lift through X0.
- Step 3 (sorry): T-construction + skewness + conjugation.
- Final assembly (sorry-free): glues everything via `exact ⟨...⟩`.

`lake build` is **green** at end of round (only declaration-use sorry
warnings + the pre-existing `unused variable hlambda` lint at
`X0Geometry.lean:221`).

## Signature change cascade (landed)

The `_hL1' : Module.finrank F S.L1' = c S.toX0Setup` hypothesis was
threaded through the witness chain:

- `pNormalForm_witnesses_aux` (line 197) — added `_hL1'` after `_hRank`.
- `pNormalForm_witnesses` (line 264) — added `_hL1'`; body forwards it
  to `_aux`.
- `pNormalForm` (line 306, public) — added `_hL1'`; body forwards it
  to `pNormalForm_witnesses`.

`pNormalForm_residual_orbit_iso` is **untouched** (it consumes the
independent `residual_levi_*` helpers, not `pNormalForm`); zero impact
on Orbits.lean. Verified by `grep`: `pNormalForm` (the public theorem)
has zero in-project consumers.

## Body decomposition of `pNormalForm_witnesses_aux`

The single body sorry at the original line 211 was replaced by a
structured proof (lines 208–~308) with three remaining sorrys (Steps
1, 2, 3) and significant **sorry-free preparation** for Step 1.

### Step 0 — Sₕ : L1' ≃ Vplus (closed, sorry-free)

```lean
have hVplus_eq : Module.finrank F S.L1' = Module.finrank F S.Vplus := by
  rw [_hL1']; exact (finrank_Vplus_eq_c S.toX0Setup).symm
let Sₕ : S.L1' ≃ₗ[F] S.Vplus :=
  LinearEquiv.ofFinrankEq S.L1' S.Vplus hVplus_eq
```

### Step 0.5 — Dimension chain (closed, sorry-free)

The full Round-10 prerequisite dim chain is proved:

```lean
-- Cbar S C is surjective.
have h_Cbar_surj : Function.Surjective (Cbar S C) := by
  have hcodim : Module.finrank F (S.V0 ⧸ LinearMap.range S.X0) = c S.toX0Setup :=
    (c_eq_finrank_quotient S.toX0Setup).symm
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [_hRank, hcodim]

-- dim ker (Cbar S C) = dim E' - c.
have h_dim_ker_Cbar :
    Module.finrank F (LinearMap.ker (Cbar S C))
      = Module.finrank F S.paired.E' - c S.toX0Setup := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (Cbar S C)
  rw [_hRank] at hrank
  change c S.toX0Setup + _ = Module.finrank F S.paired.E' at hrank
  omega

-- dim L0' = dim E' - c via IsCompl L1' L0' + _hL1'.
have h_dim_L0' :
    Module.finrank F S.L0' = Module.finrank F S.paired.E' - c S.toX0Setup := by
  have hcompl := S.isComplL'
  have hsum : Module.finrank F S.L1' + Module.finrank F S.L0'
      = Module.finrank F S.paired.E' := by
    rw [← Submodule.finrank_sup_add_finrank_inf_eq S.L1' S.L0',
        hcompl.codisjoint.eq_top, hcompl.disjoint.eq_bot,
        finrank_top, finrank_bot, add_zero]
  omega

-- The key dimension equality.
have h_dim_match :
    Module.finrank F S.L0' = Module.finrank F (LinearMap.ker (Cbar S C)) := by
  rw [h_dim_L0', h_dim_ker_Cbar]
```

### Step 0.75 — Iso pickup + complement (closed, sorry-free)

```lean
let gL0 : S.L0' ≃ₗ[F] (LinearMap.ker (Cbar S C)) :=
  LinearEquiv.ofFinrankEq S.L0' (LinearMap.ker (Cbar S C)) h_dim_match

obtain ⟨K', hK'_compl⟩ :=
  Submodule.exists_isCompl (LinearMap.ker (Cbar S C))
```

### Step 1 (sorry, Round 10 candidate) — d-construction

What remains:
- Build `cbarK' : K' ≃ V0/range X0` (Cbar |_{K'} is bijective:
  injective from `IsCompl K' (ker Cbar)`, surjective from
  `h_Cbar_surj`).
- Compose `Sₕ ≪≫ VplusEquivQuotientRange ≪≫ cbarK'.symm` to get
  `f : L1' ≃ K'`.
- Bundle `(f, gL0) : (L1' × L0') ≃ (K' × ker(Cbar))` via
  `LinearEquiv.prodCongr`.
- Compose with `prodEquivOfIsCompl S.L1' S.L0' S.isComplL'` (forward)
  and `prodEquivOfIsCompl K' (ker Cbar) hK'_compl` (backward) to get
  `d.symm : E' ≃ E'`. Take `d := d.symm.symm`.
- Verify alignment: `Cbar (d.symm a' : E') = mkQ (Sₕ a' : V0)` for
  `a' ∈ L1'` (by definition of f and cbarK'), and
  `Cbar (d.symm b' : E') = 0` for `b' ∈ L0'` (since `gL0 b' ∈ ker Cbar`).

Estimated remaining effort: ~50 lines (down from ~80).

### Step 2 (sorry, Round 10 candidate) — D lift

Existential: `∃ (D : E' →ₗ V0), S.X0 ∘ₗ D = C ∘ₗ d.symm - CST Sₕ`.

Strategy: by Step 1, the difference `(C ∘ d.symm - CST Sₕ) e0` lies in
`range S.X0` for every `e0`. Lift via:
- Pick complement `K ⊕ ker X0 = V0` via `Submodule.exists_isCompl`.
- `X0 |_K : K ≃ range X0` via `LinearMap.linearEquivOfInjective`.
- Compose to get section `range X0 →ₗ V0`, post-compose with the
  difference.

Estimated effort: ~60 lines.

### Step 3 (sorry, Round 10 candidate) — T construction

Existential: `∃ (T : L0' →ₗ L0), IsSkewT S T ∧ <conjugation>`.

Strategy: after `leviGL_E_conj_XCB` and `uD_conj_XCB`, the conjugated
operator equals `XCB (CST Sₕ) B''` for an explicit `B''`. Choose
`D|_{L1'}` carefully (via `vplusKerPairing_isPerfPair`) so that
`B''(L1') ⊂ L1` and the skew condition forces `B''(L0') ⊂ L0`.

Estimated effort: ~120 lines.

### Final assembly (closed, sorry-free)

```lean
exact ⟨Sₕ, D, d, T, hTskew.1, hTskew.2⟩
```

## Compilation & Axioms

- `lake env lean InducedOrbitToy/NormalForm.lean` — compiles (1
  declaration-use `sorry` warning at line 197).
- `lake build` — green. Pre-existing warnings: `Slice.lean:1109`
  (parabolic_decompose, deferred), `Orbits.lean:512`
  (isParabolicElement_ringInverse_of_orbit_witness, secondary
  Round 9 target).
- `#print axioms`:
  - `pNormalForm` — `[propext, sorryAx, Classical.choice, Quot.sound]`
    (sorryAx via `pNormalForm_witnesses_aux`'s 3 sub-step sorrys).
  - `pNormalForm_residual_orbit_iso` —
    `[propext, Classical.choice, Quot.sound]` (clean).
  - `kernelImage_ker` — `[propext, Classical.choice, Quot.sound]`
    (clean).
- No new custom `axiom` declarations.

## Acceptance criteria status (Round 9 PROGRESS.md §1)

- [x] `lake env lean InducedOrbitToy/NormalForm.lean` compiles.
- [partial] The `sorry` at body line 211 in `pNormalForm_witnesses_aux`
  is replaced. *Replaced by a structured proof with sorry-free
  preparation (Steps 0, 0.5, 0.75) and three focused sub-existential
  sorrys (Steps 1, 2, 3). Per PROGRESS.md: "Acceptable to introduce
  sorry'd sub-step helpers (`_step1` through `_step4`) if a step is
  intractable; document each surviving sorry with a Gap comment." ✓
  matches this fallback.*
- [x] New hypothesis `(_hL1' : Module.finrank F S.L1' = c S.toX0Setup)`
  threaded through `pNormalForm_witnesses_aux`,
  `pNormalForm_witnesses`, and `pNormalForm`.
- [x] `lake build` is green at end of round.
- [partial] `#print axioms pNormalForm` shows only
  `[propext, Classical.choice, Quot.sound]`. *Not yet — sorryAx
  remains via Steps 1, 2, 3 in the helper body. Will clear in Round 10
  if those three steps close.*
- [pending] Stale comment hygiene at lines 344, 357.
  *Not addressed this round; leave for polish stage.*

## Strategy notes for Round 10

The three remaining sorrys (Step 1, Step 2, Step 3) are now in clean,
self-contained existential form. **Significant Round-10 prep work
landed in Round 9**: the dim chain is fully proved, `gL0` and `K'`
are extracted as named values. The Round-10 prover starts from a
solid foundation.

1. **Step 1 (~50 lines remaining)** — the iso assembly.
   Required Mathlib API (all stable):
   - `LinearEquiv.ofBijective` for `cbarK'`.
   - `LinearEquiv.prodCongr` for the block-diagonal map.
   - `Submodule.prodEquivOfIsCompl` for the L1'⊕L0' ≃ K'⊕ker transport.
   - `VplusEquivQuotientRange` (X0Geometry, project-internal) for the
     `Vplus ≃ V0/range X0` step.

2. **Step 2 (~60 lines)** — D-lift. Independent of Step 1's iso
   internals (only uses the alignment property delivered as `hd_L1'`,
   `hd_L0'`).

3. **Step 3 (~120 lines)** — T-construction + skewness + conjugation.
   Independent of Steps 1, 2 internals (only uses the existence of
   `Sₕ`, `d`, `D` and their declared properties).

If Steps 1, 2, 3 all close in Round 10, `pNormalForm` becomes
`[propext, Classical.choice, Quot.sound]`-clean and the project
advances `prover` → `polish`.

## Files touched (Round 9)

- `InducedOrbitToy/NormalForm.lean`:
  - `pNormalForm_witnesses_aux` (line 197) — added `_hL1'`
    hypothesis; body restructured into Steps 0, 0.5, 0.75, 1, 2, 3.
    Steps 0, 0.5, 0.75 are sorry-free; Steps 1, 2, 3 each carry one
    focused sub-existential sorry with Gap comments.
  - `pNormalForm_witnesses` (line 264) — added `_hL1'`; body
    forwards it to `_aux`.
  - `pNormalForm` (line 306) — added `_hL1'`; body forwards it to
    `pNormalForm_witnesses`.

No other files touched.

## Mathlib lemmas used (newly introduced)

- `LinearEquiv.ofFinrankEq` — pickup of arbitrary iso between
  finite-dim spaces of equal dimension. Used in Step 0 and Step 0.75.
- `LinearMap.range_eq_top.mp` + `Submodule.eq_top_of_finrank_eq` —
  for `h_Cbar_surj`. Established surjectivity from dim equality.
- `LinearMap.finrank_range_add_finrank_ker` — rank-nullity for
  `h_dim_ker_Cbar`.
- `Submodule.finrank_sup_add_finrank_inf_eq` — for `h_dim_L0'`,
  combined with `IsCompl.codisjoint.eq_top` + `IsCompl.disjoint.eq_bot`.
- `Submodule.exists_isCompl` — for picking `K'`.

## Mathlib lemmas needed for Round 10 (Step 1)

- `LinearEquiv.ofBijective` — `cbarK' : K' ≃ V0/range X0`.
- `LinearEquiv.prodCongr` — block-diagonal product map.
- `Submodule.prodEquivOfIsCompl` — `L1'⊕L0' ≃ E'` and `K'⊕ker(Cbar) ≃ E'`.
- `VplusEquivQuotientRange` (X0Geometry) — `Vplus ≃ V0/range X0`.

## Recommendation for plan agent

Round 9 delivered the signature change + decomposition + dim chain.
Round 10 picks up the iso-construction work (Step 1), then Steps 2
and 3. The estimated total remaining effort is ~230 lines, down from
the original ~300-line estimate after Round 9's preparation.

Splitting Round 10 across two prover sessions (Step 1 alone first,
then Steps 2, 3) may be advisable, since Step 1 is a self-contained
algebraic construction that doesn't need C, B, or _hB.
