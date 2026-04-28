# Prover Backlog

`lake build` is **NOT green** at end of Round 9 — `NormalForm.lean`
has compilation errors at lines 302–308 from the Round-9 prover's
unfinished `CbarK'_inj`/`CbarK'_surj` sub-construction.  Round 10
must fix the build first.

End-of-Round-9 sorry inventory (verified 2026-04-28 by plan agent):

| File | Line | Declaration | Round 10 priority |
|---|---|---|---|
| `InducedOrbitToy/NormalForm.lean` | 197 | `pNormalForm_witnesses_aux` | **Primary — also fix build** |
| `InducedOrbitToy/Orbits.lean` | 524 | `isParabolicElement_ringInverse_of_orbit_witness` (2 sorries) | **Secondary** |
| `InducedOrbitToy/Slice.lean` | 1109 | `parabolic_decompose` | Deferred (no consumers; Tier S #6) |

Specifically the `pNormalForm_witnesses_aux` body now contains 5
internal `sorry`s (lines 309, 310, 322, 339, 356), of which:
- Lines 309, 310 are spurious (in the broken Step 0.75 sub-construction
  that the Round-10 prover should either fix or replace).
- Lines 322, 339, 356 are the genuine Step 1 / Step 2 / Step 3
  existentials (the d / D / T constructions).

Public-theorem surface accounting (verified by plan agent end of
Round 9, modulo build-break):

- `pNormalForm_residual_orbit_iso`, `inducedOrbits`,
  `multiplicityNonDeg`, `multiplicityOddCase`,
  `multiplicityEvenSymmCase` — clean
  `[propext, Classical.choice, Quot.sound]`.
- `pNormalForm` — transitive `sorryAx` via `pNormalForm_witnesses_aux`.
- `sIndependenceAndOrbitCriterion`, `main` — transitive `sorryAx` via
  `isParabolicElement_ringInverse_of_orbit_witness`.

If Round 10 closes the NormalForm helper sorries (or drives them down
to a single Step 3 sorry) AND closes the Orbits flagE conjunct via
the option-(a) signature tightening, then 2 of the 3 remaining
helper sorries close.  The flagEV0 conjunct + `parabolic_decompose`
remain deferred to polish.

## Tier S — plan-agent statement / structural fixes

(Tier S #1 through #5 — all resolved in earlier rounds; see
`task_done.md`.  Round 7 landed the Levi-factor restructure of
`pNormalForm_witnesses`; Round 9 added the `_hL1'` cascade through
`pNormalForm_witnesses_aux` / `pNormalForm_witnesses` / `pNormalForm`.)

### Tier S #6 — `parabolic_decompose` signature change (deferred)

Round 8 Slice prover identified a genuine mathematical gap: the
unipotent factor in the blueprint's `p = u_D · m` decomposition
must include a residual skew `B' : E' →ₗ E` term, which the current
`uD D` definition zero-sets.  The blueprint's "u_D" notation is
imprecise; the project's `uD D` is a strict sub-family of the actual
unipotent group.

**Plan-agent decision deferred to polish stage.** Two options:

- **Option (a) — Generalise `uD`:** define a sister `uD' D B'`
  parametrised by both `D : E' →ₗ V0` and `B' : E' →ₗ E` with
  `IsSkewB B'`.  Restate `parabolic_decompose` to expose
  `(D, B', d, g)`.  Mathematically correct; ~150-line refactor.
- **Option (b) — Narrow the hypothesis:** add a hypothesis
  `parabolic_decompose : ... (hp_geom : <residual B' is zero>) → ...`
  capturing the implicit "geometric parabolic" assumption.  Less
  clean, but smaller diff.

Since `parabolic_decompose` has **zero consumers** in the project,
deferring is non-blocking for public-theorem closure.  Polish stage
should pick the option and execute.

### Tier S #7 — Orbits helper signature tightening (Round 10)

Round 9 Orbits prover identified that the helper
`isParabolicElement_ringInverse_of_orbit_witness` is mis-stated when
specialised to `IsSkewT` only (not `Tset_circ`).  The kernel-identification
sub-claim `ker XST T_i = flagE` is true in cases 1-2 (ε=-1, or ε=+1
with l even) but false in case 3 (ε=+1, l odd, where `dim ker T_i = 1`).

**Plan-agent decision (Round 10):** execute option (a) — tighten the
helper's signature to take `T_i ∈ S.Tset_circ`, then by-cases on
`¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))`:
- Easy cases (1, 2): derive `ker T_i = ⊥` from
  `MaximalRank = dim L0'` + rank-nullity from `Tset_circ`'s
  `finrank (range T_i) = MaximalRank`; apply
  `ker_XST_eq_flagE_of_injective` (already landed Round 9).
- Hard case 3: leave a focused `sorry` with documented gap.

Caller `sIndependenceAndOrbitCriterion` already has `T_i ∈ Tset_circ`
in scope (passed as `hT₁`, `hT₂`); the call site currently
extracts `.1` to get `IsSkewT`.  Drop the `.1` extraction.

flagEV0 conjunct: kernel argument doesn't apply; deferred to polish
once `parabolic_decompose` lands.

## Tier A — provable now (Round 10)

### `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses_aux`
### body — fix build + close Steps 1, 2, 3 (Round 10 primary)

**Round 9 inheritance (real progress):**

- Step 0 (sorry-free): `Sₕ : L1' ≃ Vplus` via `LinearEquiv.ofFinrankEq`.
- Step 0.5 (sorry-free): full dimension chain
  (`h_Cbar_surj`, `h_dim_ker_Cbar`, `h_dim_L0'`, `h_dim_match`).
- Step 0.75 (partial-broken):
  - `gL0 : L0' ≃ ker(Cbar)` via `LinearEquiv.ofFinrankEq` (sorry-free).
  - `K' ⊕ ker(Cbar)` complement extracted (sorry-free).
  - **CbarK'_inj/CbarK'_surj attempt at lines 277–310 has 2 bugs**
    (variable-swap + `linarith` over a non-ordered field).  Round 10
    must either fix or replace this sub-construction.

**Round 10 strategy — recommended approach:**

1. **Fix the build first.** Two options:

   - **Option Fix:** swap variable names at line 300 — replace
     ```lean
     obtain ⟨k, hk_K', n, hn_ker, hsum⟩ := hz_top
     ```
     with
     ```lean
     obtain ⟨k, hk_ker, n, hn_K', hsum⟩ := hz_top
     ```
     (since `hK'_compl : IsCompl (ker (Cbar S C)) K'`, the destructure
     yields `k ∈ ker(Cbar)`, `n ∈ K'`, `k + n = z`).  Update lines
     302–305 accordingly.  Replace the `linarith [hsum]` at line 308
     with `linear_combination hsum` (or
     `eq_sub_of_add_eq hsum.symm`).  Then close lines 309, 310 with
     standard `LinearMap` arithmetic (`map_sub` + `hCbar_n` + `hz`).

   - **Option Replace (preferred):** remove the inline
     `CbarK'_inj`/`CbarK'_surj` block and instead use
     `LinearEquiv.ofBijective` on `CbarK'_lin` directly, with the
     bijectivity proof packaged via dim equality:
     ```lean
     have h_dim_K'_eq_quot :
         Module.finrank F K'
           = Module.finrank F (S.V0 ⧸ LinearMap.range S.X0) := by
       -- finrank K' + finrank ker(Cbar) = finrank E' (from hK'_compl)
       -- finrank ker(Cbar) = finrank E' - c (h_dim_ker_Cbar)
       -- finrank V0/range X0 = c (c_eq_finrank_quotient)
       sorry  -- short omega chain
     let cbarK' : K' ≃ₗ[F] (S.V0 ⧸ LinearMap.range S.X0) :=
       LinearEquiv.ofFinrankEq K' (S.V0 ⧸ LinearMap.range S.X0)
         h_dim_K'_eq_quot
     ```
     This is cleaner and avoids the buggy injectivity/surjectivity
     proofs altogether.  However, it loses the explicit
     `cbarK'.toLinearMap = (Cbar S C) ∘ K'.subtype` identity needed
     for Step 1's alignment property — so the alignment has to be
     proven later via a separate `cbarK'_apply`-style lemma using
     `bijective_iff_finrank_eq` chain or a custom equiv.

   **Plan-agent recommendation: Option Fix.** Smaller diff, preserves
   the explicit `CbarK'_lin = (Cbar S C) ∘ K'.subtype` identity that
   Step 1's alignment property will need.

2. **Close Step 1 (~80 lines, line 314).** After Step 0.75 lands
   sorry-free, build:
   - `cbarK' : K' ≃ V0/range X0` via `LinearEquiv.ofBijective` from
     `CbarK'_inj` + `CbarK'_surj`.
   - `f : L1' ≃ K'` via composition
     `Sₕ ≪≫ VplusEquivQuotientRange ≪≫ cbarK'.symm`.
     (`VplusEquivQuotientRange` is from `X0Geometry.lean`.)
   - `(f, gL0) : (L1' × L0') ≃ (K' × ker(Cbar))` via
     `LinearEquiv.prodCongr`.
   - `prodEq_L : (L1' × L0') ≃ E'` via
     `Submodule.prodEquivOfIsCompl S.L1' S.L0' S.isComplL'`.
   - `prodEq_K : (K' × ker(Cbar)) ≃ E'` via
     `Submodule.prodEquivOfIsCompl K' (LinearMap.ker (Cbar S C)) hK'_compl.symm`.
     (Note `.symm` to get the order right.)
   - `d.symm := prodEq_L.symm ≪≫ (f.prodCongr gL0) ≪≫ prodEq_K`.
   - `d := d.symm.symm`.
   - Verify `hd_L1'`: for `a' ∈ L1'`, `Cbar(d.symm a') = mkQ(Sₕ a')`.
     - Unfold via `prodEquivOfIsCompl` → `(a', 0) ∈ L1' × L0'` →
       `(f a', 0) ∈ K' × ker(Cbar)` → `f a' ∈ E'`.
     - Apply `Cbar`: `Cbar(f a') = cbarK' (f a')` (since `f a' ∈ K'`)
       `= (cbarK' ∘ f) a' = (cbarK' ∘ cbarK'.symm ∘ VplusEquivQuotientRange ∘ Sₕ) a' = mkQ(Sₕ a')`.
   - Verify `hd_L0'`: for `b' ∈ L0'`, `Cbar(d.symm b') = 0`.
     - Symmetric: `(0, b') ∈ L1' × L0'` → `(0, gL0 b') ∈ K' × ker(Cbar)`
       → `gL0 b' ∈ ker(Cbar)`.  `Cbar (gL0 b' : E') = 0` by definition.

   Estimated effort: ~80 lines.  Round-9 prover's "Strategy notes for
   Round 10" in
   `.archon/task_results/processed/round9/InducedOrbitToy_NormalForm.lean.md`
   has the same plan.

3. **Close Step 2 (~60 lines, line 335).** Build
   `D : E' →ₗ V0` with `S.X0 ∘ₗ D = C ∘ₗ d.symm - CST Sₕ`:
   - The difference `(C ∘ d.symm - CST Sₕ) e0` lies in `range S.X0`
     for every `e0`:
     - On `L1'`: `Cbar(C ∘ d.symm) = mkQ ∘ Sₕ` (`hd_L1'`).
       `CST Sₕ` lands in `Vplus.subtype ∘ Sₕ ∘ projL1'`.  After
       quotienting, both sides equal `mkQ(Sₕ ·)` ⇒ difference's
       `mkQ` is 0 ⇒ difference lies in `range X0`.
     - On `L0'`: `Cbar(C ∘ d.symm) = 0` (`hd_L0'`); `CST Sₕ` is 0
       on `L0'` (since `projL1' ∘ L0'.subtype = 0`).  So both sides
       are 0 in `V0` mod `range X0`, meaning the LHS is in `range X0`
       and the RHS is 0.
   - Pick complement `K ⊕ ker X0 = V0` via
     `Submodule.exists_isCompl`.
   - `X0|_K : K ≃ range X0` via `LinearMap.linearEquivOfInjective`
     (X0 restricted to its complement is injective on K).
   - Compose `(C ∘ d.symm - CST Sₕ) : E' →ₗ range X0` (range
     coercion!) with `(X0|_K).symm : range X0 →ₗ K` and
     `K.subtype : K →ₗ V0` to get `D : E' →ₗ V0`.
   - Verify `S.X0 ∘ₗ D = C ∘ₗ d.symm - CST Sₕ` by unfolding D.

   Estimated effort: ~60 lines.

4. **Close Step 3 (~120 lines, line 351).** Build
   `T : L0' →ₗ L0` and verify the conjugation equation.
   - After `leviGL_E_conj_XCB d` and `uD_conj_XCB D`, the conjugated
     operator equals `XCB (CST Sₕ) B''` where
     ```
     B'' = lambdaDualE d.symm ∘ B ∘ d.symm + (Cdual D ∘ C - Cdual C ∘ D - Cdual D ∘ X0 ∘ D) ∘ d.symm
     ```
   - **Choose `D|_{L1'}` carefully** so `B''(L1') ⊂ L1`:
     the existence of such a choice uses
     `vplusKerPairing_isPerfPair` (X0Geometry).  This may force a
     restructuring of Step 2's `D` to be a *specific* `D`, not just
     any lift.
   - Skewness of `B''` propagates from `_hB`'s skewness through
     Levi+unipotent transformations.
   - The skew condition then forces `B''(L0') ⊂ L0`.  Define
     `T u := codRestrict L0 (B'' u) <proof>` for `u ∈ L0'`.
   - Verify the conjugation equation
     `uD D ∘ leviGL_E d ∘ XCB C B = XST Sₕ T ∘ uD D ∘ leviGL_E d`
     by combining `leviGL_E_conj_XCB` and `uD_conj_XCB` with the
     identity `B'' = BST T` (which holds by construction of T).

   Estimated effort: ~120 lines.

**Decomposition strategy:** if the full body is too large, split
Step 1, Step 2, Step 3 into focused private helpers
(`pNormalForm_witnesses_aux_step1` etc.), each with its own sorry
if necessary.  Round 9 already partially set this up.

**Stop conditions:**
- If the build cannot be repaired in the first ~20% of round budget:
  back out the broken Step 0.75 sub-construction entirely and use
  `LinearEquiv.ofFinrankEq` for `cbarK'` (Option Replace above).
  The alignment proof becomes harder but the build is green.
- If Step 3 (T-construction) is intractable: ship Step 1 + Step 2,
  leave Step 3 as a focused sorry.
- Estimated total effort: ~260 lines (down from ~300 originally,
  since dim chain + Sₕ are already landed).

**Mathlib lemmas:**
- `LinearEquiv.ofBijective` — `cbarK'`.
- `LinearEquiv.prodCongr` — block-diagonal product map.
- `Submodule.prodEquivOfIsCompl` — both `L1'⊕L0' ≃ E'` and
  `K'⊕ker(Cbar) ≃ E'`.
- `Submodule.exists_isCompl` — for `K`.
- `LinearMap.linearEquivOfInjective` — `X0|_K`.
- `linear_combination hsum` (NOT `linarith`) for line 308.

**References:**
- `InducedOrbitToy/NormalForm.lean` lines 152–196 (in-file docstring).
- `.archon/informal/normalform_round7.md` § Tier A #1.
- `.archon/task_results/processed/round9/InducedOrbitToy_NormalForm.lean.md`
  ("Strategy notes for Round 10").
- `references/blueprint_verified.md` lines 200–264.

**Acceptance criteria:**
- `lake env lean InducedOrbitToy/NormalForm.lean` compiles.
- `lake build` is green (verified independently by plan agent).
- Step 0.75 build-break (lines 277–310) is fixed.
- Step 1 (line 322) sorry replaced by real proof.
- Step 2 (line 339) sorry replaced or punted into focused
  `_step2` helper with its own sorry.
- Step 3 (line 356) sorry replaced or punted into focused
  `_step3` helper with its own sorry.
- `#print axioms pNormalForm` shows
  `[propext, Classical.choice, Quot.sound]` IF all sub-steps close.
- No new `axiom` declarations.

### `InducedOrbitToy/Orbits.lean ::`
### `isParabolicElement_ringInverse_of_orbit_witness` (Round 10 secondary)

Round 9 partial: the body is now structurally sound modulo the
kernel-identification sub-claim (line 563) for the flagE conjunct.
The flagEV0 conjunct (line 624) is still deferred (needs Bruhat /
`parabolic_decompose`).

**Round 10 strategy — option (a) signature tightening:**

1. **Tighten helper signature.** Replace
   `(_hT₁ : SliceSetup.IsSkewT S T₁) (_hT₂ : SliceSetup.IsSkewT S T₂)`
   with
   `(hT₁ : T₁ ∈ S.Tset_circ) (hT₂ : T₂ ∈ S.Tset_circ)`.

2. **Add `by_cases` on `S.eps = 1 ∧ Odd (finrank L0')`.**
   - **Easy case** `¬ (S.eps = 1 ∧ Odd (finrank L0'))`:
     `MaximalRank = finrank L0'` (by `unfold MaximalRank; rw [if_neg h_easy]`).
     Combined with `Tset_circ`'s `finrank (range T_i) = MaximalRank`,
     rank-nullity gives `LinearMap.ker T_i = ⊥`:
     ```
     have hMR : S.MaximalRank = Module.finrank F S.L0' := by
       unfold SliceSetup.MaximalRank; rw [if_neg h_easy]
     have hker1 : LinearMap.ker T₁ = ⊥ := by
       have h_rank := LinearMap.finrank_range_add_finrank_ker T₁
       rw [hT₁.2, hMR] at h_rank
       have : Module.finrank F (LinearMap.ker T₁) = 0 := by omega
       exact Submodule.finrank_eq_zero.mp this
     ```
     Use `ker_XST_eq_flagE_of_injective` (already landed Round 9) for
     each of T₁, T₂.  Close the kernel-identification sub-claim
     fully.
   - **Hard case** `(S.eps = 1 ∧ Odd (finrank L0'))`:
     leave a focused `sorry` with a Gap comment.  This case requires
     case-3 specific reasoning (see Tier S #7 / blueprint lines
     658–676).

3. **Update caller.** `sIndependenceAndOrbitCriterion`'s call site
   at lines ~700+ in Orbits.lean currently passes `hT₁.1`, `hT₂.1`
   (extracting `IsSkewT` from `Tset_circ`).  After the helper's
   signature tightens, pass `hT₁`, `hT₂` directly.

4. **flagEV0 conjunct (line 624):** still sorry'd.  Document the
   case-3 dependency on `parabolic_decompose` more explicitly.
   No structural change in Round 10.

**Stop conditions:**
- The signature tightening cascade should be 1-step (only the call
  site in `sIndependenceAndOrbitCriterion` needs updating).  If a
  build cascade emerges (e.g., other consumers), revert.
- If the rank-nullity `ker T = ⊥` proof hits an obstacle, isolate it
  as a private helper.
- Estimated effort: ~50 lines.

**Mathlib lemmas:**
- `LinearMap.finrank_range_add_finrank_ker` — rank-nullity for T.
- `Submodule.finrank_eq_zero` — `finrank = 0 ↔ submod = ⊥`.
- `omega` — arithmetic from rank-nullity.
- `unfold SliceSetup.MaximalRank` + `rw [if_neg ...]` — case analysis
  on `MaximalRank`.

**Project-internal:**
- `ker_XST_eq_flagE_of_injective` (Orbits.lean line 444, Round 9
  helper).
- `S.MaximalRank`, `S.Tset_circ` (NormalForm.lean lines 54, 62).

**Acceptance criteria:**
- `lake env lean InducedOrbitToy/Orbits.lean` compiles.
- `lake build` green at end of round.
- Helper signature tightened to `T_i ∈ Tset_circ`.
- Kernel-identification sub-claim (line 563) closed in cases 1-2;
  case 3 sorry'd with documented Gap.
- flagEV0 conjunct (line 624) still sorry'd (deferred).
- Caller `sIndependenceAndOrbitCriterion` updated to pass `hT_i`
  directly.
- `#print axioms sIndependenceAndOrbitCriterion`,
  `#print axioms main` — still transitively `sorryAx`-marked due to
  case-3 + flagEV0.  Public-theorem clean status unchanged.

### `InducedOrbitToy/Slice.lean :: parabolic_decompose` (Round 10 deferred)

Same as Round 9.  No prover work this round.  If a prover is
dispatched, file a "no work" report and verify
`lake env lean InducedOrbitToy/Slice.lean` is green.

## Completed (carried forward)

See `task_done.md` for the full list.  Highlights through Round 9:

- All Round 1–8 deliverables.
- Round 9 NormalForm: `_hL1'` cascade landed; Step 0 + Step 0.5
  (dimension chain) sorry-free; Step 0.75 partially set up (and
  partially broken — Round 10 fixes).
- Round 9 Orbits: 3 new sorry-free private helpers (`orbit_conj_rearr`,
  `flagE_le_ker_XST`, `ker_XST_eq_flagE_of_injective`).  Helper body
  refactored; flagE conjunct closes modulo case-3.
