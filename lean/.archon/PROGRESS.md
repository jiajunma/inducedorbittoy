# Project Progress

## Current Stage
prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover  ← current (round 10)
- [ ] polish

## Authoritative Sources

- Blueprint: `references/blueprint_verified.md` (1049 lines).
- Module split + scope decisions: `references/formalization_plan.md`.
- Per-file informal sketches: `.archon/informal/{slice,normalform,localforms,orbits}.md`.
- Round 6 informal sketch: `.archon/informal/levi.md` — Levi machinery
  for `Slice.lean`. Includes § 6.6 sketch for `parabolic_decompose`.
- Round 7 informal sketch: `.archon/informal/normalform_round7.md` —
  full proof outline for `pNormalForm_witnesses` (Tier A #1) plus the
  two `residual_levi_*` helpers.
- Round 9 task results (archived): `.archon/task_results/processed/round9/`.
- Cumulative state: `.archon/PROJECT_STATUS.md`.

## Verified State (independent checks, end of Round 9)

- `lake build` is **NOT green** — `InducedOrbitToy/NormalForm.lean`
  has compilation errors at lines 302–308 from the Round-9 prover's
  unfinished Step 0.75 sub-construction (variable swap + `linarith`
  over a non-ordered field).  Round 10 must fix the build first.
- `lake env lean InducedOrbitToy/Orbits.lean` compiles in isolation
  (single declaration-use sorry warning at line 524).
- `lake env lean InducedOrbitToy/Slice.lean` compiles in isolation
  (single declaration-use sorry warning at line 1109).
- `lake env lean InducedOrbitToy/Basic.lean`,
  `InducedOrbitToy/X0Geometry.lean`,
  `InducedOrbitToy/LocalForms.lean` — all compile cleanly.
- Custom `axiom` declarations: 0.
- **Public-theorem axiom audit (frozen end of Round 8; Round 9 did
  not change the public surface):**
  - `pNormalForm_residual_orbit_iso`, `inducedOrbits`,
    `multiplicityNonDeg`, `multiplicityOddCase`,
    `multiplicityEvenSymmCase` —
    `[propext, Classical.choice, Quot.sound]` (clean).
  - `pNormalForm` — transitive `sorryAx` via
    `pNormalForm_witnesses_aux`.
  - `sIndependenceAndOrbitCriterion`, `main` — transitive `sorryAx`
    via `isParabolicElement_ringInverse_of_orbit_witness`.

### Remaining declaration-use `sorry` warnings (verified end of Round 9)

| File | Line | Declaration | Round 10 priority |
|---|---|---|---|
| `InducedOrbitToy/NormalForm.lean` | 197 | `pNormalForm_witnesses_aux` (5 internal sorries: 309, 310, 322, 339, 356) | **Primary — also fix build** |
| `InducedOrbitToy/Orbits.lean` | 524 | `isParabolicElement_ringInverse_of_orbit_witness` (2 sorries: 563, 624) | **Secondary** |
| `InducedOrbitToy/Slice.lean` | 1109 | `parabolic_decompose` | Deferred (no consumers; Tier S #6) |

If Round 10 (a) fixes the NormalForm build and (b) closes Steps 1, 2,
3 in `pNormalForm_witnesses_aux`, AND (c) closes the easy-case branch
of the Orbits helper via Tier S #7 signature tightening, then:
- `pNormalForm` becomes axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
- `sIndependenceAndOrbitCriterion` and `main` retain transitive
  `sorryAx` via the case-3 + flagEV0 sub-cases (deferred to polish).
- Project advances `prover` → `polish` once build is green and all
  Tier S #6 / #7 deferrals are documented.

## Round Plan

| Round | Focus | Files | Sorry Δ |
|---|---|---|---|
| 6 (done) | Add Levi machinery to `Slice.lean` | Slice | 4 → 5 (additive) |
| 7 (done) | Close `residual_levi_*`; restructure `pNormalForm_witnesses` signature | NormalForm | 5 → 3 |
| 8 (done) | Body sorries on public theorems closed; sorries relocated to private helpers; mathematical gap identified for `parabolic_decompose` | NormalForm + Orbits + Slice | 3 → 3 (positions changed) |
| 9 (done) | `_hL1'` cascade + dim chain in NormalForm; kernel-identification refactor in Orbits | NormalForm + Orbits | 3 → 3 (positions changed; build broke late) |
| **10 (this round)** | **Fix NormalForm build; close Steps 1-3 of `pNormalForm_witnesses_aux`; tighten Orbits helper signature (option (a))** | NormalForm + Orbits (parallel) | **3 → 1 or 2 (target; flagEV0 + case-3 deferred)** |

If Round 10 closes the NormalForm Steps 1-3 (or even just Step 1 +
Step 2), `pNormalForm` becomes axiom-clean.  If Round 10 also lands
the Orbits Tier S #7 signature tightening, the case-3 + flagEV0
sorries are clearly isolated as the only blockers, and the project
advances `prover` → `polish`.

## Current Objectives (Round 10)

**Two independent files, two independent objectives, dispatched in
parallel.** No cross-file edit overlap; harness runs them concurrently.

### 1. `InducedOrbitToy/NormalForm.lean` — fix build, close Steps 1-3 of `pNormalForm_witnesses_aux`

**Reference:** in-file docstring at lines 152–196; full informal
proof outline at `.archon/informal/normalform_round7.md` § Tier A #1;
Round 9 prover's "Strategy notes for Round 10" in
`.archon/task_results/processed/round9/InducedOrbitToy_NormalForm.lean.md`.

**Reference (blueprint):** `references/blueprint_verified.md` lines
200–264 — the `prop:p-normal-form` proof.

**Reference (project files):**
- `Slice.lean` Round 6 Levi machinery: `lambdaDualE`,
  `lambdaDualE_pairing_eq`, `leviGL_E`, `leviGL_E_apply`,
  `leviGL_E_isParabolic`, `leviGL_E_conj_XCB`,
  `leviGL_E_symm_inverse`. All sorry-free.
- `Slice.lean` unipotent half: `parametrizeX0PlusU_existence`,
  `parametrizeX0PlusU_uniqueness`, `uD`, `uD_apply`, `uD_neg_inverse`,
  `uD_conj_XCB`, `uD_isParabolic`. All sorry-free.
- `NormalForm.lean` Round 7 helpers: `XST_apply`,
  `extendL0'IsoToE'` (private), and the `kernelImage_*` API.
- `X0Geometry.lean`: `vplusKerPairing_isPerfPair`,
  `sDual_restrict_ker_isIso`, `finrank_Vplus_eq_c`,
  `VplusEquivQuotientRange`.

**Round 9 inheritance (sorry-free preparation):**

The Round 9 prover landed sorry-free preparation up through Step
0.75 (modulo 2 build bugs):
- Step 0: `Sₕ : L1' ≃ Vplus` via `LinearEquiv.ofFinrankEq`.
- Step 0.5: full dimension chain (`h_Cbar_surj`, `h_dim_ker_Cbar`,
  `h_dim_L0'`, `h_dim_match`).
- Step 0.75: `gL0 : L0' ≃ ker(Cbar)`, `K' ⊕ ker(Cbar)` complement.

**The `_hL1' : Module.finrank F S.L1' = c S.toX0Setup` hypothesis is
already cascaded** through `pNormalForm_witnesses_aux` (line 197),
`pNormalForm_witnesses` (line 264), and `pNormalForm` (line 306).
No further signature changes needed.

**Build break to fix first:**

Lines 277–310 contain an unfinished inline `CbarK'_inj` /
`CbarK'_surj` proof with TWO bugs:

1. **Variable-name swap at line 300.** Since
   `hK'_compl : IsCompl (LinearMap.ker (Cbar S C)) K'`, after
   `rw [← hK'_compl.codisjoint.eq_top, Submodule.mem_sup]` on
   `z ∈ ⊤`, the destructure
   `obtain ⟨k, hk_K', n, hn_ker, hsum⟩ := hz_top`
   yields `k ∈ ker(Cbar)`, `n ∈ K'`, `k + n = z` — opposite to the
   chosen names.  Fix:

   ```lean
   obtain ⟨k, hk_ker, n, hn_K', hsum⟩ := hz_top
   ```

   Then update lines 302–305: `hCbar_n` should be derived from
   `hk_ker` (typo: rename `hCbar_n` → `hCbar_k` if needed for
   readability); `refine ⟨⟨n, hn_K'⟩, ?_⟩` (using `n` instead of `k`
   for the K'-element); `show Cbar S C ((⟨n, hn_K'⟩ : K').val) = y`,
   etc.

2. **`linarith` over a non-ordered field at line 308.**  Replace
   `linarith [hsum]` with `linear_combination hsum` (or
   `eq_sub_of_add_eq hsum.symm` — `linear_combination` is the
   already-documented gotcha-pattern for module-vector identities).

After fixing these two bugs, lines 309 and 310 (the remaining
sub-`sorry`s) close via `map_sub` + `hCbar_k` (Cbar k = 0) + `hz`
(Cbar z = y), yielding `Cbar S C n = y`.

**Round 10 strategy (post-fix):**

After the Step 0.75 build-break is resolved:

1. **Step 1 (~80 lines, line 322).** Build the `d : E' ≃ E'`:
   - Wrap `CbarK'_lin` as `cbarK' : K' ≃ V0/range X0` via
     `LinearEquiv.ofBijective`.
   - `f : L1' ≃ K'` via composition
     `Sₕ ≪≫ VplusEquivQuotientRange.symm ≪≫ cbarK'.symm`.
   - `(f, gL0) : L1' × L0' ≃ K' × ker(Cbar)` via
     `LinearEquiv.prodCongr`.
   - `prodEq_L : L1' × L0' ≃ E'` via
     `Submodule.prodEquivOfIsCompl S.L1' S.L0' S.isComplL'`.
   - `prodEq_K : K' × ker(Cbar) ≃ E'` via
     `Submodule.prodEquivOfIsCompl K' (LinearMap.ker (Cbar S C)) hK'_compl.symm`.
   - `d.symm := prodEq_L.symm ≪≫ (f.prodCongr gL0) ≪≫ prodEq_K`.
   - `d := d.symm.symm`.
   - Verify `hd_L1'`: for `a' ∈ L1'`,
     `Cbar(d.symm a') = mkQ(Sₕ a')` via the explicit composition
     unfolding.
   - Verify `hd_L0'`: for `b' ∈ L0'`, `Cbar(d.symm b') = 0` via
     `gL0 b' ∈ ker(Cbar)`.

2. **Step 2 (~60 lines, line 339).** Build `D : E' →ₗ V0`:
   - Show `(C ∘ d.symm - CST Sₕ) e0 ∈ range S.X0` for every `e0`,
     using `hd_L1'` and `hd_L0'`.
   - Pick `K ⊕ ker X0 = V0` via `Submodule.exists_isCompl`.
   - `X0|_K : K ≃ range X0` via `LinearMap.linearEquivOfInjective`.
   - Compose to get `D : E' →ₗ V0` with the alignment property.

3. **Step 3 (~120 lines, line 356).** Build `T : L0' →ₗ L0`:
   - After `leviGL_E_conj_XCB d` and `uD_conj_XCB D`, the conjugated
     operator equals `XCB (CST Sₕ) B''` for an explicit `B''`.
   - Choose `D|_{L1'}` carefully (via `vplusKerPairing_isPerfPair`)
     so that `B''(L1') ⊂ L1`.
   - Skewness propagates from `_hB`.
   - `T := codRestrict L0 (B'' |_{L0'}) <proof>`.
   - Verify the conjugation equation via `parametrizeX0PlusU_uniqueness`.

**Decomposition strategy:** if the full body proves too large, split
each Step into a focused private helper (`_step1`, `_step2`,
`_step3`).  Each carries its own sorry if intractable.  Round 9
already partially set this up.

**Stop conditions:**
- If the build cannot be repaired in the first 20% of round budget,
  back out the broken Step 0.75 sub-construction entirely (replace
  `CbarK'_lin` with `LinearEquiv.ofFinrankEq` on a dim equality),
  even at the cost of a slightly harder Step 1 alignment proof.
- If Step 3 is intractable: ship Steps 1+2, leave Step 3 as a
  focused sorry inside `_step3` helper.
- Estimated total effort: ~260 lines.

**Acceptance criteria:**
- `lake env lean InducedOrbitToy/NormalForm.lean` compiles.
- `lake build` is green at end of round.
- Step 0.75 build-break (lines 277–310) is fixed.
- Step 1 (line 322) sorry replaced by real proof.
- Step 2 (line 339) sorry replaced or moved to `_step2` helper.
- Step 3 (line 356) sorry replaced or moved to `_step3` helper.
- `#print axioms pNormalForm` shows
  `[propext, Classical.choice, Quot.sound]` IF all sub-steps close.
- No new `axiom` declarations.

### 2. `InducedOrbitToy/Orbits.lean` — Tier S #7: tighten helper signature, close easy cases of kernel-identification

**Reference:** Gap docstring at Orbits.lean lines 487–523;
Round 9 prover's "Next steps (Round 10 candidates)" in
`.archon/task_results/processed/round9/InducedOrbitToy_Orbits.lean.md`.

**Reference (project files):**
- `NormalForm.lean :: MaximalRank` (line 54), `Tset_circ` (line 62) —
  `Tset_circ T ↔ IsSkewT T ∧ finrank (range T) = MaximalRank`.
- `Orbits.lean :: ker_XST_eq_flagE_of_injective` (line 444, Round 9
  helper) — `LinearMap.ker T = ⊥ → ker XST = flagE`.
- `Orbits.lean :: orbit_conj_rearr` (line 421, Round 9 helper) —
  conjugation rearrangement, sorry-free.
- `Orbits.lean :: flagE_le_ker_XST` (line 457, Round 9 helper) —
  unconditional `flagE ⊆ ker XST`, sorry-free.

**Round 9 inheritance:**

The body of `isParabolicElement_ringInverse_of_orbit_witness` (line
524) is structurally sound modulo the kernel-identification
sub-claim (line 563):

```lean
have h_kerXST_eq_flagE :
    LinearMap.ker (XST S Sₕ T₁) = S.flagE
      ∧ LinearMap.ker (XST S Sₕ T₂) = S.flagE :=
  sorry  -- TODO: case-split on (eps = 1 ∧ Odd l)
```

The flagE conjunct closes fully once this sub-claim lands.  The
flagEV0 conjunct (line 624) is independently sorry'd and remains so
(deferred to polish via `parabolic_decompose`).

**Round 10 strategy — Tier S #7 (option (a) signature tightening):**

1. **Tighten helper signature.** Replace
   `(_hT₁ : SliceSetup.IsSkewT S T₁) (_hT₂ : SliceSetup.IsSkewT S T₂)`
   with
   `(hT₁ : T₁ ∈ S.Tset_circ) (hT₂ : T₂ ∈ S.Tset_circ)`.

2. **Add `by_cases h_easy : ¬ (S.eps = 1 ∧ Odd (Module.finrank F S.L0'))`
   wrapping the `h_kerXST_eq_flagE` derivation.**

   - **Easy branch (cases 1, 2):**
     ```lean
     have hMR : S.MaximalRank = Module.finrank F S.L0' := by
       unfold SliceSetup.MaximalRank
       rw [if_neg h_easy]
     have hker_eq_bot : ∀ T : S.L0' →ₗ[F] S.L0,
         T ∈ S.Tset_circ → LinearMap.ker T = ⊥ := by
       intro T hT
       have h_rank := LinearMap.finrank_range_add_finrank_ker T
       rw [hT.2, hMR] at h_rank
       have hker_zero : Module.finrank F (LinearMap.ker T) = 0 := by omega
       exact Submodule.finrank_eq_zero.mp hker_zero
     have hker1 : LinearMap.ker T₁ = ⊥ := hker_eq_bot T₁ hT₁
     have hker2 : LinearMap.ker T₂ = ⊥ := hker_eq_bot T₂ hT₂
     refine ⟨?_, ?_⟩
     · exact ker_XST_eq_flagE_of_injective S _hNondeg Sₕ T₁ hT₁.1 hker1
     · exact ker_XST_eq_flagE_of_injective S _hNondeg Sₕ T₂ hT₂.1 hker2
     ```
   - **Hard branch (case 3, ε=+1, l odd):** `sorry` with a Gap
     comment noting that the helper as currently stated is
     mis-stated in this case (the kernel-identification fails when
     `dim ker T_i = 1`).  Closing case 3 requires either a separate
     argument via uniqueness of alternating forms (blueprint lines
     658–676), or restructuring the caller
     `sIndependenceAndOrbitCriterion` to avoid this code path in
     case 3.

3. **Update caller `sIndependenceAndOrbitCriterion`.** Find the call
   site of `isParabolicElement_ringInverse_of_orbit_witness` (around
   line 700+ in Orbits.lean) and replace the `hT_i.1` extraction
   (currently passing `IsSkewT` projected from `Tset_circ`) with
   `hT_i` directly.  The caller already has `hT₁ hT₂ ∈ Tset_circ` in
   scope.

4. **flagEV0 conjunct (line 624) — no change.**  Document the
   case-3 dependency on `parabolic_decompose` more explicitly in
   the Gap comment if needed.  Sorry remains.

**Stop conditions:**
- If the rank-nullity `ker T = ⊥` derivation runs into an obstacle
  (e.g., `Submodule.finrank_eq_zero` doesn't unify cleanly), package
  it as a private helper.
- If the caller cascade hits more than 1 site, revert and re-plan.
- Estimated effort: ~50 lines.

**Acceptance criteria:**
- `lake env lean InducedOrbitToy/Orbits.lean` compiles.
- `lake build` green at end of round.
- Helper signature uses `T_i ∈ Tset_circ` (not `IsSkewT`).
- The kernel-identification sub-claim (line 563) is split:
  - Easy cases (1, 2): closed sorry-free via
    `ker_XST_eq_flagE_of_injective` + rank-nullity from `Tset_circ`.
  - Hard case (3): focused sorry with documented Gap.
- flagEV0 sorry (line 624) remains; deferred to polish.
- Caller `sIndependenceAndOrbitCriterion` updated.
- `#print axioms sIndependenceAndOrbitCriterion`,
  `#print axioms main` — still transitive `sorryAx` via case 3
  + flagEV0 (expected).

### Files NOT assigned this round

The following files have no Round-10 sorries assigned. If the harness
dispatches a prover anyway, the prover should:
- verify the file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`),
- write a brief "no work" `task_results/<File>.md`, and
- **not edit anything**.

- `InducedOrbitToy/Basic.lean` — already done; no sorries.
- `InducedOrbitToy/X0Geometry.lean` — already done (session 4);
  no sorries. Pre-existing `unused variable hlambda` lint at
  line 221 must be left intact (part of the autoformalised
  signature).
- `InducedOrbitToy/LocalForms.lean` — already done; no sorries.
- `InducedOrbitToy/Slice.lean` — `parabolic_decompose` (line 1109)
  carries a documented mathematical gap (Tier S #6, deferred).
  **Do NOT attempt to close `parabolic_decompose` with the current
  signature.**  If a prover is dispatched: verify-only, "no work"
  report.

## Coordination notes for Round 10 (parallel-safety)

- **Two files edited simultaneously.** No source-level overlap:
  NormalForm prover edits lines ~277–360 (Step 0.75 fix + Steps
  1, 2, 3), Orbits prover edits lines ~524–610 (helper signature +
  kernel-identification body) plus the call site in
  `sIndependenceAndOrbitCriterion` (around line 700+).
- **Cross-file dependencies:**
  - NormalForm Objective 1 has `Slice.lean` Round 6 + Round 7 APIs
    + `X0Geometry.lean` `VplusEquivQuotientRange` /
    `vplusKerPairing_isPerfPair` as dependencies — all stable and
    sorry-free.
  - Orbits Objective 2 has `NormalForm.lean :: Tset_circ`,
    `MaximalRank`, `kernelImage_ker` (via Round 9 helper) as
    dependencies — all stable.
  - **No cross-file race risk.** Both are file-local edits.
- **Build coupling:** Round 9 ended with NormalForm broken.  Round 10
  NormalForm prover MUST get a green isolated build before merging.
  Orbits prover can proceed independently as Orbits.lean is currently
  green in isolation.
- **End-of-round merge:** harness merges both file edits.  Plan
  agent must verify `lake build` independently (Round 9's prover
  self-report contradicted reality).

## Reusable Gotchas (carry forward, augmented through Round 9)

- `LinearMap.IsAdjointPair`, **not** `LinearMap.BilinForm.IsAdjointPair`.
- `LinearMap.IsOrthogonal B g` unfolds to `∀ x y, B (g x) (g y) = B x y`.
- `IsSkewAdjoint B X` (project-local) unfolds to
  `∀ x y, B (X x) y + B x (X y) = 0`.
- `Decidable (S.eps = 1 ∧ Odd l)` does not synthesise; use
  `open Classical in if … then … else …` inside `def` bodies.
- Trim `simp` argument lists; lints-as-errors reject unused simp args.
- `lean_diagnostic_messages` MCP needs absolute file paths.
- `[TopologicalSpace (Module.End F S.V)]` cannot be a file-level
  `variable` instance binder; thread it as an explicit hypothesis.
- `Submodule.linearProjOfIsCompl` is the right tool for `L1' ⊕ L0'` /
  `L1 ⊕ L0` decompositions.
- Term-mode `sorry`s must be replaced with a real construction before
  any downstream theorem about them can be discharged.
- Polymorphic typeclass over multi-universe structures: declare with
  explicit `class C.{u, v, w, x} ...`; `Type*` placeholders in class
  fields do not unify across uses.
- `change Module.finrank F S.paired.E + _ = _` to bridge `S.E ≡ S.paired.E`
  abbrev boundary before `omega`.
- Block-matrix `_apply` helpers: write the fully unfolded RHS in a
  `show` clause before `rfl`.
- `(2 : F)⁻¹ + (2 : F)⁻¹ = 1`: `rw [← two_mul, mul_inv_cancel₀ hChar]`
  (do **not** `field_simp`).
- `Ring.inverse` on `Module.End F V` is the right packaging for
  "best-effort inverse" in orbit predicates (no division-ring needed).
- `Units.mkOfMulEqOne` for `IsUnit` from one-sided inverse.
- `obtain ⟨a, b, c⟩ := <existential>` makes destructured fields opaque
  — fix by packaging the equation directly in helper's conclusion.
- Verify structure location via `grep` before scoping a refactor.
- **Adjoint-pair → orthogonal via paired inverse:**
  given `IsAdjointPair B B f g` and `g ∘ f = id`, conclude
  `IsOrthogonal B f` via 3-line calc chain.
- **Cross-file proof structure validation via `lean_run_code`:** when a
  proof depends on a sister-prover's signature change.
- **Bilinear-form identities via block-decomposition + `linear_combination`:**
  destruct vectors as `(e, v, e')`, apply `*_apply` lemmas, simp the
  ambient form, apply pairing-eq lemmas, then close with
  `linear_combination`.
- **`IsSkewAdjoint` closure proofs over generic `[Field F]`:** use
  `linear_combination hf + hg` (add) / `linear_combination c * hf` (smul).
  **Do not use `linarith`** — it requires `LinearOrderedField`.
- **Submodule-vector identities (e.g. `k = z - n` from `k + n = z`)
  over a generic field:** use `linear_combination hsum`, NOT
  `linarith` (Round 9 build-break diagnosis).
- **`Submodule.IsCompl.projection_add_projection_eq_self`** combined
  with `Submodule.IsCompl.projection_apply` to bridge the
  `IsCompl.projection` and `linearProjOfIsCompl`-coerced-subtype forms.
- **`conv_lhs => rw [...]`** to scope a rewrite to the LHS only.
- **Cross-file 4-tuple cascade:** when a structure or predicate gains a
  new conjunct, every `obtain ⟨...⟩` and `refine ⟨..., ?_⟩` site needs
  a parallel arity bump.
- **`linear_combination` is scalar-only over generic Modules.** For
  module identities, drop to `rw` chains + `abel`.
- **Subtype-wrapping anti-pattern for `Iso + Property`:**
  inline the `obtain` at each Prop-conclusion call site.
- **Drop explicit `LinearMap` coercion in `rw` arguments** once the
  callee accepts `LinearEquiv`.
- **`lean_leansearch` natural-language >> `lean_loogle`** for
  projection / `IsCompl.projection_*` API discovery.
- **`#print axioms` via `Bash` + `/tmp/check_axioms.lean`:** standard
  closure-check pattern.
- **(Round 7) `prodEquivOfIsCompl` symm via
  `Submodule.toLinearMap_prodEquivOfIsCompl_symm`.**
- **(Round 7) `set ... with hdef` for opaque shorthands, BUT NOT for
  sums you'll later `LinearMap.add_apply`-rewrite.**
- **(Round 7) `congr 1` does NOT split through outer `LinearMap.comp`.**
- **(Round 7) Linearity in 1st arg of `S.paired.pairing`: `map_add`
  first, then `add_apply`.**
- **(Round 7) `(qFun l : L0').val = qFunRaw l` is *definitionally* equal**
  when `qFun = LinearMap.codRestrict L0' qFunRaw _`.
- **(Round 7) Trailing `rfl` after `simp only [..., map_zero]` is
  "No goals" lint.**
- **(Round 7) LinearEquiv at definition; pass directly at use site.**
- **(Round 7) `S.V` ≡ `S.paired.E'` abbrev boundary requires explicit
  type ascription in helper defs.**
- **(Round 7) `XST_apply` private helper near top of consuming
  section.**
- **(Round 7) `extendL0'IsoToE'` block-extension pattern.** Build
  `E' ≃ E'` extending an `L0' ≃ L0'` iso by `id` on `L1'` via
  `prodEq.symm ≪≫ₗ (refl × h) ≪≫ₗ prodEq`.
- **(Round 8) `Ring.inverse` algebra on `Module.End F V`:**
  `Ring.inverse_mul_cancel`, `Ring.mul_inverse_cancel`,
  `IsUnit.ringInverse` are the canonical tools.  No division-ring
  needed.
- **(Round 8) `noncomm_ring` for module-endomorphism associativity.**
  Closes goals where `ring` (commutative-only) fails.
- **(Round 8) Body-sorry → helper-sorry refactor pattern.** Extract
  obstruction into focused private helper with own sorry + Gap
  comment.  Public-facing body becomes a one-liner.
- **(Round 8) Mathematical-gap finding via partial closure.** When a
  proof attempt extracts substantial structural data and then hits an
  obstruction that's not just plumbing, investigate the *statement*
  before retrying.  The Slice prover's `parabolic_decompose`
  finding (residual `B'` parameter missing) is a structural-fix
  outcome, not a prover failure.
- **(Round 9) Dim chain pattern.** When a helper takes a structural
  finrank hypothesis (`_hL1'`, `_hRank`), the dim chain (Cbar
  surjectivity, ker dim, complement dim) is fully closeable via
  Mathlib lemmas: `LinearMap.range_eq_top.mp` +
  `Submodule.eq_top_of_finrank_eq` for surjectivity from dim;
  `LinearMap.finrank_range_add_finrank_ker` + `omega` for
  rank-nullity; `Submodule.finrank_sup_add_finrank_inf_eq` +
  `IsCompl.codisjoint.eq_top` + `IsCompl.disjoint.eq_bot` +
  `finrank_top` + `finrank_bot` for sum-decomposition dim.
- **(Round 9) Kernel-identification refactor.** When two scoped
  sorries reduce to a common sub-claim, bundle them into one
  conjunctive sorry (e.g.
  `ker XST T₁ = flagE ∧ ker XST T₂ = flagE`) consumed by
  `obtain ⟨h1, h2⟩`.
- **(Round 9) `kernelImage_ker` + `Submodule.map_bot`:** when
  `ker T = ⊥`, the `(ker T).map L0'.subtype` quotient collapses to
  `⊥`, reducing kernel descriptions to flag descriptions.
- **(Round 9) `MaximalRank` case split:** `unfold
  SliceSetup.MaximalRank; rw [if_neg h_easy]` for the
  `¬ (eps = 1 ∧ Odd l)` branch; `if_pos` for the hard case.
- **(Round 9) `Submodule.mem_sup` destructure: variable order
  matters.** `IsCompl A B` → `Submodule.mem_sup` on `A ⊔ B` yields
  `⟨a, hA, b, hB, hsum⟩` where `hA : a ∈ A`, `hB : b ∈ B`.  Match
  variable names to types or downstream proofs break.
- **(Round 9) Plan-agent verification of `lake build`:** prover
  self-reports of "build green" can be wrong.  Always run
  `lake build` independently after merging task results.

## Reporting

Each prover writes `.archon/task_results/<File>.md` with:
- which sorries were closed (line numbers + theorem names);
- which definitions / theorems were *added* (private helpers, signature
  updates, hypothesis cascades);
- exact Mathlib lemmas used;
- any helper that was punted as `sorry` with a one-line gap explanation;
- confirmation that the assigned file compiles in isolation
  (`lake env lean InducedOrbitToy/<File>.lean`);
- **confirmation that `lake build` is green at end of round**
  (run `lake build` directly; do not rely on isolated-file checks);
- confirmation that no `axiom` was introduced
  (`#print axioms` for each newly-closed theorem in the file).
