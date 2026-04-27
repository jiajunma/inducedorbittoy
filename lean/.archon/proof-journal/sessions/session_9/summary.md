# Session 9 — Prover Round 7 (NormalForm.lean closure cascade)

## Metadata

- **Session:** 9 (stage `prover`, Round 7 — single-file focused dispatch on `NormalForm.lean`).
- **Sorry count (declaration-use warnings) before round:** 5
  - `NormalForm.lean`: 3 (`pNormalForm_witnesses` 195, `residual_levi_extract` 319, `residual_levi_build` 348).
  - `Slice.lean`: 1 (`parabolic_decompose` 1078, deferred from Round 6).
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` lines 358 + 376 — Tier A deferred).
- **Sorry count (declaration-use warnings) after round:** **3** (−2 net)
  - `NormalForm.lean`: 1 (`pNormalForm_witnesses` at line 216 — single isolated sorry, body documented).
  - `Slice.lean`: 1 (`parabolic_decompose` at line 1089 — unchanged).
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` lines 358 + 376 — unchanged).
- **Net change:** 5 → 3 declaration warnings (−2). Plan target was 5 → 2 (close all 3 NormalForm sorries); achieved 2 of 3 with the third (`pNormalForm_witnesses`) deferred to Round 8 as documented in the body docstring.
- **Custom axioms introduced:** 0. `#print axioms` audit:
  - `pNormalForm_residual_orbit_iso` (the public consumer, now sorry-free): `[propext, Classical.choice, Quot.sound]` — CLEAN.
  - `kernelImage_ker`, `kernelImage_im`, `kernelImage_dim`: CLEAN.
  - `pNormalForm`: still depends on `sorryAx` *transitively* via `pNormalForm_witnesses` — expected.
- **Build status:** `lake build` green at end of round (8033 jobs). Remaining warnings: 3 sorry declarations + 1 pre-existing unused-variable lint at `X0Geometry.lean:221`.
- **Pre-processed log:** 139 events total (1 summary line + 138 events), **19 edits to a single file** (`NormalForm.lean`), 2 explicit `lean_goal` checks, 20 diagnostic checks, 0 `lean_build` MCP calls (lake invoked via `Bash` directly), 11 lemma searches (mix of `lean_leansearch`, `lean_loogle`, `lean_local_search`).

## Process observation

The plan agent assigned **one** file this round (`NormalForm.lean` — close 3 sorries via the Round-6 Levi machinery). The harness still dispatched provers to all six files; non-objective provers (`Basic.lean`, `LocalForms.lean`, `Slice.lean`, `Orbits.lean`, `X0Geometry.lean`) correctly verified isolation, wrote brief "no work" reports, and made no edits.

The single objective prover landed two of three Round 7 targets cleanly (`residual_levi_extract` and `residual_levi_build`, both sorry-free). The third (`pNormalForm_witnesses`) was deferred to Round 8 with a single isolated `sorry` in the body and an extended docstring outlining the four-step plan.

A non-trivial **Tier S #5 signature restructure** also landed (`pNormalForm_witnesses` exposes a Levi factor `d` and `Sₕ` strengthened to `LinearEquiv`), cascading correctly through `pNormalForm`, `pNormalForm_residual_orbit_iso`, and the two `residual_levi_*` helpers. The new public statement of `pNormalForm_residual_orbit_iso` is sorry-free (verified by axiom audit).

## Target — `InducedOrbitToy/NormalForm.lean :: residual_levi_extract` ✅ CLOSED

### Approach (Option B — no `parabolic_decompose` dependency)

Per `informal/normalform_round7.md` § Tier A #2 (and the session 8 prover's
recommendation in the task_results report). Four-step skeleton:

1. **Step A (preserve L0').** For `l : L0'`, evaluate `p ∘ XST(Sₕ, T₁) = XST(Sₕ, T₂) ∘ p` at `(0, 0, (l : E'))`. The V0-component equation `0 = X0 v + (Sₕ (projL1' e') : V0)` plus `Vplus ⊕ range X0 = V0` (`S.isCompl.disjoint`) forces both `(Sₕ (projL1' e') : V0) = 0` and `X0 v = 0`. `Sₕ : L1' ≃ Vplus` (LinearEquiv strengthening from Tier S #5) gives `Sₕ.injective`, so `projL1' e' = 0`, i.e., `e' ∈ L0'`.
2. **Step B (define h).** Define `qFunRaw : L0' →ₗ E' := projE'_V ∘ p ∘ inE' ∘ L0'.subtype`. Step A gives `qFunRaw l ∈ L0'`, so codRestrict to `qFun : L0' →ₗ L0'`.
3. **Step C (h is bijective).** Show `qFun` is injective: if `qFun l = 0`, then `(p (0, 0, l)).2.2 = 0`, so `p (0, 0, l) ∈ flagEV0`. Since `p` is invertible *and* maps `flagEV0` to `flagEV0`, `p⁻¹` also preserves `flagEV0`, so `(0, 0, l) ∈ flagEV0`, i.e., `l = 0`. Build `LinearEquiv` via `LinearMap.linearEquivOfInjective` with `dim L0' = dim L0'`.
4. **Step D (verify isometry).** Use `IsOrthogonal` of `p` on `(T₁ u, 0, 0)` and `(0, 0, (v : E'))`; substitute `p (T₁ u, 0, 0) = XST(Sₕ, T₂) (p (0, 0, u))` from Step A's conjugation hypothesis; expand via `XST_apply`; kill the `Cdual` term using `Cdual_pairing_eq` + `(CST Sₕ) e'_v = 0`; reduce to `BT T₂ (h u) (h v) = BT T₁ u v`.

### Attempt log — `residual_levi_extract` (~10 edits inside this single theorem)

| # | Strategy | Result | Insight |
|---|---|---|---|
| 1 (edit log line 179, ~22kb edit) | First full-body skeleton with all four steps inlined. | ❌ `unexpected token 'from'; expected ')', ',' or ':'` at line 785; plus `Unknown identifier XST_apply` (helper not yet in scope). | XST_apply needed to be moved earlier in file before `residual_levi_extract`. |
| 2 (line 189) | Add `XST_apply` private helper at top of section. | ❌ Same unexpected `from` error remained. | The `from` issue is independent of XST_apply. |
| 3 (line 193) | Inlined helper consolidation. | ❌ New `Type mismatch: After simplification, term h has type qFun l = 0 but is expected to have type qFunRaw l = 0`. | `qFun = codRestrict L0' qFunRaw _`; the subtype unwrap needs explicit `Subtype.val` extraction. |
| 4 (line 200) | Replace `simpa using h` chain with explicit `have h_val : ((qFun l : S.L0') : S.paired.E') = 0 := by rw [hql]; rfl; exact h_val`. | ✅ qFun-injection step closes; new error elsewhere. | `(qFun l : L0').val = qFunRaw l` is *definitionally* equal when `qFun = LinearMap.codRestrict`. |
| 5 (line 206) | Restate `h_amb_unfold` (rewrite of hOrth's ambientForm via its definition). | ❌ `unexpected token ':='` at line 806. | Multiline `have : ... := by` indentation issue. |
| 6 (line 213) | `set p_uv := p (0, 0, (v : E'))` to abbreviate; restate h_amb_unfold. | ❌ Same `unexpected ':='`. | `set` syntax wasn't the issue; the problem was the `have` block formatting. |
| 7 (line 220) | `set lhs_E := Cdual ... + T₂ ...`; restate h_amb_unfold. | ❌ `Tactic rewrite failed: Did not find an occurrence of (?f + ?g) ?x in the target expression`. | `set`-ed sum is opaque; `rw [add_apply]` can't match it. |
| 8 (line 229) | Drop `zero_add` from rw chain (`rw [h_X0_c_u_zero, zero_add] at hOrth` → `rw [h_X0_c_u_zero] at hOrth`). | ❌ `Did not find occurrence of (?f + ?g) ?x` — same family. | Needed to abandon `set lhs_E` and re-inline. |
| 9 (line 236) | Restate h_amb_unfold inline (no `set` for sum). | ❌ `No goals to be solved` at line 819 + 829. | Over-reduction by `simp only [...]` + trailing `rfl`. |
| 10 (line 243) | Drop trailing `rfl` after `simp only [LinearMap.comp_apply, h_proj_e'v_L1', map_zero]`. | ✅ All errors gone. Only the deferred `pNormalForm_witnesses` sorry remains. | `simp only` with `map_zero` already closes `f 0 = 0`; trailing `rfl` triggers "No goals". |

After edit #10: `clean: true` from diagnostics. Final `lake build` green.

## Target — `InducedOrbitToy/NormalForm.lean :: residual_levi_build` ✅ CLOSED

### Approach

Per `informal/normalform_round7.md` § Tier A #3:

1. **Build d.** Define `extendL0'IsoToE' S h : E' ≃ E'` via the `Submodule.prodEquivOfIsCompl` direct-sum decomposition, applying `id × h` on the `(L1', L0')` product:
   ```lean
   prodEq.symm ≪≫ₗ ((LinearEquiv.refl F S.L1').prodCongr h) ≪≫ₗ prodEq
   ```
   where `prodEq := S.L1'.prodEquivOfIsCompl S.L0' S.isComplL'`.
   Pointwise: `d.symm e' = (projL1' e' : E') + (h.symm (projL0' e') : E')`.
2. **Take p := leviGL_E S d.** Parabolicity from `leviGL_E_isParabolic`.
3. **Verify conjugation.** By `leviGL_E_conj_XCB`,
   `leviGL_E d ∘ XCB(CST Sₕ, BST T₁) = XCB(CST Sₕ ∘ d.symm, lambdaDualE d.symm ∘ BST T₁ ∘ d.symm) ∘ leviGL_E d`.
   Reduce to two component identities:
   - `CST Sₕ ∘ d.symm = CST Sₕ` (uses `projL1' ∘ d.symm = projL1'`, proved as helper `projL1'_extendL0'IsoToE'_symm`).
   - `lambdaDualE d.symm ∘ BST T₁ ∘ d.symm = BST T₂` (uses `projL0' ∘ d.symm = h.symm ∘ projL0'`, then `lambdaDualE_pairing_eq`, then `IsCompl L1' L0'` decomposition + `S.L0_isotropic_L1'` to kill cross terms, then the hypothesis `hh u v: BT T₂ (h u) (h v) = BT T₁ u v` substituted at `u → h.symm u, v → h.symm b'`).

### Helper lemmas added

- `extendL0'IsoToE' (S, h) : E' ≃ E'` (private noncomputable def).
- `extendL0'IsoToE'_symm_apply` — pointwise formula for `d.symm`.
- `projL1'_extendL0'IsoToE'_symm`: `projL1' ∘ d.symm = projL1'`.
- `projL0'_extendL0'IsoToE'_symm`: `projL0' ∘ d.symm = h.symm ∘ projL0'`.

### Attempt log — `residual_levi_build` (4 edits)

| # | Strategy | Result | Insight |
|---|---|---|---|
| 1 (edit log line 137) | First-batch skeleton with `extendL0'IsoToE'` and `residual_levi_build` body. | ❌ `Application type mismatch: argument e' has type S.V but expected S.paired.E'`. | `S.V` ≡ `S.paired.E'` abbrev boundary needs explicit type ascription in helper definitions. |
| 2 (line 145) | Restructure `residual_levi_build` body around component identities `h_C` and `h_B`. | ❌ `unsolved goals`. | The `lambdaDualE` block reduction needed an explicit `lambdaDualE_pairing_eq` rewrite chain. |
| 3 (line 153) | Add `rfl` to `hBST_T₁` proof. | ❌ `Tactic rewrite failed: Did not find occurrence of (?f + ?g) ?x` after `lambdaDualE_pairing_eq`. | Test vector `e''` decomposition needed `map_add` (linearity in 1st arg of `pairing`) BEFORE `add_apply`. |
| 4 (line 159) | Reorder rewrite chain: `map_add` first, then `add_apply` (i.e., drop `LinearMap.add_apply` from the chain that came after `map_add`). | ❌ Type mismatch on consumer call site (`Sₕ` typing). | LinearEquiv vs LinearMap coercion issue at call site. |
| 5 (line 165) | Update consumer call site to pass `(Sₕ : S.L1' →ₗ[F] S.Vplus)` LinearMap-coerced. | ✅ `clean: true`. `residual_levi_build` closed. | `Sₕ` strengthened to LinearEquiv at definition; explicit coercion needed at use sites that expect LinearMap. |

## Target — `InducedOrbitToy/NormalForm.lean :: pNormalForm_witnesses` ⏸ DEFERRED

**Status:** STILL SORRY (single isolated `sorry` at line 216, extended docstring above it outlines the four-step plan).

The Tier S #5 **signature restructure** landed (replacing the mathematically-false `uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T` with the corrected Levi-factor form):
```lean
∃ (Sₕ : S.L1' ≃ₗ[F] S.Vplus) (D : S.E' →ₗ[F] S.V0)
  (d : S.E' ≃ₗ[F] S.E') (T : S.L0' →ₗ[F] S.L0),
  IsSkewT S T ∧
  uD S D ∘ₗ leviGL_E S d ∘ₗ XCB S C B
    = XST S (↑Sₕ) T ∘ₗ uD S D ∘ₗ leviGL_E S d
```

The body deferral plan (in the docstring):
1. Build `(Sₕ, d)` from `_hRank : rank Cbar = c` (the d-construction via `LinearEquiv.ofBijective`).
2. Set `(C', B') := (C ∘ d.symm, lambdaDualE d.symm ∘ B ∘ d.symm)` and apply `leviGL_E_conj_XCB`.
3. Build `D` such that `X0 ∘ D = C' - CST Sₕ` (lands in `range X0` by construction); `T` reads off the `B`-block residual.
4. Combine via `uD_conj_XCB` + `parametrizeX0PlusU_uniqueness` + `uD_neg_inverse`.

**Why deferred:** The two consumers (`residual_levi_extract` and `residual_levi_build`) are now sorry-free, which was the higher-priority plan target — `pNormalForm_residual_orbit_iso` is consequently sorry-free (axiom-audited). The full d-construction + uniqueness step is estimated ~150 lines and was beyond Round 7's budget.

### Cascading consumer changes that did land

- `pNormalForm` (line 248–): body refactored to consume the new `pNormalForm_witnesses` signature. Internal proof reduces conjugation goal `(uD D ∘ leviGL_E d) ∘ XCB C B = XST Sₕ T ∘ (uD D ∘ leviGL_E d)` to `hConj` modulo `LinearMap.comp_assoc`. Body sorry-free; depends on `pNormalForm_witnesses` so transitively `sorryAx`.
  - Edit attempts (lines 109/113/122 in raw log): #1 docstring update, #2 body rewrite (~4515 chars), #3 simplified final `congr` chain to `rw [LinearMap.comp_assoc]; exact hConj`.
- `pNormalForm_residual_orbit_iso` (line 990–): docstring restated, body unchanged structurally. **Sorry-free.**
- `XST_apply` (private helper, line 329): added because `residual_levi_extract` needs the explicit unfolding `XST S Sₕ T (e, v, e') = (Cdual S (CST S Sₕ) v + (T (projL0' S e') : S.E), S.X0 v + (Sₕ (projL1' S e') : S.V0), 0)`.

## Lemma searches (11 total)

The prover used `lean_leansearch` heavily for `IsCompl`-related decomposition and `LinearEquiv.prodCongr`-style API discovery:

| Query | Tool | Hit |
|---|---|---|
| "LinearEquiv from IsCompl decomposition combining equivs on complementary subspaces" | leansearch | `LinearMap.ofIsCompl` (not directly used; led to `prodEquivOfIsCompl`) |
| "LinearEquiv.prod" | loogle | No results |
| "LinearEquiv.prod" | local_search | No results (after init) |
| "linear equiv product of two linear equivs componentwise" | leansearch | `ContinuousLinearEquiv.piCongrRight` (wrong universe) |
| "LinearEquiv.prodCongr two linear equivs M ≃ N -> P ≃ Q -> M × P ≃ N × Q" | leansearch | **`LinearEquiv.prodCongr` ✅** — used in `extendL0'IsoToE'` |
| "prodEquivOfIsCompl symm linearProjOfIsCompl" | leansearch | `LinearMap.linearProjOfIsCompl` |
| "Submodule.map composition" | leansearch | `LinearMap.comp` |
| "Submodule.map composed of two linear maps equals submodule map of submodule map" | leansearch | `Submodule.map₂_map_map` |
| "linearProjOfIsCompl_apply" | grep | local |
| "prodEquivOfIsCompl apply pair sum subtype" | leansearch | `Submodule.prodEquivOfIsCompl` ✅ |
| "prodEquivOfIsCompl mk x y subtype add" | leansearch | confirmed `Submodule.prodEquivOfIsCompl` |

Notable: `lean_loogle` returned `No results found` for `LinearEquiv.prod` (a structural search), but `lean_leansearch` natural-language queries succeeded. This reproduces the session-5 reusable-pattern about `lean_leansearch >> lean_loogle` for projection / `IsCompl` API discovery.

## Key findings / patterns discovered

### Round 7 additions to the gotchas knowledge base

- **`prodEquivOfIsCompl` symm via `Submodule.toLinearMap_prodEquivOfIsCompl_symm`:** the symm coerces to `(linearProjOfIsCompl p q h).prod (linearProjOfIsCompl q p _)`, i.e., `prodEq.symm e' = (projL1' e', projL0' e')` for our `IsCompl L1' L0'`. Use this to compute `d.symm` apply lemmas without unfolding through `LinearEquiv.trans` repeatedly.

- **`set ... with hdef` for opaque shorthands:** when proving identities with multiple `(p (0, 0, ...))` occurrences, `set` abbreviates them. Beware: `set lhs_E := Cdual ... + T₂ ...` becomes opaque; `LinearMap.map_add` / `add_apply` cannot rewrite into the `set`-ed sum. Either don't `set` the sum, or `unfold` it before the `rw`.

- **`congr 1` on `XCB S A B = XCB S A' B' ∘ leviGL_E d` style equations doesn't split into 2 component goals** (the outer is `LinearMap` composition, not `XCB`). Better: prove the two component identities (`A = A'`, `B = B'`) as separate `have`s and chain `rw [hC, hB]`.

- **Linearity in first arg of bilinear `S.paired.pairing`:** `pairing (a + b) = pairing a + pairing b` is `LinearMap.map_add`; then `(f + g) e'_v = f e'_v + g e'_v` is `LinearMap.add_apply`. Order matters: `map_add` first, then `add_apply`.

- **`(qFun l : L0').val = qFunRaw l` is *definitionally* equal** when `qFun = LinearMap.codRestrict L0' qFunRaw _`. Use `(qFun l : E') = 0 → qFunRaw l = 0` via `exact h_val` (no `simpa`) — Subtype.val unwraps codRestrict.

- **Trailing `rfl` after `simp only [..., map_zero]` is often a "No goals" lint:** `simp only` with `map_zero` already closes the goal `f 0 = 0`. Drop the redundant `rfl`.

- **`Sₕ` LinearEquiv vs LinearMap coercion at consumer call sites:** when a private theorem strengthened `Sₕ` from `LinearMap` to `LinearEquiv`, the consumer call site that expects `S.L1' →ₗ[F] S.Vplus` must explicitly coerce: `residual_levi_extract S _hNondeg _hChar (Sₕ : S.L1' →ₗ[F] S.Vplus) ...` fails type-check; pass `Sₕ` directly (Lean auto-coerces via `LinearEquiv.toLinearMap`-via-CoeFun).

- **`S.V` ≡ `S.paired.E'` abbrev boundary in helper defs:** when defining `extendL0'IsoToE' S h : E' ≃ E'`, an explicit `(d.symm : S.paired.E' →ₗ[F] S.paired.E')` ascription is needed at every application site to bridge the abbrev. Without it: `Application type mismatch: argument e' has type S.V but expected S.paired.E'`.

### Reusable patterns flowing into PROJECT_STATUS.md

(Augments session 8 list.)

- **(NEW session 9) `XST_apply` private helper pattern.** When a proof needs the explicit unfolding of a multi-let block-matrix definition, write a `private theorem XST_apply` near the top of the consuming section. Saves ~10 lines per consumer.

- **(NEW session 9) Component-split identities via `have` chains, NOT `congr 1`.** For `XCB(A, B) = XCB(A', B') ∘ leviGL_E d`-style outer-composition equations, prove `A = A'` and `B = B'` as separate `have`s and chain `rw [hA, hB]`. `congr 1` doesn't split through outer `LinearMap.comp`.

- **(NEW session 9) `extendL0'IsoToE'` block-extension pattern.** Build `E' ≃ E'` extending an `L0' ≃ L0'` iso by `id` on `L1'` via `prodEq.symm ≪≫ₗ (refl × h) ≪≫ₗ prodEq`, where `prodEq := L1'.prodEquivOfIsCompl L0' isCompl`. The pointwise `d.symm e' = (projL1' e' + h.symm (projL0' e') : E')` formula falls out; `projL1' ∘ d.symm = projL1'` and `projL0' ∘ d.symm = h.symm ∘ projL0'` are the two key bridge lemmas.

- **(NEW session 9) `lean_leansearch` natural language >> `lean_loogle` structural** (REINFORCED). `lean_loogle "LinearEquiv.prod"` returned No results; `lean_leansearch "LinearEquiv.prodCongr two linear equivs M ≃ N -> P ≃ Q -> M × P ≃ N × Q"` returned the right hit on first query. Already documented; reaffirmed this round.

## Recommendations for next session

See `recommendations.md` for the prioritised next-round queue. Briefly:
- **Round 8 single-objective:** close `pNormalForm_witnesses` body (line 216) — the single isolated sorry remaining in NormalForm.lean. Use the four-step plan in the theorem's docstring.
- **Round 8 secondary objectives** (independent of Round 8 primary):
  - close `parabolic_decompose` (Slice.lean line 1089) — Round 6 deferred, three sub-constructions per `informal/levi.md §6.6`. **Optional** unless downstream needs it.
  - close `sIndependenceAndOrbitCriterion` (Orbits.lean lines 358 + 376) — Round 8 plan, two scoped sorries (forward + reverse), needs added hypotheses (`Nondegenerate`, `(2 : F) ≠ 0`, `Sₕ`-equality). Now structurally unblocked because `pNormalForm_residual_orbit_iso` is sorry-free.
