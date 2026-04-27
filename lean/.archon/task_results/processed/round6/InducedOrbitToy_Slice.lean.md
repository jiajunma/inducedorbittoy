# InducedOrbitToy/Slice.lean — Round 6 (Levi machinery)

**Result: IN PROGRESS** — helpers 1–7 RESOLVED (sorry-free); helper 8
(`parabolic_decompose`) DEFERRED to Round 7 with sorry + documented gap.

End-of-round state:
- `lake env lean InducedOrbitToy/Slice.lean` — compiles (no errors).
- `lake build` — green.
- Slice.lean declaration-use `sorry` warnings: **0 → 1** (new
  `parabolic_decompose` only).
- NormalForm.lean / Orbits.lean sorries: **unchanged** (3 + 1, lines
  195/319/348/324). ✓ Round-6 acceptance criterion.
- Total declaration-use `sorry` warnings: **4 → 5** (additive only). ✓

Axiom audit (all 14 newly-added declarations via `#print axioms` on
`/tmp/check_axioms_slice.lean`):
- `lambdaDualE`, `lambdaDualE_pairing_eq`, `lambdaDualE_id`,
  `lambdaDualE_comp` — `[propext, Classical.choice, Quot.sound]`.
- `leviGL_E`, `leviGL_V0`, `leviGL_E_apply`, `leviGL_V0_apply` — same.
- `leviGL_E_symm_inverse`, `leviGL_V0_symm_inverse` — same.
- `leviGL_E_isParabolic`, `leviGL_V0_isParabolic` — same.
- `leviGL_E_conj_XCB`, `leviGL_V0_conj_XCB` — same.

**No custom axioms introduced.**

## Definitions added (Section 6.1–6.2)

### `lambdaDualE` (line ~696, post-`uD_conj_XCB`)
- **Approach:** Mirror the existing `Cdual` construction (line 71).
  Define `lambdaDualE S g e := S.lambda.toPerfPair.symm (g.dualMap (S.lambda e))`.
  The inner `g.dualMap (S.lambda e) : Module.Dual F S.E'` is a linear
  functional on `S.E'`; the outer perfect-pairing inverse lifts it to `S.E`.
- **Key Mathlib lemmas:** `LinearMap.dualMap`, `LinearMap.dualMap_apply`,
  `LinearMap.IsPerfPair.toPerfPair`, `LinearMap.apply_symm_toPerfPair_self`.
- **Result:** RESOLVED.

### `lambdaDualE_pairing_eq` (defining identity)
- **Approach:** Same `show` + `rw [apply_symm_toPerfPair_self]` + `simp [dualMap_apply]`
  pattern as `Cdual_pairing_eq` (line 78).
- **Result:** RESOLVED.

### `lambdaDualE_id`
- **Approach:** Pair both sides with arbitrary `e'` via
  `S.paired.isPerfect.1` (left injectivity of perfect pairing); then
  `lambdaDualE_pairing_eq` reduces both sides to `S.lambda e e'`.
- **Result:** RESOLVED.

### `lambdaDualE_comp`
- **Approach:** Same `S.paired.isPerfect.1` template. After `show`-ing
  `(g₁ ∘ₗ g₂)`'s `lambdaDualE` equals the nested form, three
  `lambdaDualE_pairing_eq` rewrites + `rfl` close the goal.
- **Initial dead end:** Without the `show` step, `rw` couldn't match
  `lambdaDualE_pairing_eq` on the RHS because the composition `(f ∘ₗ g) e`
  was opaque. Fixed by `show`-ing the goal in nested-application form.
- **Result:** RESOLVED.

### `lambdaDualE_symm_comp` / `lambdaDualE_comp_symm` (private helpers)
- **Approach:** Use `lambdaDualE_comp` to fold compositions, then
  `lambdaDualE_id` on the trivialised inner.
- **Result:** RESOLVED.

### `leviGL_E` / `leviGL_V0` (block-diagonal embeddings)
- **Approach:** Direct block-matrix definitions via `LinearMap.inl`,
  `LinearMap.inr`, `LinearMap.fst`, `LinearMap.snd` projections/embeddings.
  `leviGL_E d` acts as `((d⁻¹)^∨, id, d)` on `E × V0 × E'`;
  `leviGL_V0 g` as `(id, g, id)`. Definitions follow the informal
  `levi.md §6.2` exactly.
- **Note:** `leviGL_V0` does NOT depend on the isometry hypothesis on `g`.
  Per `levi.md` side note, only the parabolicity proof needs it. This
  avoids the Round-5 subtype-wrapping anti-pattern.
- **Result:** RESOLVED (definitions). `_apply` lemmas RESOLVED via
  `unfold` + `simp`.

### `leviGL_E_symm_inverse` / `leviGL_V0_symm_inverse`
- **Approach:** `LinearMap.ext` + `Prod.mk.injEq` to component-split, then
  `congrArg` on `lambdaDualE_comp_symm` for the E-block, `simp` for the rest.
- **Key insight:** `d.symm.symm = d` is `rfl` for `LinearEquiv` (via
  Mathlib's `LinearEquiv.symm_symm`), so applying
  `leviGL_E_symm_inverse S d.symm` gives the other-direction inverse for
  free. Used in `leviGL_E_isParabolic` IsUnit conjunct.
- **Result:** RESOLVED.

## Section 6.4 — Parabolicity

### `leviGL_E_isParabolic`
- **Approach:** Statement unfolds `IsParabolicElement S` (defined in
  NormalForm.lean, downstream — so unfolded as 4-conjunct `IsUnit ∧
  Submodule.map = ∧ Submodule.map = ∧ IsOrthogonal`). The four conjuncts:
  - **IsUnit:** `Units.mkOfMulEqOne` on the symm inverse (with `d.symm`
    twice for the other-direction inverse via `d.symm.symm = d` rfl).
  - **flagE preservation:** `le_antisymm` + standard `rintro` patterns;
    forward inclusion uses `leviGL_E_apply` + `simp`; backward uses
    `lambdaDualE_symm_comp` to invert.
  - **flagEV0 preservation:** Same template.
  - **IsOrthogonal:** `simp only [SliceSetup.ambientForm,
    LinearMap.mk₂_apply]` to expand the bilinear form, then
    `lambdaDualE_pairing_eq` rewrites both `λ` atoms, `simp` closes via
    `d.symm (d _) = _`.
- **Result:** RESOLVED.

### `leviGL_V0_isParabolic`
- **Approach:** Same template as `leviGL_E_isParabolic`. The IsOrthogonal
  conjunct uses the isometry hypothesis `hg : ∀ u v, S.formV0 (g u) (g v) = S.formV0 u v`
  via `rw [hg]`.
- **Result:** RESOLVED.

## Section 6.5 — Conjugation transformation

### `lambdaDualE_Cdual` (private helper)
- **Statement:** `lambdaDualE S g (Cdual S C v) = Cdual S (C ∘ₗ g) v`.
- **Approach:** Pair both sides with `e''` via `S.paired.isPerfect.1`,
  reduce LHS via `lambdaDualE_pairing_eq` then `Cdual_pairing` (no-Nondeg
  variant), reduce RHS via `Cdual_pairing` + `LinearMap.comp_apply`.
- **Result:** RESOLVED.

### `leviGL_E_conj_XCB`
- **Approach:** Component-split via `Prod.mk.injEq`. E-component uses
  `lambdaDualE_Cdual` and `LinearMap.map_add`; V0-component is a direct
  `simp [comp_apply]`; E'-component is trivially 0 = 0.
- **Result:** RESOLVED.

### `leviGL_V0_conj_XCB`
- **Approach:** Same template. The hypothesis `hgC` had to be stated
  carefully to bridge the LinearEquiv FunLike (`g v`) with the LinearMap
  FunLike (`(g : V0 →ₗ V0) (C e'')`). Final form:
  `S.formV0 (g v) ((g : S.V0 →ₗ[F] S.V0) (C e'')) = S.formV0 v (C e'')`.
- **Initial dead end (10 min):** Stated `hgC` symmetrically with `g`-FunLike
  on both sides, but the `Cdual_pairing` rewrite produces `(g : V0 →ₗ V0)
  (C e'')` (LinearMap-coerced) on the second arg. The asymmetric
  statement matches the goal exactly.
- **Result:** RESOLVED.

## Section 6.6 — Levi/unipotent decomposition (DEFERRED)

### `parabolic_decompose` (line 1078)
- **Statement:** Adapted to take 4 unfolded conjuncts of
  `IsParabolicElement` (since `IsParabolicElement` lives in NormalForm.lean,
  downstream). Round 7's NormalForm consumer destructs
  `IsParabolicElement` and passes the 4 components.
- **Approach attempted:** Outline only; left as `sorry` with explanatory
  comment block (24 lines preceding the theorem).
- **Gap:** The full proof requires three substantive sub-constructions
  per `levi.md §6.6`:
  - **(a) `g₀` extraction** via descent of `p` to the quotient
    `flagEV0 / flagE ≃ V0` (~30 lines: define quotient module action,
    show it's bijective, bridge through `Submodule.quotientEquivOfIsCompl`).
  - **(b) `(d⁻¹)^∨` extraction** from `Submodule.map p S.flagE = S.flagE`
    (~25 lines: restrict `p` to `flagE`, transfer through `flagE ≃ E`,
    invert `lambdaDualE` via `lambdaDualE_pairing_eq` + perfect pairing).
  - **(c) Residual `D`** via
    `parametrizeX0PlusU_existence`/`parametrizeX0PlusU_uniqueness` applied
    to `p ∘ₗ (leviGL_E d ∘ₗ leviGL_V0 g)⁻¹` (~30 lines: prove this
    composition is in `UnipotentRadical S`, apply `existence` to extract
    `(C, B)`, identify `C = D` and `B = 0` via the third (skewness)
    conjunct).
- **Result:** DEFERRED — explicit `sorry` with documented 3-step roadmap
  in the file's `/-** Gap: ... -/` block.
- **Round 7 plan:** Either close `parabolic_decompose` here (additively
  in `Slice.lean`, ~85 lines) OR work around it for `residual_levi_extract`
  only — the consumer can use `parametrizeX0PlusU_uniqueness` +
  `leviGL_E_isParabolic` directly (per `levi.md` line 240) without
  needing the full Levi/unipotent decomposition.

### Why deferred (per PROGRESS.md stop conditions)
- The `lambdaDualE_*`, `leviGL_*_apply`, `leviGL_*_symm_inverse`, all 4
  conjuncts of both `_isParabolic` lemmas, and both `_conj_XCB` lemmas
  consumed the bulk of the round budget (helpers 1–7 priority per
  `PROGRESS.md` lines 142–144).
- Per the PROGRESS.md stop condition: "If `parabolic_decompose` proves
  intractable: stop and report. Do NOT spend more than ~30% of the round
  budget on it; helpers 1–7 are the priority."

## Mathlib lemmas used (new this round)

- `LinearMap.dualMap`, `LinearMap.dualMap_apply` — for `lambdaDualE`.
- `LinearMap.IsPerfPair.toPerfPair`, `LinearMap.apply_symm_toPerfPair_self`
  — already used by `Cdual`; reused here.
- `Units.mkOfMulEqOne` — IsUnit witnesses (Round 4 carry-forward).
- `LinearEquiv.symm_apply_apply` — `g.symm (g v) = v` (used in
  `leviGL_V0_symm_inverse` and the `simp` cleanups).
- `LinearMap.comp_apply` — composition unfolding throughout.

## Lessons learned (carry forward to Round 7+)

- **`d.symm.symm = d` is `rfl` for `LinearEquiv`.** This makes
  `leviGL_E_symm_inverse S d.symm` directly usable as the other-direction
  inverse, halving the inverse-proof work.
- **LinearEquiv FunLike vs LinearMap FunLike coercion mismatch in
  `rw` patterns.** Even though `g v = (g : V →ₗ V) v` is `rfl`, `rw`
  pattern-matching is syntactic. When stating an isometry-style hypothesis
  used in `rw`, match the LinearMap-coerced form that appears in the goal
  after `LinearMap.comp_apply` rewrites. Specifically: if the second arg
  comes from `(g : V →ₗ V) ∘ₗ C` after `comp_apply`, state the hypothesis
  with `(g : V →ₗ V) (C e'')` rather than `g (C e'')`.
- **`show` to convert composed-form goals to nested-application form**
  before `rw`-ing perfect-pairing equations. Pattern: when the goal has
  `(f ∘ₗ g) e`, use `show ... = ... f (g e)` to make `rw` targets visible.
- **Block-matrix inverse via componentwise identity proofs.** The Levi
  proofs all use `Prod.mk.injEq .. |>.mpr ⟨?_, Prod.mk.injEq .. |>.mpr
  ⟨?_, ?_⟩⟩` to split into E/V0/E' components, then close each individually.
  Reusable for any `Module.End F (E × V0 × E')` proofs.
- **`leviGL_V0` definition takes only `g : V0 ≃ₗ V0`, no isometry
  bundled.** Avoids Round-5 subtype anti-pattern. Isometry hypothesis is
  passed separately at consumer sites (`leviGL_V0_isParabolic`,
  `leviGL_V0_conj_XCB`).

## Next steps (Round 7 prover for NormalForm.lean)

The 4 sorries in NormalForm.lean (lines 195, 319, 348) and the deferred
`parabolic_decompose` (Slice.lean line 1078) are now ready to consume.

**Recommended Round 7 sequencing:**
1. **`pNormalForm_witnesses` (NormalForm line 195)** — uses
   `leviGL_E_conj_XCB` (Slice 6.5) to align `(C, B)` to a Levi-normalised
   form, then `uD_conj_XCB` to clear the residual. Estimated ~50 lines.
2. **`residual_levi_extract` (NormalForm line 319)** — choose between:
   - **Option A:** Close `parabolic_decompose` first (~85 lines in
     Slice.lean), then use it directly (~10 lines in NormalForm).
   - **Option B:** Skip `parabolic_decompose`; work directly via
     `parametrizeX0PlusU_uniqueness` + `leviGL_E_isParabolic` (~40 lines
     in NormalForm). **Recommended.**
3. **`residual_levi_build` (NormalForm line 348)** — construct
   `d : E' ≃ₗ E'` from the iso `h : L0' ≃ₗ L0'` via
   `IsCompl L1' L0'`, then `p := leviGL_E d`. Estimated ~40 lines.

After Round 7 lands, only Orbits.lean line 324
(`sIndependenceAndOrbitCriterion`, Round 8) remains.

## File diff summary

- Slice.lean: lines 1–678 byte-for-byte unchanged. Lines 679–1093
  appended (~414 lines including comment headers).
- No other files edited.
