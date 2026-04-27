# Session 5 — Prover Round 3 (Tier S #1 statement correction, two coupled provers)

## Metadata

- **Session:** 5 (stage `prover`, Round 3 — focused two-file dispatch).
- **Sorry count (declaration-use warnings) before round:** 9
  - `X0Geometry.lean`: 0 (closed in session 4) ✅
  - `Slice.lean`: 2 (`parametrizeX0PlusU_existence` line 232, `uD_isParabolic` line 442 — both Tier D)
  - `NormalForm.lean`: 6 (`pNormalForm_witnesses` 196, `pNormalForm` 237 — Tier-D inheritance only, `residual_levi_extract` 307, `residual_levi_build` 336, `kernelImage_ker` 482, `kernelImage_im` 577)
  - `Orbits.lean`: 1 (`sIndependenceAndOrbitCriterion` line 242 — Tier A deferred)
- **Sorry count (declaration-use warnings) after round:** **7** ✅ (−2)
  - `X0Geometry.lean`: 0 (unchanged)
  - `Slice.lean`: 1 (`parametrizeX0PlusU_existence` line 232 — Tier D, untouched; **`uD_isParabolic` resolved** ✅)
  - `NormalForm.lean`: 5 (`pNormalForm_witnesses` line 210, `residual_levi_extract` line 330, `residual_levi_build` line 363, `kernelImage_ker` lines 537+543, `kernelImage_im` line 595; **`pNormalForm` resolved** ✅)
  - `Orbits.lean`: 1 (unchanged)
- **Net change:** 9 → 7 declaration warnings (−2). Both closed sorries are direct effects of Tier S #1 statement correction landing.
- **Custom axioms introduced:** 0. `lean_verify InducedOrbitToy.Slice.uD_isParabolic` reports `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no custom axioms.
- **Build status:** `lake build` green at end of round (8033 jobs replayed/built; 7 sorry warnings + 1 pre-existing unused-variable lint at `X0Geometry.lean:221`).
- **Pre-processed log:** 91 events (summary line + 90), 6 edits across 2 files, 1 explicit `lean_goal` check, 5 diagnostic checks, 5 lemma searches (3 `lean_loogle`, 2 `lean_local_search` — one failed because Lean project path not yet set), 0 `lean_build` calls (lake invoked via `Bash` instead), 7 `lean_multi_attempt` invocations during the Slice prover's `linear_combination` iteration.

## Process observation

The plan agent assigned exactly **two** files for this round (Slice.lean + NormalForm.lean — the two halves of Tier S #1), but the harness still dispatched provers to all six files. Outcomes match the documented protocol:

- **Slice.lean prover** (Tier S #1 half 1): edited statement of `uD_isParabolic`, discharged the now-true scoped `sorry` at line 460, **2 → 1** declaration warning. Used `lean_multi_attempt` ~7 times to converge on the right `simp only` argument list and the right ε-symmetry-based `linear_combination` coefficients.
- **NormalForm.lean prover** (Tier S #1 half 2): edited definition of `IsParabolicElement` (4th conjunct: `IsAdjointPair p p` → `LinearMap.IsOrthogonal p`), closed the Tier-D inheritance sorry at line 272 of `pNormalForm`, **6 → 5** declaration warnings. Verified the calc-chain proof structure independently via `lean_run_code` before the cross-file dependency landed.
- **Basic.lean, LocalForms.lean, Orbits.lean, X0Geometry.lean provers**: all four correctly identified that no work was assigned; verified isolation-compile, wrote brief "no work" task_results files, made no edits.

The expected mid-round build break (NormalForm uses corrected `uD_isParabolic` shape before Slice lands its half) was observed and resolved automatically when the sister prover finished. End-of-round `lake build` is green.

## Target 1 — `InducedOrbitToy/Slice.lean :: uD_isParabolic` (2 → 1 declaration warning) ✅ RESOLVED

### Statement edit (line 426 region)

Changed the `IsAdjointPair` conjunct of `uD_isParabolic` from
`IsAdjointPair B B (uD S D) (uD S D)` (self-adjoint, **false in general**)
to
`IsAdjointPair B B (uD S D) (uD S (-D))` (isometry, **true**).

The two flag-preservation conjuncts (`Submodule.map (uD D) S.flagE ≤ S.flagE`, `Submodule.map (uD D) S.flagEV0 ≤ S.flagEV0`) are unchanged and remain proven.

Docstring updated to reflect the correct semantics: "`u_D` is parabolic: it is an isometry of the ambient form and preserves the flag…"

### Proof of the IsAdjointPair conjunct (lines 449–467)

```lean
intro x y
obtain ⟨e₁, v₁, e₁'⟩ := x
obtain ⟨e₂, v₂, e₂'⟩ := y
rw [uD_apply S D e₁ v₁ e₁', uD_apply S (-D) e₂ v₂ e₂', Cdual_neg]
simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, LinearMap.map_add,
  LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply,
  smul_eq_mul, LinearMap.neg_apply, LinearMap.map_neg, neg_neg]
rw [Cdual_pairing_eq S _hNondeg D v₁ e₂',
    Cdual_pairing_eq S _hNondeg D (D e₁') e₂',
    Cdual_pairing_eq S _hNondeg D v₂ e₁',
    Cdual_pairing_eq S _hNondeg D (D e₂') e₁']
have hε := S.epsSymm
have hε2 : S.eps * S.eps = 1 := by rcases S.epsValid with h | h <;> simp [h]
have hC : S.formV0 v₂ (D e₁') = S.eps * S.formV0 (D e₁') v₂ := hε _ _
have hD' : S.formV0 (D e₂') (D e₁') = S.eps * S.formV0 (D e₁') (D e₂') := hε _ _
linear_combination
  (-S.eps) * hC + (S.eps * (2 : F)⁻¹) * hD'
    + (S.formV0 (D e₁') (D e₂') * (2 : F)⁻¹ - S.formV0 (D e₁') v₂) * hε2
```

### Mathematical derivation

After `uD_apply` on both sides and `Cdual_pairing_eq` on all four `λ(Cdual D ·, ·)` atoms, set
`A := B₀(D e₁', D e₂')`, `B := B₀(D e₁', v₂)`, `C := B₀(v₂, D e₁')`, `D' := B₀(D e₂', D e₁')`.
The LHS − RHS reduces to `−A/2 + B − ε·C + (ε/2)·D'`. ε-symmetry `C = ε·B`, `D' = ε·A`, then `ε² = 1`, gives `(1 − ε²)·(B − A/2) = 0`. The `linear_combination` coefficients `(−ε)·hC, (ε/2)·hD', (A/2 − B)·hε2` produce exactly this cancellation; `ring` closes the residual.

### Attempts trail (7 `lean_multi_attempt` iterations)

| Attempt | What was tried | Outcome |
|---|---|---|
| 1 | `obtain ⟨…⟩; rw [uD_apply S D ..., uD_apply S (-D) ..., Cdual_neg]` then `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply]` | Goal still has unsimplified `LinearMap.add_apply` / `LinearMap.map_smul` shapes — needs broader simp set. |
| 2 | Add `LinearMap.map_add, LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul` | Closer; `λ(D ·, ·) ` atoms remain (no `Cdual_pairing_eq` applied yet). |
| 3 | Add `LinearMap.neg_apply, LinearMap.map_neg, neg_neg` to handle `Cdual_neg`-induced negations | Now reduces to scalar identity — but `linear_combination` without ε-symmetry hints fails to close. |
| 4 | Introduce `hε := S.epsSymm`, `hε2`, then `linear_combination` with naive coefficients (`hε * 0`) | Residual `≠ 0` — coefficients wrong. |
| 5 | Iterate on coefficients via `lean_multi_attempt` exploration | Several tries close once the right linear combination of `hC`, `hD'`, `hε2` is found. |
| 6 | Final form with `(-S.eps) * hC + (S.eps * (2 : F)⁻¹) * hD' + (A/2 − B) * hε2` | ✅ Closes; `ring`-norm satisfied. |
| 7 | `lake env lean InducedOrbitToy/Slice.lean` | Only line 232 sorry warning remains. End-of-round `lake build` green. |

### Anti-patterns explicitly avoided

- Did **not** use `field_simp` (would leave `1 + 1 = 2` per Round-3 PROGRESS.md gotcha).
- Did **not** introduce term-mode `sorry`.
- Did **not** use the private `Cdual_pairing` (lives at line 478, out of scope at line 442) — used `Cdual_pairing_eq` (line 78, in scope).
- Did **not** rely on `eps_sq_eq_one` (also defined later); inlined the two-line `rcases S.epsValid with h | h <;> simp [h]`.
- Did **not** modify any other sorry-free declaration (helpers `XCB_apply`, `XST_apply`, `uD_apply`, `uD_conj_XCB`, `Cdual_pairing_eq` signatures unchanged).

## Target 2 — `InducedOrbitToy/NormalForm.lean :: pNormalForm` (6 → 5 declaration warnings) ✅ RESOLVED

### Statement edit: `IsParabolicElement` definition (line 85)

Changed 4th conjunct:
```diff
- LinearMap.IsAdjointPair S.ambientForm S.ambientForm p p
+ LinearMap.IsOrthogonal S.ambientForm p
```

Updated docstring: "`p` is an isometry of the ambient form (`LinearMap.IsOrthogonal S.ambientForm p`), matching the `IsometryEnd` shape used in `Orbits.lean`".

### Proof of the IsOrthogonal conjunct in `pNormalForm` (lines 270–284)

```lean
· -- LinearMap.IsOrthogonal S.ambientForm (uD S D)
  intro u v
  have hAdj :
      LinearMap.IsAdjointPair S.ambientForm S.ambientForm
          (uD S D) (uD S (-D)) :=
    (uD_isParabolic S _hNondeg _hChar D).1
  have hinv : uD S (-D) ∘ₗ uD S D = LinearMap.id := by
    have := uD_neg_inverse S _hNondeg _hChar (-D)
    simpa [neg_neg] using this
  have hinv_apply : ∀ w, uD S (-D) (uD S D w) = w := by
    intro w
    have := congrArg (fun f : Module.End F S.V => f w) hinv
    simpa using this
  calc S.ambientForm (uD S D u) (uD S D v)
      = S.ambientForm u (uD S (-D) (uD S D v)) := hAdj u (uD S D v)
    _ = S.ambientForm u v := by rw [hinv_apply]
```

### Pre-landing structure verification

Before the sister Slice.lean prover landed its corrected `uD_isParabolic` statement, the NormalForm prover ran the proof shape against a hypothetical input via `lean_run_code`:

```lean
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (f g : Module.End R M)
    (hAdj : LinearMap.IsAdjointPair B B f g)
    (hinv_apply : ∀ w, g (f w) = w) :
    LinearMap.IsOrthogonal B f := by
  intro u v
  calc B (f u) (f v)
      = B u (g (f v)) := hAdj u (f v)
    _ = B u v := by rw [hinv_apply]
```

✅ no diagnostics. The proof structure is sound; the only dependency is the (concurrent) Slice statement edit, which landed before round end.

### Mid-round cross-file dependency (expected)

`lake env lean InducedOrbitToy/NormalForm.lean` reported during NormalForm-but-pre-Slice window:

```
Type mismatch
  (uD_isParabolic S _hNondeg _hChar D).left
has type   IsAdjointPair B B ⇑(uD S D) ⇑(uD S D)
expected   IsAdjointPair B B ⇑(uD S D) ⇑(uD S (-D))
```

Per PROGRESS.md "Coordination notes for Round 3 (parallel-safety)", this was correctly identified as an expected, transient cross-file mismatch that resolves when the sister prover lands. End-of-round `lake build` is green.

### `residual_levi_build` comment-only edit (line 348)

Inline comment updated to remove the now-stale Tier-D inheritance reference. Body unchanged (still bare sorry, still Tier A + Tier S #3).

### Side-effect review of every `IsParabolicElement` consumer

After the definition change:

- `pNormalForm` (line 236) — produces `IsParabolicElement`; isometry conjunct closed in body (above).
- `residual_levi_extract` (line 321) — consumes via `_hP`; underscore-prefixed binding doesn't dispatch on field structure. ✅ no change needed.
- `residual_levi_build` (line 348) — produces in existential conclusion; body is whole-statement `sorry`. ✅ no change needed.
- `pNormalForm_residual_orbit_iso` (line 388) — uses in iff statement; body delegates to `residual_levi_extract` / `residual_levi_build`. ✅ no change needed.

All four compile after the definition edit.

### Reusable proof-structure pattern (NEW)

**Adjoint-pair → orthogonal via paired inverse**: when you have an `IsAdjointPair B B f g` and `g ∘ f = id`, you get `IsOrthogonal B f` via the calc chain `B (f u) (f v) = B u (g (f v)) = B u v`. The intermediate `hinv_apply : ∀ w, g (f w) = w` is reached via `congrArg (· w) hinv` + `simpa`. Verified independently with `lean_run_code` before the cross-file dependency landed — useful template for future "convert pair-adjoint to orthogonal" rewrites.

## Target 3 — `InducedOrbitToy/Basic.lean` (0 → 0 sorries) ✅ NO WORK

Verified `lake env lean InducedOrbitToy/Basic.lean` produces no output. No edits made. Result file written for transparency.

## Target 4 — `InducedOrbitToy/LocalForms.lean` (0 → 0 sorries) ✅ NO WORK

Verified `lean_diagnostic_messages` returns 0 errors, 0 warnings. No edits made.

## Target 5 — `InducedOrbitToy/X0Geometry.lean` (0 → 0 sorries) ✅ NO WORK

Verified compilation produces only the pre-existing `unused variable hlambda` lint at line 221 (intentional per autoformalised statement of `sDual_restrict_ker_isIso`; do not remove). No edits.

## Target 6 — `InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion` (1 → 1 declaration warning) ✅ NO WORK

Verified `lean_diagnostic_messages` reports the single existing sorry warning at line 242. No edits made. Cross-file Tier S #1 refactor (IsParabolicElement / uD_isParabolic) does **not** propagate into Orbits.lean (the file's references to Slice.lean and NormalForm.lean are type/structure-level only, not predicate-consumption). After sister provers landed, end-of-round `lake build` for Orbits.lean is green.

## Key findings

1. **Tier S #1 closes 2 sorries with one signature edit each.** The mathematical core was already known (Slice prover used the same toolkit as `uD_conj_XCB`, NormalForm prover used a 16-line calc chain). The only blocker was the false statement.
2. **Cross-file parallel-safety actually works.** The PROGRESS.md "Coordination notes for Round 3" predicted the mid-round break would resolve when both sister provers landed; both provers correctly noted the transient mismatch and proceeded; end-of-round build is green.
3. **`lean_run_code` is a strong pre-validation tool for cross-file changes.** The NormalForm prover verified the proof shape in isolation with hypothetical inputs before the cross-file dependency was available — eliminating uncertainty about whether the local proof was sound.
4. **`linear_combination` exploration via `lean_multi_attempt` is efficient.** Once the goal reduces to a polynomial identity in `λ`, `B₀`, `ε`, the right ε-symmetry coefficients can be reached in 5–7 attempts with the multi-attempt MCP tool, no manual algebra needed beyond the structural setup.

## Anti-patterns confirmed (do not repeat)

- `field_simp` on `(2 : F)⁻¹ + (2 : F)⁻¹ = 1` leaves `1 + 1 = 2` residual (Round 2 finding, re-confirmed this round in the Slice prover's anti-pattern notes).
- Private declarations (e.g. `Cdual_pairing` at line 478) are not in scope at earlier line numbers; use the public alternative (`Cdual_pairing_eq` at line 78) plus the `_hNondeg` hypothesis.
- `obtain ⟨a, b, c⟩ := <existential>` makes destructured fields opaque (session 4 finding); avoided this round.

## Recommendations for next session

See `recommendations.md` in this folder. Headline: **Round 4 should attack Tier A** (Levi-action machinery in Slice.lean, ≈60–100 lines additive code) plus **Tier S #2 / #3 statement fixes** (UnipotentRadical skew-adjoint tightening, SliceSetup Lagrangian condition). After both land, 5 of the 7 remaining sorries close mechanically.
