# InducedOrbitToy/Slice.lean

## Round 3 (prover) — Tier S #1 half 1: corrected `uD_isParabolic`

**Assigned objective**: change the `IsAdjointPair` conjunct of
`uD_isParabolic` from `IsAdjointPair B B (uD D) (uD D)` (self-adjoint,
**false**) to `IsAdjointPair B B (uD D) (uD (-D))` (isometry, **true**),
then discharge the (now-true) sorry at line 460.

### Result: RESOLVED

- Statement edited per `PROGRESS.md` Round 3 §1.
- The internal `IsAdjointPair` sorry is fully closed by ε-symmetry +
  `(2 : F)⁻¹ + (2 : F)⁻¹ = 1` toolkit (no new helper lemmas, no axioms).
- File compiles in isolation: `lake env lean InducedOrbitToy/Slice.lean`
  produces only the `parametrizeX0PlusU_existence` line 232 warning
  (Tier D, **untouched** as instructed).
- `lake build` is green at end of round (NormalForm.lean's half landed
  in parallel).
- `#print axioms uD_isParabolic` (via `lean_verify`):
  `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`.
- All previously sorry-free declarations untouched. Helpers
  `XCB_apply`, `XST_apply`, `uD_apply`, `uD_conj_XCB`,
  `Cdual_pairing_eq` signatures **unchanged**.

### Statement edit (lines 426–441)

Docstring updated to reflect the (correct) isometry semantics; the
4th-conjunct argument list went from `(uD S D) (uD S D)` to
`(uD S D) (uD S (-D))`. The two flag-preservation conjuncts are
unchanged.

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

### Mathematical derivation (verified by `linear_combination`)

Set abbreviations
`A := B₀(D e₁', D e₂')`, `B := B₀(D e₁', v₂)`,
`C := B₀(v₂, D e₁')`,    `D' := B₀(D e₂', D e₁')`.

After `uD_apply` on both sides and applying `Cdual_pairing_eq` to all
`λ(Cdual D ·, ·)` atoms, the LHS − RHS reduces to

```
−A/2 + B − ε·C + (ε/2)·D'.
```

Use ε-symmetry `C = ε·B`, `D' = ε·A`, then `ε² = 1` to obtain
`(1 − ε²)·(B − A/2) = 0`. The `linear_combination` coefficients
`(−ε)·hC, (ε/2)·hD', (A/2 − B)·hε2` give exactly this cancellation;
the residual is closed by `ring`.

### Mathlib lemmas used (none new)

- `LinearMap.mk₂_apply` — peels `SliceSetup.ambientForm` (a `mk₂`) into
  its underlying scalar formula `λ + B₀ + ε·λ`.
- `LinearMap.map_add`, `LinearMap.add_apply`, `LinearMap.map_smul`,
  `LinearMap.smul_apply`, `smul_eq_mul`, `LinearMap.neg_apply`,
  `LinearMap.map_neg`, `neg_neg` — distribute the bilinear form
  through the block-vector arithmetic emitted by `uD_apply`.
- `linear_combination` (with default `ring` norm) — close the final
  scalar identity.

### Anti-patterns avoided

- Did **not** use `field_simp` (would have left residual `1 + 1 = 2`).
- Did **not** introduce term-mode `sorry`.
- Did **not** modify any other sorry-free declaration.
- Did **not** use `private` `Cdual_pairing` (defined later in the file
  at line 478, so out of scope at line 442). Used the equivalent
  `Cdual_pairing_eq` (defined at line 78) with the in-scope `_hNondeg`
  hypothesis.
- Did **not** rely on `eps_sq_eq_one` (also defined later at line 511).
  Inlined the two-line `rcases S.epsValid with h | h <;> simp [h]`.

### Not touched (per `PROGRESS.md` instructions)

- `parametrizeX0PlusU_existence` (line 232) — Tier D, blocked on
  Tier S #2 (`UnipotentRadical` skew-adjoint tightening). Two internal
  scoped sorries at lines 256 (IsSkewB component) and 294 (E component
  of the equality) remain as left by the round-2 prover.
- All declarations before line 426 (`uD_neg_inverse`, `uD_apply`,
  `Cdual_neg`, `Cdual_pairing_eq`, `XCB_apply`, `X0Lift_apply`,
  `parametrizeX0PlusU_mem`, `parametrizeX0PlusU_uniqueness`,
  `Cdual`, `uD`, `XCB`, `XST`, `XST_apply`-helpers, `BST`, `CST`,
  `projL0'`, `projL1'`).
- All declarations after line 467 in the same block
  (`uD_isParabolic` flag-preservation conjuncts, `Cdual_pairing`,
  `Cdual_X0_apply`, `eps_sq_eq_one`, `uD_conj_XCB`).

### Final diagnostic

```
$ lake env lean InducedOrbitToy/Slice.lean
warning: InducedOrbitToy/Slice.lean:232:8: declaration uses `sorry`
```

```
$ lake build
⚠ [8028/8033] Replayed InducedOrbitToy.Slice
warning: InducedOrbitToy/Slice.lean:232:8: declaration uses `sorry`
⚠ [8029/8033] Built InducedOrbitToy.NormalForm (10s)
warning: InducedOrbitToy/NormalForm.lean:195:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:319:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:348:16: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:495:8: declaration uses `sorry`
warning: InducedOrbitToy/NormalForm.lean:590:8: declaration uses `sorry`
✔ [8030/8033] Built InducedOrbitToy.LocalForms (8.2s)
⚠ [8031/8033] Built InducedOrbitToy.Orbits (10s)
warning: InducedOrbitToy/Orbits.lean:242:8: declaration uses `sorry`
✔ [8032/8033] Built InducedOrbitToy (7.9s)
Build completed successfully (8033 jobs).
```

End-of-round sorry counts:
- Slice.lean: **1** declaration-use warning (was 2; `uD_isParabolic`
  closed). Two internal scoped sorries inside
  `parametrizeX0PlusU_existence` are unchanged.
- NormalForm.lean: 5 (was 6; sister prover landed its half — Tier D
  inheritance sorry in `pNormalForm` closed).
- Orbits.lean: 1 (unchanged, blocked).

### Summary

| Sorry | Status before round 3 | Status after round 3 |
|---|---|---|
| `uD_isParabolic` IsAdjointPair (line 460) | scoped sorry, statement was self-adjoint (false) | **CLOSED** — statement corrected to isometry-pair, proof via `Cdual_pairing_eq` + ε-symmetry + ε² = 1 |
| `parametrizeX0PlusU_existence` E-component (line 256) | scoped sorry (Tier D) | unchanged (not assigned this round) |
| `parametrizeX0PlusU_existence` IsSkewB (line 294) | scoped sorry (Tier D) | unchanged (not assigned this round) |

Net work: **1 sorry closed**, 1 statement corrected, **0 axioms
introduced**, 0 helper lemmas added (all toolkit was already in scope).

### Next steps (for plan agent)

- Round 4: address Tier S #2 (`UnipotentRadical` skew-adjoint) which
  unblocks `parametrizeX0PlusU_existence`'s two internal sorries.
- The `Cdual_pairing` (private, line 478) and `Cdual_pairing_eq` (line
  78) duplicate each other up to the `_hNondeg` hypothesis; future
  rounds may want to consolidate them. Out of scope here.
