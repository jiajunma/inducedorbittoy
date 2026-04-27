# Recommendations for Session 6

## Snapshot

- **Build state:** `lake build` is green; **7** declaration-use `sorry` warnings remain (down from 9 at end of session 4).
- **Custom axioms:** 0. `lean_verify InducedOrbitToy.Slice.uD_isParabolic` reports `[propext, Classical.choice, Quot.sound]`. All other public theorems still depend only on these; `sorryAx` appears only on declarations that still embed an explicit `sorry`.
- **Net session-5 progress:** 9 → 7 declaration sorries (−2). Both closed sorries are direct effects of the Tier S #1 statement correction landing.

## What actually shipped this round

| File | Δ declaration sorries | Net assessment |
|---|---|---|
| `Basic.lean` | 0 → 0 | No-op (verified clean). |
| `LocalForms.lean` | 0 → 0 | No-op (verified clean). |
| `X0Geometry.lean` | 0 → 0 | No-op (verified clean; pre-existing line-221 unused-variable lint is intentional). |
| `Slice.lean` | 2 → 1 ✅ | **`uD_isParabolic` resolved.** Statement fixed (4th conjunct: `(uD D, uD D)` → `(uD D, uD (-D))`); proof discharged via `Cdual_pairing_eq` + ε-symmetry + `linear_combination`. |
| `NormalForm.lean` | 6 → 5 ✅ | **`pNormalForm` resolved.** `IsParabolicElement` definition updated (4th conjunct: `IsAdjointPair p p` → `LinearMap.IsOrthogonal p`); the line-272 inheritance sorry closed via 16-line calc chain combining the corrected `uD_isParabolic` with `uD_neg_inverse`. |
| `Orbits.lean` | 1 → 1 | No-op (Tier A deferred; cross-file Tier S #1 refactor does not propagate). |

## Priority queue for next plan iteration

### Tier S — Plan-agent-only work (statement corrections still pending)

These remain **out of scope for any prover** and must be addressed by the plan agent issuing statement-level corrections.

1. **`InducedOrbitToy/Basic.lean :: UnipotentRadical`** (Tier S #2)
   - Tighten the predicate to enforce skew-adjointness w.r.t. `S.ambientForm`. The current loose flag-preserving Lie-algebra version is mathematically too weak: a generic `Y ∈ UnipotentRadical` does *not* satisfy the V₀→E ↔ E'→V₀ block-symmetry that `parametrizeX0PlusU_existence` demands.
   - **Impact:** unblocks `Slice.lean :: parametrizeX0PlusU_existence` line 232 — closes both internal scoped sorries (line 256 `IsSkewB` component and line 294 E component).

2. **`SliceSetup` (likely on a derived structure to avoid breaking instances)** (Tier S #3)
   - Add a Lagrangian-pair condition `L0_paired : IsPaired paired.pairing L0 L0'` (alongside the existing weaker `L0_isotropic`). The `IsPaired → IsPerfPair` upgrade on `L0 × L0'` is required for:
     - `kernelImage_ker` (NormalForm.lean line 537/543 — needs `λ(L1, L0') = 0`),
     - `kernelImage_im` (NormalForm.lean line 595 — same condition),
     - `residual_levi_build` (NormalForm.lean line 363 — needs the perfect-pairing dual `(h⁻¹)^∨ : L0 → L0`).
   - **Impact:** unblocks 3 Tier-A / Tier-C sorries (residual_levi_build, kernelImage_ker, kernelImage_im).

3. **`InducedOrbitToy/NormalForm.lean :: kernelImage_ker` signature** (Tier S #4)
   - Re-type `Sₕ` from `LinearMap` to `LinearEquiv` at the call site (already done in `kernelImage_im` and `kernelImage_dim`; remaining is `kernelImage_ker`).
   - **Impact:** unblocks the `Sₕ`-injectivity step in `kernelImage_ker`.

### Tier A — Highest priority for next prover round (provable now, additive infrastructure)

These are blocked only by **adding new infrastructure**, not by statement fixes. Each is a focused, mechanical addition to `Slice.lean`.

4. **Add Levi-action machinery to `Slice.lean`** (≈60–100 additive lines):
   - `leviGL_E : (S.E' ≃ₗ[F] S.E') →* Module.End F S.V` — block-diagonal embedding of `GL(E')`.
   - `leviGL_V0 : (S.V0 ≃ₗ[F] S.V0) →* Module.End F S.V` — same for `GL(V0)`.
   - `levi_conj_XCB` lemma: action on parameters per blueprint lines 277–278:
     `m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` for `m = leviGL_E d ∘ leviGL_V0 g₀`.
   - **Impact:** unblocks `pNormalForm_witnesses` (NormalForm.lean line 210) and `residual_levi_extract` (line 330).
   - **Strict additivity required**: the `XCB_apply`, `XST_apply`, `uD_apply` signatures are load-bearing for `pNormalForm`'s assembly. Add new lemmas, do not refactor existing ones.

5. **Discharge `pNormalForm_witnesses`** (NormalForm.lean line 210) — once item 4 lands:
   - Choose `d ∈ GL(E')` so `d(L0') = ker Cbar` (uses `_hRank`).
   - Choose `d|_{L1'}` so the resulting `Cbar|_{L1'}` matches the iso induced by `Sₕ` (uses surjectivity of `Cbar`).
   - `D := X0⁻¹ on (C - CST Sₕ)` (uses surjectivity of `X0` onto `range X0` plus a section choice via `Vplus`-complement).
   - **Estimated effort:** ~50 additive lines.

6. **Discharge `residual_levi_extract`** (NormalForm.lean line 330) — needs item 4 plus a *Levi-decomposition* lemma `parabolic_decompose : ∀ p, IsParabolicElement S p → ∃ D m, p = uD D ∘ leviGL m`. **Estimated effort:** ~30 lines for the decomposition lemma + ~20 lines for the helper.

7. **Discharge `residual_levi_build`** (NormalForm.lean line 363) — needs Tier S #3 (Lagrangian condition) plus item 4 (Levi machinery). **Estimated effort:** ~40 lines once both upstreams land.

### Tier C — Provable after Tier S #3 + #4

8. **`kernelImage_ker`** (NormalForm.lean lines 537+543, 2 internal scoped sorries) — needs Tier S #3 (Lagrangian) + Tier S #4 (`Sₕ` as `LinearEquiv`).

9. **`kernelImage_im`** (NormalForm.lean line 595) — needs Tier S #3 (Lagrangian).

### Tier A (deferred)

10. **`InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion`** (line 242, 2 internal sorries)
    - Unblocked once `pNormalForm_residual_orbit_iso` is fully sorry-free (i.e. items 4, 6, 7 all landed).
    - May also need signature extension (add `Nondegenerate` / `(2 : F) ≠ 0` hypotheses; reduce two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s existence half).
    - **Estimated effort:** 30 lines once upstreams land.

## Suggested round structure for next session

- **Round 4a (plan agent — statement fixes, blocking):**
  - Tier S #2: `Basic.lean :: UnipotentRadical` skew-adjoint tightening.
  - Tier S #3: `SliceSetup` Lagrangian condition (decide whether to add to `SliceSetup` directly or to a derived structure to avoid instance breakage; review call sites first).
  - Tier S #4: `kernelImage_ker` re-type `Sₕ` to `LinearEquiv`.

- **Round 4b (parallel provers, after 4a lands; one file per prover, 4 provers):**
  - Prover A — `Slice.lean`: add Levi-action machinery (item 4) AND close `parametrizeX0PlusU_existence` (now provable after Tier S #2 — items 4 + Tier S #2).
  - Prover B — `NormalForm.lean` first half: close `pNormalForm_witnesses` (item 5) and `residual_levi_extract` (item 6) (sequentially). **Wait for prover A's item 4 to land before starting.**
  - Prover C — `NormalForm.lean` second half: close `kernelImage_ker` and `kernelImage_im` (items 8 + 9). Tier S #3 + #4 must land first.
  - Prover D (after B and C land) — `NormalForm.lean :: residual_levi_build` (item 7).

- **Round 5 (cleanup):**
  - `sIndependenceAndOrbitCriterion` in `Orbits.lean` (item 10).

**Note on coupling**: items 4 → 5 → 6 → 7 are a chain within `NormalForm.lean`; items 8 + 9 are blocked on Tier S #3 / #4 only and can run in parallel with the chain. Total 4 provers in Round 4b is feasible if the harness can serialize within `NormalForm.lean` (avoid two provers editing the same file mid-round).

## Reusable proof patterns discovered (carry forward)

(Augmenting session 4 list.)

1. **Adjoint-pair → orthogonal via paired inverse** (NEW session 5):
   When you have `LinearMap.IsAdjointPair B B f g` and `g ∘ f = id`,
   conclude `LinearMap.IsOrthogonal B f` via:
   ```lean
   intro u v
   calc B (f u) (f v)
       = B u (g (f v)) := hAdj u (f v)
     _ = B u v := by rw [hinv_apply]
   ```
   where `hinv_apply : ∀ w, g (f w) = w` is reached via `congrArg (· w) hinv` + `simpa`.
   Useful template for "convert pair-adjoint to orthogonal" in any file.

2. **Block-decomposition + `linear_combination` for bilinear-form identities** (NEW session 5):
   For an identity in `S.ambientForm` (a `mk₂` of `λ`, `B₀`, `ε`):
   - Destruct vector arguments as `(e, v, e')`.
   - Apply `*_apply` lemmas to unfold the operator.
   - `simp only [SliceSetup.ambientForm, LinearMap.mk₂_apply, LinearMap.map_add, LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, LinearMap.neg_apply, LinearMap.map_neg, neg_neg]`.
   - Apply pairing-eq lemmas (`Cdual_pairing_eq` here) to all `λ(F ·, ·)` atoms.
   - Close with `linear_combination` using ε-symmetry-derived hypotheses (`hε`, `hε2`, point-specific instantiations like `hC`, `hD'`).
   This converged in ~5 `lean_multi_attempt` iterations on the right coefficient set.

3. **Cross-file proof structure validation via `lean_run_code`** (NEW session 5):
   When a proof depends on a sister-prover's signature change that hasn't landed yet, validate the local proof shape with hypothetical inputs of the correct shape:
   ```lean
   example (B : LinearMap.BilinForm R M) (f g : Module.End R M)
       (hAdj : LinearMap.IsAdjointPair B B f g)
       (hinv_apply : ∀ w, g (f w) = w) :
       LinearMap.IsOrthogonal B f := by ...
   ```
   Eliminates uncertainty about whether the proof is sound vs. waiting on the cross-file dependency.

## Anti-patterns to retire / confirm

- ✅ **Confirmed retired this round:** `field_simp` on `(2 : F)⁻¹ + (2 : F)⁻¹` (Slice prover correctly avoided it).
- ✅ **Confirmed retired this round:** private-declaration scoping confusion (Slice prover correctly used public `Cdual_pairing_eq` instead of private `Cdual_pairing`).
- ⏸ **Still active:** `obtain ⟨…⟩ := <existential>` makes destructured fields opaque (session 4 finding); did not bite this round but will on Round 4b's `pNormalForm_witnesses` discharge if we package the Levi data as an existential rather than as a structure.

## Stale recommendations to retire

The session 4 recommendations file said:
- "Tier S #1 fix `uD_isParabolic` IsAdjointPair from `(uD D, uD D)` → `(uD D, uD (-D))`" — **DONE this round.**
- "Tier S #1 fix `IsParabolicElement` to use `IsOrthogonal` instead of self-adjoint `IsAdjointPair`" — **DONE this round (combined into the Tier S #1 work).**
- "Tier-D inheritance sorry in `pNormalForm`" — **DONE this round (closed via the calc-chain proof).**
- "Levi-action machinery in `Slice.lean`" — **STILL PENDING**; Round 4 priority.
- "`UnipotentRadical` skew-adjoint tightening" — **STILL PENDING**; Round 4 plan-agent work.
- "`SliceSetup` Lagrangian condition" — **STILL PENDING**; Round 4 / 5 plan-agent work.
- "`kernelImage_ker` re-type `Sₕ` to `LinearEquiv`" — **STILL PENDING**; Round 4 plan-agent work.
- "`sIndependenceAndOrbitCriterion`" — **STILL DEFERRED** to Round 5.

## Risk of further regressions

- Build is green and `pNormalForm` is now sorry-free, but its `show`-pattern fragility (session 4 mid-round break) is still latent. **Recommendation reaffirmed:** when adding Levi-action machinery to `Slice.lean` in Round 4, keep changes strictly additive (do not modify existing `_apply` lemmas).
- Tier S #3 (Lagrangian condition) requires deciding *where* to add the field. Adding directly to `SliceSetup` may break instance synthesis; if so, define a sibling structure `SliceSetupWithPaired` extending `SliceSetup` with the extra field. **Audit `SliceSetup` usage sites first.** Currently `SliceSetup` has zero non-trivial typeclass instances (it's a structure, not a class), so direct addition is *probably* safe but warrants verification.
- Tier S #2 (UnipotentRadical tightening) will affect every consumer of `UnipotentRadical`. Audit consumers in `Slice.lean :: parametrizeX0PlusU_existence` and any other call sites before changing the predicate.

## Confidence summary

- **High confidence (close in next round, ≤50 lines each):** items 4 + 5 (Levi machinery + `pNormalForm_witnesses` discharge).
- **Medium confidence (depends on Tier S landing first):** items 6, 7, 8, 9 (residual_levi_extract, residual_levi_build, kernelImage_ker, kernelImage_im).
- **Lower confidence (depends on chain):** item 10 (`sIndependenceAndOrbitCriterion`) — Round 5.

**Net forecast:** if Round 4a (3 plan-agent statement fixes) and Round 4b (additive Levi machinery + 4 prover discharges) both succeed, end of session 6 should see **0–2 declaration sorries remaining** (Orbits.lean's `sIndependenceAndOrbitCriterion` is the most likely holdout, blocked on Round 5).
