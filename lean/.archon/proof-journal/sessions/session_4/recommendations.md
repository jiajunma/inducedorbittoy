# Recommendations for Session 5

## Snapshot

- **Build state:** `lake build` is green; 9 declaration-use `sorry` warnings remain.
- **Custom axioms:** 0. All public theorems depend on `[propext, Classical.choice, Quot.sound]` only.
- **Net session-4 progress:** 8 → 9 declaration-use sorries (+1, but with major structural improvement; see below).

## What actually shipped this round

| File | Δ declaration sorries | Net assessment |
|---|---|---|
| `Basic.lean` | 0 → 0 | No-op (verified clean). |
| `LocalForms.lean` | 0 → 0 | No-op (verified clean). |
| `X0Geometry.lean` | 1 → 0 ✅ | **Genuine win.** `sDual_restrict_ker_isIso` resolved by enriching `DualTransposeData` with two new fields (intra-file refactor). |
| `NormalForm.lean` | 4 → 6 | **Structural win, count regression.** Two bare Tier A sorries decomposed into focused, named helpers (`pNormalForm_witnesses`, `residual_levi_extract`, `residual_levi_build`). The public theorems' bodies are now mechanical assemblies that close once the helpers do. |
| `Slice.lean` | 2 → 2 | **Body refinement.** Tier D sorries unchanged in declaration count; *internal* proof bodies refined to expose the precise false obligation, with two flag-preservation conjuncts of `uD_isParabolic` newly closed. |
| `Orbits.lean` | 1 → 1 | **Body refinement.** Witness extraction made explicit in both directions; downstream Tier A dependency unchanged. |

## Priority queue for next plan iteration

### Tier S — Plan-agent-only work (statement corrections)

These are **out of scope for any prover** and must be addressed by the
plan agent issuing statement-level corrections. They are the only way
to eliminate the Tier D sorries.

1. **`InducedOrbitToy/Slice.lean :: uD_isParabolic`** (line 442 — `IsAdjointPair` conjunct)
   - Change the autoformalised `LinearMap.IsAdjointPair B B (uD D) (uD D)` (self-adjoint) to `LinearMap.IsAdjointPair B B (uD D) (uD (-D))` (isometry).
   - **Rationale:** session 4 verified by direct calculation that `B(uD D x, y) - B(x, uD D y) = -2 · S.formV0 v (D e₁')` for `x = (0, v, 0)`, `y = (0, 0, e₁')` — non-zero in general.
   - **Impact:** unblocks `uD_isParabolic` itself (→ ~10 line proof from `uD_neg_inverse`) AND the Tier-D inheritance in `pNormalForm`'s `IsAdjointPair` conjunct (line 272) AND `residual_levi_build` (line 336). Three sorries unblocked at once.

2. **`InducedOrbitToy/Basic.lean :: UnipotentRadical`** (used by `Slice.lean :: parametrizeX0PlusU_existence` line 232)
   - Tighten the predicate to enforce skew-adjointness w.r.t. `S.ambientForm`. The current loose flag-preserving Lie-algebra version is mathematically too weak: a generic `Y ∈ UnipotentRadical` does *not* satisfy the V₀→E ↔ E'→V₀ block-symmetry that the existence claim demands.
   - **Impact:** unblocks `parametrizeX0PlusU_existence` (the false E-component sorry at line 294 becomes provable; the `IsSkewB` sorry at line 256 also resolves).

3. **`InducedOrbitToy/Slice.lean :: SliceSetup` (or a derived structure)**
   - Add a Lagrangian-pair condition `L0_paired : IsPaired paired.pairing L0 L0'` (alongside the existing weaker `L0_isotropic`). The `IsPaired` upgrade to `IsPerfPair` on `L0 × L0'` is required for:
     - `kernelImage_ker` (NormalForm.lean line 482 — needs `λ(L1, L0') = 0`),
     - `kernelImage_im` (NormalForm.lean line 577 — same condition),
     - `residual_levi_build` (NormalForm.lean line 336 — needs the perfect-pairing dual `(h⁻¹)^∨ : L0 → L0`).
   - **Impact:** unblocks 3 Tier C/Tier A-dependent sorries.

4. **`InducedOrbitToy/NormalForm.lean :: kernelImage_ker` and `kernelImage_im` signatures**
   - Re-type `Sₕ` from `LinearMap` to `LinearEquiv` at the call sites (already done at one of the two consumers in `kernelImage_im` and `kernelImage_dim`; remaining is `kernelImage_ker`).
   - **Impact:** unblocks the Sₕ-injectivity step in `kernelImage_ker`.

### Tier A — Highest priority for next prover round (provable now)

These are blocked only by **adding new infrastructure**, not by statement
fixes. Each is a focused, mechanical addition to `Slice.lean`.

5. **Add Levi-action machinery to `Slice.lean`** (≈60–100 lines):
   - `leviGL_E : (S.E' ≃ₗ[F] S.E') →* Module.End F S.V` — block-diagonal embedding of `GL(E')`.
   - `leviGL_V0 : (S.V0 ≃ₗ[F] S.V0) →* Module.End F S.V` — same for `GL(V0)`.
   - `levi_conj_XCB` lemma: action on parameters per blueprint lines 277–278:
     `m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` for `m = leviGL_E d ∘ leviGL_V0 g₀`.
   - **Impact:** unblocks `pNormalForm_witnesses` (NormalForm.lean line 196) and `residual_levi_extract` (line 307).

6. **Discharge `pNormalForm_witnesses`** (NormalForm.lean line 196) — once Levi machinery lands:
   - Choose `d ∈ GL(E')` so `d(L0') = ker Cbar` (uses `_hRank`).
   - Choose `d|_{L1'}` so the resulting `Cbar|_{L1'}` matches the iso induced by `Sₕ` (uses surjectivity of `Cbar`).
   - `D := X0⁻¹ on (C - CST Sₕ)` (uses surjectivity of `X0` onto `range X0` plus a section choice via `Vplus`-complement).
   - **Mechanical follow-up.** Estimated effort: ~50 lines.

7. **Discharge `residual_levi_extract`** (NormalForm.lean line 307) — needs Levi machinery from item 5 plus a *Levi-decomposition* lemma `parabolic_decompose : ∀ p, IsParabolicElement S p → ∃ D m, p = uD D ∘ leviGL m`. Estimated effort: ~30 lines for the decomposition lemma + 20 lines for the helper itself.

8. **Discharge `residual_levi_build`** (NormalForm.lean line 336) — needs the Tier S item 3 (Lagrangian condition) plus item 5 (Levi machinery). Estimated effort: ~40 lines once both upstreams land.

### Tier A (deferred)

9. **`InducedOrbitToy/Orbits.lean :: sIndependenceAndOrbitCriterion`** (line 242)
   - Unblocked once `pNormalForm_residual_orbit_iso` is fully sorry-free (i.e. items 5, 7, 8 all landed).
   - May also need signature extension (add `Nondegenerate` / `(2 : F) ≠ 0` hypotheses; reduce two-`Sₕ` case to single-`Sₕ` via `pNormalForm`'s existence half).
   - Estimated effort: 30 lines once upstreams land.

## Suggested round structure for next session

- **Round 3a (plan agent — statement fixes, blocking):**
  - Fix `uD_isParabolic` IsAdjointPair from `(uD D, uD D)` → `(uD D, uD (-D))`.
  - Fix `Basic.lean :: UnipotentRadical` to enforce skew-adjointness.
  - Add `L0_paired` Lagrangian condition to `SliceSetup`.
  - Re-type `Sₕ` parameters to `LinearEquiv` where applicable.

- **Round 3b (parallel provers, after 3a lands):**
  - One prover adds Levi-action machinery to `Slice.lean` (item 5).
  - One prover closes `parametrizeX0PlusU_existence` and `uD_isParabolic` in `Slice.lean` (now provable after Tier S fixes).
  - One prover closes `pNormalForm_witnesses`, then `residual_levi_extract`, then `residual_levi_build` in `NormalForm.lean` (sequentially — item 5 → item 6 → item 7 → item 8).
  - One prover closes `kernelImage_ker`, `kernelImage_im` in `NormalForm.lean` (now provable after Tier S item 3 + 4).

- **Round 4 (cleanup):**
  - `sIndependenceAndOrbitCriterion` in `Orbits.lean` (item 9).

## Reusable proof patterns discovered

(Carry forward — augmenting session 3 list.)

1. **`Units.mkOfMulEqOne` for `IsUnit` from a one-sided inverse** on
   `Module.End F V` (finite-dim V):
   ```lean
   exact (Units.mkOfMulEqOne _ _ h).isUnit
   ```
   Replaces the now-deprecated chain `LinearMap.mul_eq_one_of_mul_eq_one`
   + `isUnit_of_mul_eq_one`. The signature of `IsUnit.of_mul_eq_one`
   has changed — it no longer takes the second factor positionally.

2. **Helper-lemma decomposition for "cannot fully close, but can articulate
   the obligation precisely."** When stuck on a multi-step proof where the
   last step requires missing infrastructure, extract the missing piece
   as a focused helper with a targeted signature, sorry it, and use it
   from the public theorem. This *increases* the raw sorry count short-term
   but lets the next prover round attack a focused, named lemma rather than
   reverse-engineer English commentary inside a `sorry`.

3. **Avoid `obtain ⟨a, b, c⟩ := <existential>` if you need to talk about
   `let`-bound contents inside the existential's witness.** `obtain` makes
   the destructured fields opaque, breaking later `show` patterns that
   reference the let-bound values. **Fix:** package the equation directly
   in the helper's conclusion (avoid the existential wrapper).

4. **Multi-`let` definition `show` unfolding:** when a definition's body uses
   multiple `let`s, a downstream `show <unfolded RHS>` will fail to match
   (Lean's whnf does not unfold `let`s automatically). Either change the
   helper's conclusion to package the relevant equation, or insert an
   explicit `change` that bridges from the `let`-form to the unfolded form.

5. **Intra-file structure enrichment is preferable to cross-file refactor.**
   Verify the location of a structure via `grep` before scoping a refactor;
   the session 3 recommendation that `DualTransposeData` lived in
   `Basic.lean` was incorrect (it lives in `X0Geometry.lean`). The
   intra-file refactor was 4 added fields + 2 one-line proof closures.

## Stale recommendations to retire

The session 3 recommendations file said:
- "Tier B (sDual_restrict_ker_isIso) needs a `Basic.lean :: DualTransposeData` refactor"
  — **incorrect**; the structure is in `X0Geometry.lean`. Resolved this round.
- "Tier C `kernelImage_ker` / `kernelImage_im` need `SliceSetup` Lagrangian
  condition" — **still correct**; not yet landed.
- "Tier D `parametrizeX0PlusU_existence` and `uD_isParabolic` are statement
  bugs" — **still correct**; not yet landed.

## Risk of further regressions

- The current build is green but fragile near the `pNormalForm` body; the
  mid-round `show` pattern break (lines 300, 304 during this session) was
  triggered by parallel-prover ordering. **Recommendation:** when adding
  Levi-action machinery to `Slice.lean`, keep the changes additive (do
  not modify existing `_apply` lemmas). The `XCB_apply` and `XST_apply`
  signatures are load-bearing for `pNormalForm`'s assembly.
- Adding fields to `SliceSetup` (Tier S item 3) may break instances; audit
  call sites first. Currently `SliceSetup` has zero non-trivial instances
  (it's a structure, not a class), so additions should be safe.
