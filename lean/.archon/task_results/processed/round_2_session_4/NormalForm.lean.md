# InducedOrbitToy/NormalForm.lean — Round 2 (prover)

## Summary

Both Tier A targets (`pNormalForm`, `pNormalForm_residual_orbit_iso`)
were converted from bare `sorry` bodies into structured proofs that
factor the missing infrastructure into focused, named helper lemmas.
The two main theorems compile and have proof bodies that reduce to
helper sorries plus the documented Tier D inheritance (the
`IsAdjointPair` conjunct of `IsParabolicElement`, blocked by the
upstream `uD_isParabolic` statement bug).

**Sorry count:** 4 → 6 (4 helper/inheritance sorries instead of 2 bare
ones), but the *structure* of the proofs is now in place and the
remaining gaps are explicitly named. The 2 untouched Tier C sorries
(`kernelImage_ker`, `kernelImage_im`) are unchanged per round
instructions.

**Verification (2026-04-27):**

* `lake env lean InducedOrbitToy/NormalForm.lean` → only `sorry`
  warnings, no errors.
* `lake build` → green; only `sorry` warnings.
* `#print axioms` for `pNormalForm`, `pNormalForm_residual_orbit_iso`,
  `kernelImage_dim` → only `[propext, sorryAx, Classical.choice,
  Quot.sound]`. **No custom axioms.**

## Per-target detail

### `pNormalForm` (line 246, was line 167)

#### Approach
- **RESOLVED (with focused sorries)** — proof reduces to a single
  `pNormalForm_witnesses` helper plus a `IsParabolicElement` build that
  inherits exactly the Tier D `IsAdjointPair` conjunct.

#### Structure of the proof
1. `pNormalForm_witnesses` (line ~196): packages the multi-step Levi
   pre-conjugation as the existence of `(Sₕ, D, T)` such that
   `IsSkewT T ∧ uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T`. Sorried — this is
   the genuine blocker (no Levi action machinery in `Slice.lean`).
2. `isUnit_uD` (helper at line ~149): `IsUnit (uD D)` from
   `uD_neg_inverse` via `Units.mkOfMulEqOne`.
3. `map_uD_eq_of_le` (helper at line ~159): `Submodule.map (uD D) F = F`
   from inclusions both ways, using `uD D ∘ uD (-D) = id`.
4. `pNormalForm` itself: assembles `Sₕ, T, hT, uD D, parabolic-element,
   conjugation`. The conjugation falls out of `hConj` from the helper
   by multiplying right by `uD D` and using `uD (-D) ∘ uD D = id`.

#### Remaining sorries
- Line 196 (`pNormalForm_witnesses`): Levi witness existence. Documented
  with the precise blueprint reference (lines 200–264 of
  `references/blueprint_verified.md`).
- Line 237 (`pNormalForm` IsAdjointPair conjunct): Tier D inheritance
  from `Slice.lean :: uD_isParabolic` — see that docstring.

#### Mathlib lemmas used
- `Units.mkOfMulEqOne`, `Units.isUnit`
- `LinearMap.comp_assoc`, `LinearMap.comp_id`
- `Submodule.map` (membership unpack)

#### Anti-patterns hit (resolved)
- `LinearMap.mul_eq_one_of_mul_eq_one` is **deprecated** —
  use `Units.mkOfMulEqOne ... |>.isUnit` directly (one-sided
  invertibility suffices to package as a `Units`).
- `isUnit_of_mul_eq_one` is **deprecated** — use
  `IsUnit.of_mul_eq_one` (no longer takes the second argument
  positionally), or `(Units.mkOfMulEqOne _ _ h).isUnit` (cleaner).
- Cannot `obtain ⟨C', B', ...⟩ := uD_conj_XCB ...` and then
  `show C' = ...; exact ...` — the `obtain` makes `C'`, `B'` opaque
  variables, not the let-bound terms inside `uD_conj_XCB`'s proof.
  **Workaround**: change the helper's conclusion to package the
  *conjugation equation directly* (`uD D ∘ XCB C B ∘ uD (-D) = XST Sₕ T`),
  bypassing `uD_conj_XCB`'s existential wrapper entirely.

### `pNormalForm_residual_orbit_iso` (line 369, was line 199)

#### Approach
- **RESOLVED (with focused sorries)** — the iff splits into two helper
  lemmas, each owning one direction.

#### Structure of the proof
- `residual_levi_extract` (line ~307): forward direction, sorried —
  needs Levi/unipotent decomposition `p = u_D · m` to extract the
  `L0'`-block of `m` as `h : L0' ≃ L0'`.
- `residual_levi_build` (line ~336): backward direction, sorried —
  needs the perfect-pairing dual `(h⁻¹)^∨ : L0 → L0` (and a missing
  Lagrangian condition on `λ(L0, L0')`).
- `pNormalForm_residual_orbit_iso` itself: trivial `refine ⟨?_, ?_⟩`
  plus dispatch.

#### Remaining sorries
- Line 307 (`residual_levi_extract`): Levi decomposition machinery.
- Line 336 (`residual_levi_build`): perfect-pairing dual on `L0`,
  plus the Tier D `IsAdjointPair` conjunct *inside* `IsParabolicElement`.

### `kernelImage_ker` (line 482, formerly 302)

- **NOT TOUCHED** per round instructions (Tier C — needs `SliceSetup`
  refactor exposing Lagrangian condition `λ(L1, L0') = 0` and `Sₕ`
  typed as `LinearEquiv`).
- Body contains 2 scoped sorries from prior round, plus the existing
  outline comments. Untouched.

### `kernelImage_im` (line 577, formerly 397)

- **NOT TOUCHED** per round instructions (Tier C, same blocker as above).
- Body is a bare `sorry`. Untouched.

## What's now needed to finish (for the plan agent)

### To close `pNormalForm` completely

The remaining work is in **two pieces**, in order:

1. **Add Levi-action machinery to `Slice.lean`**. Specifically, expose
   constructors for:
   - `leviGL_E : (S.E' ≃ₗ[F] S.E') →* Module.End F S.V` — the embedding
     of `GL(E')` into the Levi factor of `P`,
   - `leviGL_V0 : (S.V0 ≃ₗ[F] S.V0) →* Module.End F S.V` — same for
     `GL(V0)` (acting trivially on `E` and `E'`),
   - and a `levi_conj_XCB` lemma giving the action on `XCB` parameters
     (`m X_{C,B} m⁻¹ = X_{g₀ C d⁻¹, (d⁻¹)^∨ B d⁻¹}` per blueprint
     line 277–278).
2. **Fill `pNormalForm_witnesses`** using the new Levi machinery. The
   blueprint construction is now mechanical:
   - choose `d ∈ GL(E')` so `d(L0') = ker Cbar` (uses `_hRank`),
   - choose `d|_{L1'}` so the resulting `Cbar|_{L1'}` matches the
     fixed iso induced by `Sₕ` (uses surjectivity of `Cbar`),
   - `D := X0⁻¹ on (C - CST Sₕ)` (uses surjectivity of `X0` onto
     `range X0` plus a section choice via `Vplus`-complement).

After (1) and (2), `pNormalForm`'s assembly is already complete in this
file — it only needs `pNormalForm_witnesses` to discharge.

### To close `pNormalForm_residual_orbit_iso` completely

1. The same Levi-action machinery (above) plus a *Levi-decomposition*
   lemma `parabolic_decompose : ∀ p, IsParabolicElement S p → ∃ D m,
   p = uD D ∘ leviGL m` for the forward direction.
2. **Add a Lagrangian-pair condition** to `SliceSetup` (or to a derived
   structure): `L0_paired : IsPaired paired.pairing L0 L0'`. The bare
   `L0_isotropic` is *not* enough; we need a perfect pairing on
   `L0 × L0'` to dualize `h⁻¹` for the backward direction's
   construction `(h⁻¹)^∨ : L0 → L0`.
3. The `IsAdjointPair` conjunct of `IsParabolicElement` is still Tier D
   (the construction is an isometry, not self-adjoint w.r.t.
   `S.ambientForm` — the autoformalisation bug applies here too).

### To unblock the Tier D conjunct globally

Plan agent must rewrite `IsParabolicElement` to use either:
- `IsAdjointPair S.ambientForm S.ambientForm p (Ring.inverse p)` (the
  isometry condition), or
- a dedicated `IsIsometry` predicate.

Until then, *all* downstream uses of `IsParabolicElement` will inherit
this blocker.

## Negative search results / dead ends

- Searched for `Module.End.isUnit_iff` and `isUnit_of_left_inverse` in
  Mathlib — both do not match a one-sided inverse over a non-comm ring
  in the form needed. The cleanest approach is via `Units.mkOfMulEqOne`
  (which uses `IsDedekindFiniteMonoid` — `Module.End F V` for finite-dim
  V satisfies this).
- Tried `obtain ⟨C', B', _, hConj⟩ := uD_conj_XCB ...` then
  `show C' = CST Sₕ` — fails because `obtain` makes `C'` opaque.
  **Switched** the helper's conclusion to package the conjugation
  equation directly, eliminating the need for `uD_conj_XCB`'s
  existential wrapper.
- Considered `parametrizeX0PlusU_uniqueness` to identify the abstract
  `(C', B')` from `uD_conj_XCB` with `(CST Sₕ, BST T)` — would require
  proving `IsSkewB (BST T)` first, which itself is **not** automatic
  from `IsSkewT T` (needs `λ(L0, L1') = 0`, a missing structural
  condition). Same root issue as `kernelImage_ker` Tier C blocker.

## Test plan for next round

Once Levi machinery is in place:

1. Verify `pNormalForm_witnesses` compiles with the Levi-based
   construction (inspect goal at line 196).
2. Verify the `obtain` destructure in `pNormalForm` still threads
   correctly (`hConj` should be of the new shape).
3. Verify `residual_levi_extract` and `residual_levi_build` compile
   with the parabolic decomposition lemma.
4. Re-run `#print axioms` to confirm only `[propext, Classical.choice,
   Quot.sound]` remain (no `sorryAx`).

## Confirmation (per acceptance criteria)

- `lake env lean InducedOrbitToy/NormalForm.lean` → ✅ only `sorry`
  warnings.
- `lake build` → ✅ green.
- No new `axiom` declarations — ✅ verified via `#print axioms`.
- All helpers introduced are `private` and live inside `NormalForm.lean`
  — ✅ (`isUnit_uD`, `map_uD_eq_of_le`, `pNormalForm_witnesses`,
  `residual_levi_extract`, `residual_levi_build`).
- Initial definitions and final theorem statements unchanged — ✅
  (the existing `pNormalForm` and `pNormalForm_residual_orbit_iso`
  signatures and their docstrings are unchanged; only the proof bodies
  were filled).
