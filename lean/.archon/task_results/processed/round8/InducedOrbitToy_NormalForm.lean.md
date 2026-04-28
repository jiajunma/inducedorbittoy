# InducedOrbitToy/NormalForm.lean — Round 8 Prover Report

## Round 8 status: IN PROGRESS — Single isolated helper sorry

`lake env lean InducedOrbitToy/NormalForm.lean` compiles with **one
declaration-use `sorry` warning** at line 197
(`pNormalForm_witnesses_aux`).

**Note on `lake build`:** at the time of writing, `lake build` was
breaking due to *parallel-Slice-prover* edits to
`InducedOrbitToy/Slice.lean` (lines ~1101–1518), which left
`parabolic_decompose` in a half-implemented state with type errors.
The Slice prover's Round-8 work (Objective 3) is responsible for that
file. NormalForm.lean is independent of those edits (only depends on
the stable Round-6/Round-7 Slice APIs).

## pNormalForm_witnesses (line 264)

### Attempt 1
- **Approach:** Refactored the single body `sorry` into a single isolated
  helper sorry `pNormalForm_witnesses_aux` (line 197). The body of
  `pNormalForm_witnesses` is now sorry-free — it just unpacks the
  helper.
- **Result:** IN PROGRESS — the helper carries the residual sorry.
  Net declaration-use sorry count in NormalForm.lean: 1 (unchanged
  from the start of Round 8).
- **Rationale:** The PROGRESS.md acceptance criterion explicitly
  permits this fallback: "Acceptable to introduce one isolated helper
  `private def` with its own sorry if Step 1 (d-construction) is
  intractable; in that case the helper sorry must be documented with a
  `Gap:` comment block." The aux helper carries a comprehensive Gap
  docstring (lines 152–196) walking through all four steps of the
  blueprint proof.

### Attempts considered but not landed
1. **Direct four-step proof inline.** Aborted because Step 1 (the
   d-construction) alone was estimated at ~150 lines (per PROGRESS.md
   §1) and Steps 2–4 require non-trivial block-matrix algebra plus a
   separate lifting helper through `X0`.
2. **Two helper sorries (`pNormalForm_levi_data`,
   `pNormalForm_lift_D`) + body sorry for Steps 3–4.** Rolled back
   because (a) the net sorry count would have *increased* from 1 to
   3, and (b) the round-8 plan calls for *one* isolated helper, not
   multiple.

### Strategy notes for Round 9 (or polish)
The Gap docstring of `pNormalForm_witnesses_aux` (lines 152–196)
contains the full four-step plan:

1. **Step 1 — `(Sₕ, d)` construction.**
   - `Cbar S C` is surjective by `_hRank` + `dim (V0/range X0) = c`.
   - `dim ker (Cbar S C) = dim E' - c`.
   - **Subtle:** `dim L1' = c` is needed for `Sₕ : L1' ≃ Vplus`. This
     is *not* enforceable from `SliceSetup` alone (counterexamples:
     `L1' = E'`, `L0' = 0`). The Round-9 prover may need to either
     (a) add a hypothesis `dim L1' = c` to the signature, or (b)
     identify a hidden derivation from `_hRank` + the slice
     constraints.
   - Construct `d : E' ≃ E'` by combining `L0' ≃ ker (Cbar S C)`
     with `L1' ≃ K'` (a chosen complement of `ker (Cbar S C)`)
     normalised so that `(Cbar S C) ∘ d.symm |_{L1'} = mkQ ∘ Sₕ`.

2. **Step 2 — Lift through X0.**
   - `(C ∘ d.symm - CST Sₕ)` lands in `range X0` by Step 1.
   - Lift via a section of `X0 |_K : K ≃ range X0` for any complement
     `K` of `ker X0` in `V0`.
   - Mathlib API: `Submodule.exists_isCompl` for `K`,
     `LinearEquiv.ofInjective` (or `LinearMap.linearEquivOfInjective`)
     for `K ≃ range X0`. Compose with `LinearMap.codRestrict`-style
     restriction.

3. **Step 3 — Identify `T : L0' →ₗ L0`.**
   - After `leviGL_E_conj_XCB` and `uD_conj_XCB`, the conjugated
     operator equals `XCB(C', B'')` with explicit `(C', B'')`.
   - `C' = C ∘ d.symm - X0 ∘ D = CST Sₕ` (by Step 2's `hXD`).
   - `B''` is the Cdual-corrected `B' = lambdaDualE d.symm ∘ B ∘ d.symm`.
   - Choose `D|_{L1'}` carefully (via `vplusKerPairing_isPerfPair`)
     so that `B''(L1') = 0` and the skew condition forces
     `B''(L0') ⊂ L0`. **This requires extending Step 2 to choose
     `D` more carefully than just "any lift."**
   - The L0'-restriction of `B''` defines `T`.

4. **Step 4 — Verify `IsSkewT T` + conjugation.**
   - Skewness of `T` propagates from `_hB` through Levi+unipotent.
   - The conjugation reduces to `parametrizeX0PlusU_uniqueness`
     applied to `(C', B'')` and `(CST Sₕ, BST T)`.

### Mathlib lemmas relevant to Round 9
- `Submodule.exists_isCompl` — for picking complements in
  finite-dim spaces.
- `LinearMap.linearEquivOfInjective` — already used in
  `residual_levi_extract`; pattern reusable.
- `Submodule.prodEquivOfIsCompl` — already used in
  `extendL0'IsoToE'`; pattern reusable.
- `LinearEquiv.ofFinrankEq` — for picking arbitrary iso between
  finite-dim spaces of equal dim.
- `vplusKerPairing_isPerfPair` (X0Geometry) — perfect pairing
  `Vplus × ker X0 → F` used in Step 3 to choose `D|_{L1'}`.
- `LinearMap.exists_extend` (or equivalent) — for the lift through
  `X0` (Step 2). May need a custom helper if Mathlib's API doesn't
  directly fit.

### Key pitfalls (carry-forward to Round 9)
- **`dim L1' = c` is not in the bare `SliceSetup`.** The Round-9
  prover should verify whether this is implicitly enforceable from
  `_hRank` + slice constraints. If not, the helper signature may need
  a `(_hL1' : Module.finrank F S.L1' = c S.toX0Setup)` hypothesis
  added (cascading through `pNormalForm`, `pNormalForm_residual_orbit_iso`,
  and downstream).
- **Step 3's choice of `D|_{L1'}` is non-trivial.** The blueprint
  (lines 230–258) requires using the perfect pairing
  `Vplus × ker X0 → F` to satisfy a half-skewness condition. Round 8's
  current helper doesn't expose this; Round 9 may want to refactor
  the helper to expose `D` more directly with the L1'/L0' split.

## Files touched (Round 8)
- `InducedOrbitToy/NormalForm.lean`:
  - **Added:** `pNormalForm_witnesses_aux` (line 197) — single
    isolated helper carrying the residual sorry. Includes a
    comprehensive Gap docstring (lines 152–196).
  - **Modified:** `pNormalForm_witnesses` body (line 264) — replaced
    bare `sorry` with `exact pNormalForm_witnesses_aux ...`. The body
    is now sorry-free.

## Compilation status
- `lake env lean InducedOrbitToy/NormalForm.lean` — **compiles** (1
  warning: declaration uses `sorry` at line 197).
- `lake build` — **breaks** in `Slice.lean` due to parallel
  Slice-prover edits (Round-8 Objective 3, unrelated to NormalForm).
  NormalForm.lean is unaffected.

## Axioms
- `pNormalForm_witnesses` transitively uses `sorryAx` via
  `pNormalForm_witnesses_aux`.
- Once the helper closes (Round 9), `#print axioms pNormalForm_witnesses`
  is expected to show only `[propext, Classical.choice, Quot.sound]`.

## Acceptance criteria status (Round 8 PROGRESS.md §1)
- [x] `lake env lean InducedOrbitToy/NormalForm.lean` compiles.
- [partial] The `sorry` at body line 216 is replaced by a real proof.
  *Replaced by a one-liner that calls a documented helper sorry.*
  Per PROGRESS.md: "Acceptable to introduce one isolated helper
  `private def` with its own sorry if Step 1 (d-construction) is
  intractable; in that case the helper sorry must be documented with
  a `Gap:` comment block." ✓ matches this fallback.
- [external] `lake build` is green at end of round.
  *Currently broken in Slice.lean (parallel-prover regression),
  unrelated to NormalForm.*
- [n/a] `#print axioms pNormalForm_witnesses` shows only
  `[propext, Classical.choice, Quot.sound]`. *Not yet — sorry'd in
  helper. Expected to clear once Round 9 closes the helper.*
- [pending] Stale comment hygiene at lines 344, 357. Not edited this
  round.

## Recommendation for plan agent
Round 9 can pick up `pNormalForm_witnesses_aux` and either close it in
full (~200–300 lines) or split it into more granular helpers
(`levi_data` + `lift_D` + `T_construction` + `verify`). The Gap
docstring at lines 152–196 contains the full informal plan; the
Mathlib-lemma list above is a starting point for the formal closure.
