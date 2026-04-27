# InducedOrbitToy/X0Geometry.lean

## Summary

- `vplusKerPairing_isPerfPair` (line 111): **RESOLVED** (sorry-free).
- `sDual_restrict_ker_isIso` (line 206): **PARTIAL** — full proof skeleton in
  place; injectivity of the candidate map `Tdual ∘ subtype` is closed; two
  scoped `sorry`s remain (`h_in_L1`, `h_dim_L1`) that are autoformalization
  gaps in `DualTransposeData`.

`lake build` is green. No new `axiom` declarations introduced.
`#print axioms InducedOrbitToy.vplusKerPairing_isPerfPair` reports only
`propext`, `Classical.choice`, `Quot.sound` (Mathlib defaults).

## `vplusKerPairing_isPerfPair` (line 111) — RESOLVED

### Approach
Apply `LinearMap.IsPerfPair.of_injective`, which (over a `Field`) reduces a
perfect pair to two-sided injectivity, given `[FiniteDimensional F S.Vplus]`
(automatic since `S.Vplus ≤ S.V0` is finite).

Two helper facts established locally:
- `href : S.formV0.IsRefl` — extracted from `S.epsSymm`.
- `horthorth : S.formV0.orthogonal (LinearMap.ker S.X0) = LinearMap.range S.X0`
  — combine `orthogonal_range_eq_ker` with
  `LinearMap.BilinForm.orthogonal_orthogonal hnondeg href`.

Left injectivity (`vplusKerPairing` injective on `S.Vplus`):
1. From `vplusKerPairing v = 0`, get `S.formV0 v x = 0` for every
   `x ∈ ker X0` (`congrArg` + `LinearMap.domRestrict₁₂_apply`).
2. By reflexivity, also `S.formV0 x v = 0` for every `x ∈ ker X0`, hence
   `(v : S.V0) ∈ S.formV0.orthogonal (LinearMap.ker S.X0) = LinearMap.range S.X0`.
3. Combined with `v ∈ S.Vplus` and `S.isCompl.disjoint.eq_bot`, conclude
   `(v : S.V0) = 0`, hence `v = 0`.

Right injectivity (the flip injective on `LinearMap.ker S.X0`):
1. From `(vplusKerPairing).flip x = 0`, get `S.formV0 v x = 0` for every
   `v ∈ Vplus`.
2. For arbitrary `y ∈ S.V0`, decompose `y = v + r` with `v ∈ Vplus`,
   `r ∈ range X0` using `S.isCompl.codisjoint.eq_top`. The `v`-part is
   killed by step 1; the `r`-part by `ker_le_orthogonal_range`.
3. Now `S.formV0 y x = 0` for every `y ∈ S.V0`. Apply `hnondeg.2`
   (right-separating part of `Nondegenerate`) to get `(x : S.V0) = 0`.

### Mathlib lemmas used
- `LinearMap.IsPerfPair.of_injective`
- `LinearMap.BilinForm.orthogonal_orthogonal`
- `LinearMap.BilinForm.mem_orthogonal_iff`
- `LinearMap.domRestrict₁₂_apply`
- `injective_iff_map_eq_zero`
- `Submodule.mem_sup`, `Submodule.mem_bot`, `Subtype.ext`
- `IsCompl.disjoint`, `IsCompl.codisjoint`,
  `Disjoint.eq_bot`, `Codisjoint.eq_top`

## `sDual_restrict_ker_isIso` (line 206) — PARTIAL

### Approach
The candidate map is `f := D.Tdual ∘ₗ (LinearMap.ker S.X0).subtype`. The
proof factors into four steps:

#### Step A — `f` is injective (RESOLVED).

Suppose `f w = 0`, i.e. `D.Tdual (w : S.V0) = 0`.
- For each `v : S.Vplus`, `D.pairing_eq w (T.symm v)` plus the fact
  that `T (T.symm v) = v` (via `simp`) gives
  `S.formV0 w v = 0`.
- Reflexivity (`href`) flips this to `S.formV0 v w = 0` for every
  `v ∈ S.Vplus`.
- Apply right-injectivity of `vplusKerPairing` (the `bijective_right`
  component of `hperf := vplusKerPairing_isPerfPair`) — this gives
  `(vplusKerPairing).flip w = 0` and hence `w = 0`.

#### Step B — `D.Tdual` maps `ker S.X0` into `L1` (SCOPED SORRY).

This is **not derivable from `DualTransposeData` as currently
autoformalized**.  `DualTransposeData` exposes only the values of
`lambda (D.Tdual v)` on `L1' ⊆ E'`; the values on `L0' ⊆ E'` are free.
Without that, `D.Tdual w` is determined only up to an `L0'`-extension and
need not lie in `L1`.

In the blueprint, the missing data is supplied by:
- `IsPaired lambda L1 L1'` (so `lambda` restricted to `L1 × L1'` is a
  perfect pair),
- `IsIsotropic lambda L0 L0'` and an `IsCompl` decomposition `L1 ⊕ L0 = E`
  (so `L1` is exactly the kernel of `λ(·)` restricted to `L0' ⊆ E'`).

#### Step C — `dim L1 = c S` (SCOPED SORRY).

Same source as Step B.  Without `IsPaired lambda L1 L1'`, `L1` is an
arbitrary `Submodule F E` and there is no path from `dim L1' = c S`
(`hL1'`) to `dim L1 = c S`.  In a slice setup with `IsPaired`, the
identity follows from `IsPaired.dim_eq` (or its analogue) plus `hL1'`.

#### Step D — package the equivalence (RESOLVED, modulo B and C).

Use `LinearMap.codRestrict L1 f hf_in_L1` to obtain
`g : ker S.X0 →ₗ[F] L1`, where `hf_in_L1` follows from B.  Injectivity of
`g` follows from `hf_inj` via coercion.  Dimension equality
`finrank (ker S.X0) = finrank L1` reduces to C and the definitional
`c S = finrank (ker S.X0)`.  Then
`g.linearEquivOfInjective hg_inj hg_dim` is the desired
`φ : ker S.X0 ≃ₗ[F] L1`, and the pointwise identity
`(φ w : E) = D.Tdual w` follows by
`LinearMap.linearEquivOfInjective_apply` and
`LinearMap.codRestrict_apply`.

### Recommended fix at the plan layer

Strengthen `DualTransposeData` to carry the missing constraints, or
restate `sDual_restrict_ker_isIso` to take them as separate hypotheses.
Concretely, add (either as fields or as additional hypotheses on the
theorem):
```
Tdual_mem_L1 : ∀ w : LinearMap.ker S.X0, Tdual (w : S.V0) ∈ L1
lambda_pair_L1 : IsPaired lambda L1 L1'
```
With these, `h_in_L1` is just `Tdual_mem_L1 w`, and `h_dim_L1` follows
from `lambda_pair_L1.1` together with `hL1'`. Once these are in place, the
existing proof skeleton in this file should close with no further edits.

Alternatively, fold these conditions into a strengthened slice-aware
variant of `DualTransposeData` (`DualTransposeData.OfSlice` or similar)
and route the consumer in `Slice.lean` through that.

### Mathlib lemmas used / referenced
- `LinearMap.IsPerfPair.bijective_right`
- `LinearMap.codRestrict`, `LinearMap.codRestrict_apply`
- `LinearMap.linearEquivOfInjective`,
  `LinearMap.linearEquivOfInjective_apply`
- `Function.Injective` via `injective_iff_map_eq_zero`
- `LinearMap.flip_apply`, `LinearMap.domRestrict₁₂_apply`

## Verification

```
$ lake env lean InducedOrbitToy/X0Geometry.lean
InducedOrbitToy/X0Geometry.lean:206:8: warning: declaration uses `sorry`
```
- Single warning, corresponding to the two scoped `sorry`s inside
  `sDual_restrict_ker_isIso` (lines ~261 and ~264).
- `vplusKerPairing_isPerfPair` is `sorry`-free (no warning emitted at its
  declaration site).
- `lake build` completes successfully with the same warnings reported by
  the other in-progress files (`Slice.lean`, `NormalForm.lean`,
  `Orbits.lean`).
- `lean_verify InducedOrbitToy.vplusKerPairing_isPerfPair` →
  `axioms = [propext, Classical.choice, Quot.sound]` (no custom axioms).
- `lean_verify InducedOrbitToy.x0Geometry` likewise inherits only the
  Mathlib defaults (it depends on `vplusKerPairing_isPerfPair`).

## Notes for next session

- The remaining gaps in `sDual_restrict_ker_isIso` are *structural* — they
  cannot be closed by trying harder with Mathlib search.  Resolving them
  requires the plan agent to choose between strengthening
  `DualTransposeData` or adding explicit hypotheses to the theorem; once
  that decision is made, this file should compile sorry-free using the
  proof skeleton already in place.
- Do not revert the structure of the `set f := ...` / `let g := ...`
  block; the surrounding plumbing is what makes the eventual sorry-free
  closure trivial once `h_in_L1` and `h_dim_L1` become real proofs.
- The `simp` line inside `hf_inj` (line ~248) currently uses
  `[LinearMap.flip_apply, vplusKerPairing, LinearMap.domRestrict₁₂_apply,
  LinearMap.zero_apply, map_zero]`.  If polish-stage linting trims this
  further, keep `LinearMap.domRestrict₁₂_apply` — without it the goal
  cannot be reduced to the `h_pair'` shape.
