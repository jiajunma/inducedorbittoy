# InducedOrbitToy/Slice.lean

## Round 8 status: PARTIAL PROGRESS — substantial structural work added,
single consolidated `sorry` remains, **mathematical gap identified**

## parabolic_decompose (declaration line 1109, body sorry within block)

### Attempt 1 — full closure attempt
- **Approach:** Direct construction of `(D, d, g, hg, eq)` via diagonal-block
  extraction of the action of `p`. Define `pE_fn`, `pV0_fn`, `pE'_fn` as
  the obvious linear maps; package as `LinearEquiv`s using `_hpUnit`.
  Use `_hpIso` on key vector pairs to force the cross-pairing identity
  `λ(pE_fn e, pE'_fn e') = λ(e, e')` and the V0-isometry.
- **Result:** PARTIAL — the data extraction (sorry-free) and the key
  isometry identity all landed cleanly. The final assembly (the equation
  `p = uD D ∘ leviGL_E d ∘ leviGL_V0 g`) hits a structural obstacle.
- **Mathematical finding:** the statement of `parabolic_decompose` as
  written is **strictly narrower than the full Levi decomposition**. A
  general parabolic isometry decomposes as
  `(more general unipotent) ∘ leviGL_E d ∘ leviGL_V0 g`, where the
  "more general unipotent" has the form
  `(e, v, e') ↦ (e + Cdual D v + ½ Cdual D (D e') + B' e', v + D e', e')`
  for some skew `B' : E' →ₗ[F] E`. The current `uD D` definition fixes
  `B' = 0`, which is **not generic**.
- **Witness for the obstacle:** Setting `d := pE'_equiv`, `g := pV0_equiv`,
  `D e' := (p (0, 0, d.symm e')).2.1`, and expanding componentwise:
  - V0-component: matches automatically by definition of `D`.
  - E'-component: matches by construction of `d`.
  - E-component: requires `(p (0, v, 0)).1 = Cdual D (pV0_fn v)` AND
    `(p (0, 0, e')).1 = ½ Cdual D (D (pE'_fn e'))` for all `v, e'`.
  - The first identity follows from `_hpIso` at `((0, v, 0), (0, 0, e''))`
    via `Cdual_pairing` + non-degeneracy of `λ`.
  - The second identity does **NOT** follow from `_hpIso`. The isometry
    only forces (with `f e' := (p (0, 0, e')).1 - ½ Cdual D (D (pE'_fn e'))`):
    ```
    λ(f e₁', pE'_fn e₂') + ε λ(f e₂', pE'_fn e₁') = 0  for all e₁', e₂'
    ```
    This is the `IsSkewB`-shape of a residual skew `B'`, hence `f` is
    in general nonzero.

### What landed (sorry-free, inside the proof body)

All of the following are body-only `let` / `have` declarations with
complete, sorry-free proofs:

1. **Inverse extraction:**
   - `pinv := _hpUnit.unit.inv : Module.End F S.V`.
   - `hpinv_left : ∀ x, pinv (p x) = x` via
     `Module.End.isUnit_inv_apply_apply_of_isUnit`.
   - `hpinv_right : ∀ x, p (pinv x) = x` via
     `Module.End.isUnit_apply_inv_apply_of_isUnit`.

2. **Flag-preservation transfer to `pinv`:**
   - `hpinv_flagE : Submodule.map pinv S.flagE = S.flagE`.
   - `hpinv_flagEV0 : Submodule.map pinv S.flagEV0 = S.flagEV0`.

3. **Diagonal-block linear maps:**
   - `pE_fn : S.E →ₗ[F] S.E` with `pE_fn_eq : ∀ e, p (e,0,0) = (pE_fn e, 0, 0)`.
   - `pV0_fn : S.V0 →ₗ[F] S.V0` with `pV0_fn_E'_eq : ∀ v, (p (0,v,0)).2.2 = 0`.
   - `pE'_fn : S.E' →ₗ[F] S.E'`.
   - Plus the parallel maps `pE_inv`, `pV0_inv`, `pE'_inv` from `pinv`.

4. **Bijectivity (round-trip identities):**
   - `pE_round_left : ∀ e, pE_fn (pE_inv e) = e` via a 3-step calc chain
     `(e,0,0) = p (pinv (e,0,0)) = p (pE_inv e, 0, 0) = (pE_fn (pE_inv e), 0, 0)`.
   - `pE_round_right : ∀ e, pE_inv (pE_fn e) = e` symmetric.
   - `pV0_round_left`, `pV0_round_right` — using the trick that
     `p (γv, pV0_inv v, 0) = (0, v, 0)` decomposes via linearity into
     `p (γv, 0, 0) + p (0, pV0_inv v, 0)` and the V0-component yields
     `pV0_fn (pV0_inv v) = v` after `simp`.
   - `pE'_round_left`, `pE'_round_right` — using analogous decomposition
     `(βi, γi, pE'_inv e') = (βi, 0, 0) + (0, γi, 0) + (0, 0, pE'_inv e')`.

5. **`LinearEquiv` packaging:**
   - `pE_equiv : S.E ≃ₗ[F] S.E := { pE_fn with invFun := pE_inv, ... }`.
   - `pV0_equiv : S.V0 ≃ₗ[F] S.V0`.
   - `pE'_equiv : S.E' ≃ₗ[F] S.E'`.

6. **V0-isometry:**
   - `pV0_iso : ∀ u v, S.formV0 (pV0_fn u) (pV0_fn v) = S.formV0 u v` —
     via `_hpIso` at `((0, u, 0), (0, v, 0))` with `simp` reducing the
     ambient form to the V0-block (the λ-cross-terms vanish because
     `(p (0, ·, 0)).2.2 = 0`).

7. **Cross-pairing key identity:**
   - `hkey : ∀ e e', S.lambda (pE_fn e) (pE'_fn e') = S.lambda e e'` —
     from `_hpIso` at `((e, 0, 0), (0, 0, e'))`. Forces
     `pE_fn = lambdaDualE pE'_equiv.symm` (provable from `hkey` plus the
     perfect pairing on E', though that step is not currently materialised).

### Mathlib lemmas / project-internal lemmas used

- **From `Module.End`:** `Module.End.isUnit_inv_apply_apply_of_isUnit`,
  `Module.End.isUnit_apply_inv_apply_of_isUnit` (two-sided inverse from
  `IsUnit`).
- **From `LinearMap`:** `LinearMap.IsOrthogonal` (unfolding to
  `∀ x y, B (g x) (g y) = B x y`), `map_add`, `map_smul`, `map_zero`.
- **From `Submodule`:** `Submodule.map`, `Submodule.zero_mem`,
  `Submodule.mem_bot`, `_hpFlagE.le ⟨_, _, rfl⟩` membership transfer.
- **From `LinearEquiv`:** `LinearEquiv.mk { toLinearMap with invFun, left_inv, right_inv }`
  pattern via the `{ pE_fn with ... }` anonymous-constructor syntax.
- **Project:** `SliceSetup.flagE`, `SliceSetup.flagEV0`,
  `SliceSetup.ambientForm`, `Cdual_pairing` (signposted in the Gap
  comments but not yet used).

### Structural validation

- `lake env lean InducedOrbitToy/Slice.lean` compiles. **Single warning:**
  `Slice.lean:1109:8: declaration uses 'sorry'` (matches the deferred
  `parabolic_decompose` body).
- `lake build` completes successfully (8033 jobs).
- `#print axioms parabolic_decompose` returns
  `[propext, sorryAx, Classical.choice, Quot.sound]` (transitive `sorryAx`
  expected from the unresolved body).
- All existing declarations through line 1078 (the `Section 6.6` comment
  block) remain byte-for-byte unchanged — the modification is body-only.
- Pre-existing `unused variable hlambda` lint at `X0Geometry.lean:221:35`
  is untouched.

### Recommendation for Round 9 / polish stage

**Two options for the next round:**

(a) **Mathematically correct route (preferred):** generalise `uD` (or add
    a sister `uD_B`) to accept a residual skew parameter
    `B' : E' →ₗ[F] E` satisfying `IsSkewB S B'`, and update
    `parabolic_decompose` to expose `(D, B', d, g)`. The proof then
    closes by setting
      `B' e' := (p (0, 0, pE'_equiv.symm e')).1 - ½ Cdual D (D e')`
    and verifying the `IsSkewB` condition from the residual constraint
      `λ(B' e₁', e₂') + ε λ(B' e₂', e₁') = 0`
    derived above.

(b) **Narrowing route:** keep the current signature and add a hypothesis
    that the residual `B'` vanishes (e.g., a hypothesis that `p` lies
    in a specific subgroup of `P` — the sort of "geometric" parabolic
    elements the current `uD D ∘ leviGL_E d ∘ leviGL_V0 g` actually
    captures). Less mathematically clean.

Round 7 consumers (`residual_levi_extract`, `residual_levi_build`)
already sidestepped `parabolic_decompose` via Option B, so this signature
change is **non-blocking** for the public theorems.

### Dead-end warnings

- **Do not** try to close `parabolic_decompose` directly with the current
  signature. The mathematical analysis above shows the statement is
  not provable in full generality — a parameter is missing.
- **Do not** modify the existing `uD` definition in place. Round 7's
  `residual_levi_extract` / `residual_levi_build` were proved against
  the existing `uD` shape; changing it would cascade.
- **Do not** try `linear_combination` on the residual `IsSkewB`-type
  identity — the constraint involves `λ` (lambda pairing on E × E') and
  `Cdual` which require `rw` chains, not coefficient manipulation.

### Diff summary

- `InducedOrbitToy/Slice.lean` lines 1078–1109: docstring updated to
  reflect partial progress and gap analysis.
- `InducedOrbitToy/Slice.lean` lines 1109–1518 (approx): proof body
  expanded from a bare `sorry` to a substantial structured calculation
  that establishes (1)–(7) above. The single remaining `sorry` is now
  inside an extensively documented Gap comment block.
- The pre-existing `Section 6.6` comment block (lines 1049–1077) is
  unchanged.
- All other declarations in the file are unchanged.
