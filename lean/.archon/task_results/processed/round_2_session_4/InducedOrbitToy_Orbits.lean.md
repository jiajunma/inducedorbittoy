# InducedOrbitToy/Orbits.lean

## Round 2 status

**Assigned-but-deferred file.** Per `PROGRESS.md` (Round 2) and
`task_pending.md`, `Orbits.lean :: sIndependenceAndOrbitCriterion`
is **Tier A (deferred to next round)** — it depends on
`pNormalForm_residual_orbit_iso` (NormalForm.lean line 199, the
companion Round 2 target) landing first. Round 2 was assigned a single
NormalForm.lean prover, with this file's continuation deferred to
Round 3.

This round's work on `Orbits.lean`:

- Confirmed file still compiles in isolation and as part of `lake build`.
- Confirmed no `axiom` declarations introduced in this file.
- **Made the partial progress concrete in the proof body**: extracted
  the conjugating-isometry witness `g` (forward direction) and the
  bilinear-isometry witness `h : L0' ≃ₗ[F] L0'` (reverse direction).
  These are the structural steps that *do not* require the missing
  `Nondegenerate`/`(2 : F) ≠ 0` hypotheses; they were left implicit
  in Round 1's commentary and are now visible in the code (lines
  259–284 of the revised file).

Net change: the two scoped sorries inside
`sIndependenceAndOrbitCriterion` remain (still 2 of them), but their
prefixes now contain real proof steps documenting exactly what is
extracted before the genuinely-stuck point.

## Compilation status

- `lake env lean InducedOrbitToy/Orbits.lean` ✅ — single
  expected warning at line 242 (`sIndependenceAndOrbitCriterion`),
  matching what was there before this round.
- `lake build` initial replay ✅ (post-edit, before parallel
  NormalForm prover landed changes); the same 8 declaration-use
  `sorry` warnings as before.
- A subsequent `lake build` failed in **NormalForm.lean** (lines
  300, 304 — `show` pattern not definitionally equal in the
  parallel prover's `pNormalForm` work). That breakage is **not**
  in this file; `Orbits.lean` continues to compile in isolation.
  The plan agent will reconcile the NormalForm prover's output
  separately.
- `lean_verify` axiom check: `inducedOrbits` uses only the standard
  trio (`propext`, `Classical.choice`, `Quot.sound`); `main` and
  `sIndependenceAndOrbitCriterion` resolve via `sorryAx` (no custom
  axioms). No `axiom` declarations in this file.

## sIndependenceAndOrbitCriterion (line 242) — IN PROGRESS

### Forward direction (lines 252–273) — partial progress

#### Approach
1. From the orbit-equality hypothesis `horbit`, derive that
   `XST S Sₕ₁ T₁ ∈ GOrbit S (XST S Sₕ₂ T₂)` by transporting along
   self-membership of the LHS orbit.
2. Self-membership uses the witness `(g := 1, hg := ⟨isUnit_one,
   fun _ _ => rfl⟩)` together with `Ring.inverse_one`. The residual
   `_ = 1 ∘ₗ _ ∘ₗ 1` reduces by `rfl` after rewriting
   `Ring.inverse 1 = 1`.
3. `obtain ⟨_g, _hg, _hyeq⟩` extracts the conjugating isometry from
   the unfolded orbit-membership witness.

#### Result
**IN PROGRESS** — scoped `sorry` at the *true* stuck point: showing
that `_g` is a `P`-element (i.e. `IsParabolicElement S _g`), then
applying `pNormalForm_residual_orbit_iso` to translate the conjugation
into a bilinear isometry.

#### Blocker (carry forward)
1. `pNormalForm_residual_orbit_iso` (NormalForm.lean line 199) is
   itself sorry — Round 2's NormalForm prover is the upstream.
2. That lemma requires `Nondegenerate` and `(2 : F) ≠ 0`, which are
   absent from `sIndependenceAndOrbitCriterion`'s signature.
3. The lemma also requires `Sₕ₁ = Sₕ₂` — but the public statement
   here allows distinct `Sₕ₁`, `Sₕ₂`. The blueprint outline implicitly
   assumes one passes through the existence half of `pNormalForm` to
   reduce the two-`Sₕ` case to the single-`Sₕ` case (then the residual
   `T` orbits coincide modulo a Levi adjustment). This is downstream of
   `pNormalForm` (NormalForm.lean line 167), the *other* Round 2 target.

### Reverse direction (lines 274–284) — partial progress

#### Approach
1. Unfold `IsometryRel S T₁ T₂ ↔ Bilinear.AreIsometric (BT S T₁) (BT S T₂)`
   via `unfold IsometryRel Bilinear.AreIsometric at hiso`.
2. `obtain ⟨_h, _h_isom⟩` extracts the bilinear-isometry witness:
   `_h : ↥S.L0' ≃ₗ[F] ↥S.L0'` and
   `_h_isom : ∀ u v, BT S T₂ (_h u) (_h v) = BT S T₁ u v`.

#### Result
**IN PROGRESS** — scoped `sorry` at the *true* stuck point: lifting
`_h` to a `P`-element `p` of `S.V` via the block-decomposition
`V = L_1 ⊕ L_0 ⊕ V_0 ⊕ L_1' ⊕ L_0'` (acting as `(_h⁻¹)^∨ ⊕ id ⊕ _h`),
then concluding orbit equality by mutual containment.

#### Blocker (carry forward)
Same triple as the forward direction: needs
`pNormalForm_residual_orbit_iso` + `Nondegenerate` + `(2 : F) ≠ 0` +
`Sₕ₁ = Sₕ₂` reduction (or extension of `pNormalForm_residual_orbit_iso`
to handle distinct `Sₕ₁, Sₕ₂`).

## Useful Mathlib / project lemmas leveraged this round

- `Ring.inverse_one (M₀ := Module.End F S.V)` for the orbit
  self-membership witness.
- `isUnit_one`, `LinearMap.IsOrthogonal` (definition only — `1` is
  trivially form-preserving by `rfl`).
- `IsometryRel`, `Bilinear.AreIsometric` — the two abstractions
  bridging this file with `NormalForm.lean`/`LocalForms.lean`.

## Negative search results / dead ends

- `1 ∘ₗ x ∘ₗ 1 = x` is **not** `rfl` directly when `x = XST S Sₕ T` (a
  multi-`let` definition) — but it *is* `rfl` after rewriting
  `Ring.inverse 1` to `1`. (`simp [Ring.inverse_one]` did not close;
  `rw [Ring.inverse_one]; rfl` did.) Carrying this forward as a
  micro-pattern.
- `LinearMap.one_eq_id` does **not** exist in the current Mathlib;
  use `(1 : Module.End F V) = LinearMap.id` definitionally or via
  `Module.End.one_def` if needed. (Not needed here — `rfl` suffices
  after `Ring.inverse_one`.)

## Hand-off to next round (Round 3)

Once `pNormalForm_residual_orbit_iso` lands in `NormalForm.lean`, the
remaining work in `sIndependenceAndOrbitCriterion` splits cleanly:

1. **Forward direction.** From the extracted `_g, _hg, _hyeq`:
   - Show `_g` preserves the slice `O0PlusU` (a parabolic-stability
     argument that uses `XST_sub_X0Lift_mem_unipotent` and the
     `IsometryEnd → IsParabolicElement` direction). This is the
     hardest sub-step and needs `Nondegenerate` + `(2 : F) ≠ 0`.
   - Reduce to the single-`Sₕ` case via the existence half of
     `pNormalForm` (NormalForm.lean line 167; Round 2 Tier A target).
   - Apply `pNormalForm_residual_orbit_iso` to extract the bilinear
     isometry.

2. **Reverse direction.** From the extracted `_h, _h_isom`:
   - Build `p` as `(_h⁻¹)^∨ ⊕ id ⊕ _h` on the block decomposition
     `V = E ⊕ V_0 ⊕ E'` (further decomposing `E = L_1 ⊕ L_0`,
     `E' = L_1' ⊕ L_0'` via `S.isComplL'` and the dual pairing).
   - Verify `IsParabolicElement S p` (modulo the Tier D
     `IsAdjointPair p p` autoformalization bug — same scoped sorry
     pattern as in `pNormalForm` body).
   - Show `p ∘ₗ XST T₁ = XST T₂ ∘ₗ p` reduces to the diagonal blocks
     via `XST_apply` and `_h_isom`.
   - Conclude orbit equality by mutual containment using
     `IsParabolicElement → IsometryEnd` (also currently blocked by the
     Tier D `IsAdjointPair` bug — round 4 fix required).

3. **Hypothesis-list reconciliation.** Round 3 should *also* propose
   adding `(_hNondeg : S.formV0.Nondegenerate)` and
   `(_hChar : (2 : F) ≠ 0)` to the public statement of
   `sIndependenceAndOrbitCriterion` (matching `pNormalForm` /
   `pNormalForm_residual_orbit_iso`'s signatures), and threading them
   through `main` (line 302). The current omission is an
   autoformalization oversight — they appear on every other public
   theorem in this layer.

## #print axioms (recorded for review)

- `inducedOrbits` → `propext, Classical.choice, Quot.sound` (standard,
  no custom axioms).
- `main` → resolves via `sorryAx` due to the embedded
  `sIndependenceAndOrbitCriterion` call (expected; no custom axioms).
- `sIndependenceAndOrbitCriterion` → `sorryAx` (the body's two scoped
  sorries; no custom axioms).
