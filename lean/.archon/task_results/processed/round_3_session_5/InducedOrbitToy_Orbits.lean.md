# InducedOrbitToy/Orbits.lean

## Round 3 status: NO WORK (file not assigned this round)

Per `PROGRESS.md` (Round 3), this file is **not** in the current
objectives. The single remaining sorry —
`sIndependenceAndOrbitCriterion` (line 242) — is a Tier-A deferred
target that depends on `pNormalForm_residual_orbit_iso` fully closing
in `NormalForm.lean`, which is itself Round 4/5 work. The PROGRESS
section "Files NOT assigned this round" explicitly lists
`InducedOrbitToy/Orbits.lean` and instructs non-objective-file provers
to verify isolation-compile, write a brief "no work" report, and
**not edit anything**.

## Verification

- **Isolation compile:** `lean_diagnostic_messages` on
  `InducedOrbitToy/Orbits.lean` returned exactly one diagnostic, a
  `warning: declaration uses 'sorry'` at line 242, column 9
  (`sIndependenceAndOrbitCriterion`). No errors. No new warnings.
- **No edits made.** The file body is byte-identical to its state at
  the start of the round (the prover did not invoke `Edit` or `Write`
  on `InducedOrbitToy/Orbits.lean`).

## Cross-file note

Mid-round build breakage in `Orbits.lean` is possible while the
sister provers on `Slice.lean` and `NormalForm.lean` are mid-flight,
because Round 3 changes the *signature* of `IsParabolicElement` (4th
conjunct: `IsAdjointPair … p p` → `LinearMap.IsOrthogonal … p`) and
the *statement* of `uD_isParabolic` (2nd argument: `uD D` → `uD (-D)`).

`Orbits.lean` does **not** consume `IsParabolicElement` or
`uD_isParabolic` directly — its only `NormalForm.lean` references are
type/structure-level (`IsSkewT`, `Tset_circ`, `XST`), and only
type-level for `Slice.lean` (`X0Lift`, `XST`, `XCB_apply`,
`X0Lift_apply`, `CST`, `BST`, `UnipotentRadical`, `XST_apply` is not
used). Therefore the Round-3 refactor of `IsParabolicElement` /
`uD_isParabolic` should not propagate into `Orbits.lean`. After the
sister provers land, end-of-round `lake build` should remain green
for `Orbits.lean` without any change here.

## Tier-A handoff for Round 5

When Round 4 closes `pNormalForm_residual_orbit_iso` in
`NormalForm.lean`, Round 5's prover for this file will need:

1. **The added hypotheses currently missing from
   `sIndependenceAndOrbitCriterion`:** `S.formV0.Nondegenerate`,
   `(2 : F) ≠ 0`. These are already documented in the file's docstring
   (lines 234–241) and in the in-line comments at lines 257–258 and
   281–282 as the gap.
2. **An equality `Sₕ₁ = Sₕ₂`** (or a stability statement
   showing the orbit is independent of `Sₕ`). The current statement
   distinguishes `Sₕ₁` and `Sₕ₂` because the blueprint criterion is
   on `T` alone, but the LHS encodes both; the prover-stage notes at
   lines 263–265 / 292–293 flag this.
3. **A parabolic-decomposition lemma** showing every `g ∈ G` with
   `g ∘ₗ XST T₁ ∘ₗ Ring.inverse g = XST T₂` lies in `P` (i.e. is an
   `IsParabolicElement`). This decomposition lemma does not exist in
   the current codebase and will need to be added — likely in
   `NormalForm.lean` as a converse to `pNormalForm`'s parabolic
   construction.

Both the forward and reverse directions of the iff (lines 251–276 and
277–294) already contain partial-progress witness extraction
(unpacking the `GOrbit` membership / unfolding `IsometryRel`); the
remaining `sorry`s are in the post-extraction step where the missing
hypotheses bite. Round 5's prover should **not** revert that partial
progress.

## Confirmation

- `#print axioms` was not run this round (no edits made; nothing to
  re-verify). The file's existing axiom footprint was confirmed clean
  (`[propext, Classical.choice, Quot.sound] + sorryAx` for the four
  declarations whose proof bodies still embed `sorry`s, all expected)
  during session 4 review (`PROJECT_STATUS.md`).
- `lake build` end-of-round status is delegated to the plan-agent
  post-round verification; `Orbits.lean` contributes no new warnings
  and no new errors.
