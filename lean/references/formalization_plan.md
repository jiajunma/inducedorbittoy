# Formalization Plan for `blueprint_verified.md`

This project should follow Archon's staged workflow. The current stage is
`autoformalize`: create a Lean skeleton that compiles with `sorry`, matching the
informal blueprint and preserving theorem boundaries.

## Source Blueprint

Use
`../Rethlas/agents/generation/results/induced_orbit_toy_problem/blueprint_verified.md`
as the authoritative source. The main sections are:

1. `lem:x0-geometry`
2. `lem:parametrize-x0-plus-u`
3. `lem:unipotent-conjugation`
4. `prop:p-normal-form`
5. `prop:kernel-image`
6. `lem:local-form-classes`
7. `prop:induced-orbits`
8. `prop:s-independence-and-orbit-criterion`
9. `prop:multiplicity`
10. `thm:main`

## Lean Module Split

Use these files:

- `InducedOrbitToy/Basic.lean`
- `InducedOrbitToy/X0Geometry.lean`
- `InducedOrbitToy/Slice.lean`
- `InducedOrbitToy/NormalForm.lean`
- `InducedOrbitToy/LocalForms.lean`
- `InducedOrbitToy/Orbits.lean`
- `InducedOrbitToy.lean`

Each module should import the previous dependency layer only. The root
`InducedOrbitToy.lean` should import all submodules.

## Scope Decisions

- Work over a general field `F` first, with explicit hypotheses such as
  `[Field F]`, `[CharZero F]`, and finite-dimensionality. Do not try to encode
  the full non-archimedean local-field infrastructure in the first skeleton.
- Use Mathlib's linear algebra wherever possible. Prefer existing definitions
  for bilinear forms, submodules, ranges/kernels, linear equivalences, and
  finite-dimensional dimensions.
- Do not introduce `axiom`. If a theorem depends on local-field classification
  or topology not immediately available in Mathlib, state that dependency as a
  hypothesis or as a lemma with `sorry` for the proof.
- Keep notation close to the blueprint, but Lean names should use ASCII:
  `x0Geometry`, `parametrizeX0PlusU`, `unipotentConjugation`,
  `pNormalForm`, `kernelImage`, `localFormClasses`,
  `inducedOrbits`, `sIndependenceAndOrbitCriterion`, `multiplicity`, `main`.

## Suggested Structures and Definitions

In `Basic.lean`, bundle recurring data so later statements are not overloaded
with arguments:

- A predicate for `epsilon`-symmetric bilinear forms.
- A predicate for skew-adjoint endomorphisms relative to a bilinear form.
- A structure for the `X0` setup: `V0`, form on `V0`, `X0`, nilpotence if
  needed, `c = finrank F (ker X0)`, complement `Vplus`, and decomposition
  hypotheses.
- A structure for the parabolic slice setup: spaces `E`, `E'`, pairing
  `lambda`, subspaces `L1`, `L0`, `L1'`, `L0'`, and the induced ambient space.

If direct sums of arbitrary vector spaces become cumbersome, use product types
or bundled direct-sum constructions consistently. The first autoformalization
goal is a coherent API, not finished proofs.

## Risk Notes

- The orbit-closure and component-group statements are the highest-risk part.
  During autoformalization, it is acceptable to define the relevant predicates
  abstractly and leave the hard classification statements as theorems with
  `sorry`.
- `lem:x0-geometry`, `prop:kernel-image`, and the block formulas in
  `Slice.lean` are the best first proof targets after autoformalization because
  they are mostly finite-dimensional linear algebra.
- The local-form classification should be isolated in `LocalForms.lean` so that
  later proof agents can replace broad assumptions with Mathlib-supported
  statements incrementally.
