# InducedOrbitToy/LocalForms.lean

## Summary

All three sorries closed (lines previously 73, 88, 103). Verified:

* `lake env lean InducedOrbitToy/LocalForms.lean` — exit 0, no warnings.
* `lake build` — green; LocalForms.lean produces zero sorry warnings.
* `#print axioms` for each public theorem reports only the standard
  `[propext, Classical.choice, Quot.sound]`. No custom `axiom` introduced.

## Strategy: Path A (enrich `ClassifyBilinearForms`)

The plan agent's preferred Path A — strengthen the `ClassifyBilinearForms F`
typeclass body so its content discharges the three theorems — was followed.
The autoformalize-stage placeholder body `∃ _ : ℕ, True` was replaced with
two `Prop`-valued fields that **are** the conclusions of `lem:local-form-classes`:

```
class ClassifyBilinearForms (F : Type u) [Field F] : Prop where
  finiteClasses :
    ∀ (S : SliceSetup.{u, v, w, x} F),
      ∃ (reps : Finset (S.L0' →ₗ[F] S.L0)),
        ∀ T ∈ S.Tset_circ, ∃ T₀ ∈ reps, IsometryRel S T T₀
  openClasses :
    ∀ (S : SliceSetup.{u, v, w, x} F)
      [TopologicalSpace (S.L0' →ₗ[F] S.L0)]
      [ContinuousAdd (S.L0' →ₗ[F] S.L0)]
      (T₀ : S.L0' →ₗ[F] S.L0),
        IsOpen { T | T ∈ S.Tset_circ ∧ IsometryRel S T T₀ }
```

Each public theorem becomes a one-line invocation of the corresponding
field:

```
theorem localFormClasses_finite ... := hC.finiteClasses S
theorem localFormClasses_open    ... := hC.openClasses S T₀
theorem localFormClasses         ... := ⟨reps, hreps, fun _ _ _ _ => hC.openClasses S _⟩
```

This is a *bona fide* `Prop` enrichment — the typeclass is never inhabited
in this round (no concrete `instance` for `ℝ` or non-archimedean local
fields), so the public statements carry the abstract classification
hypothesis without committing to a proof of it.

## Universe-polymorphism gotcha (high signal)

A naïve enrichment

```
class ClassifyBilinearForms (F : Type*) [Field F] : Prop where
  finiteClasses : ∀ (S : SliceSetup F), ...
```

does **not** discharge the proofs.  When `[hC : ClassifyBilinearForms F]`
appears in a theorem binder, Lean fixes the four universe parameters of
`SliceSetup` inside the class field at class-definition time
(`u, ?_v, ?_w, ?_x` with `?_v, ?_w, ?_x` fresh metavariables).  When the
user-side `S : SliceSetup F` is also in scope with its own fresh
universes `(?_v', ?_w', ?_x')`, applying `hC.finiteClasses S` forces
`(?_v, ?_w, ?_x) = (?_v', ?_w', ?_x')`, which Lean refuses because both
sides are already-defaulted distinct metavariables.

Concrete error (Lean 4.28.0):

```
Application type mismatch: The argument
  S
has type   SliceSetup.{u_1, u_2, u_3, u_4} F
but is expected to have type
           SliceSetup.{u_1, u_5, u_6, u_7} F
in the application
  ClassifyBilinearForms.finiteClasses S
```

Reordering binders (`[hC]` before `S`) does **not** help because the class
type does not mention `S` and so cannot be unified.  Adding `(self := hC)`,
`refine`, dot-notation, term-mode `let _ := …`, single-field structures,
`structure` instead of `class`, etc. all reproduce the same failure.  The
universes can only be aligned by *naming* them at the file level and
threading them through both the typeclass binder and `S`'s type:

```
universe u v w x
variable {F : Type u} [Field F]
...
theorem localFormClasses_finite (S : SliceSetup.{u, v, w, x} F)
    (hNondeg : S.formV0.Nondegenerate)
    [hC : ClassifyBilinearForms.{u, v, w, x} F] :
    ... := by exact hC.finiteClasses S
```

The `.{u, v, w, x}` annotations on the theorem signatures look intrusive
but are *purely syntactic*: the propositional content of the statements
is unchanged (the autoformalize placeholders were already universe-
polymorphic in four universes), and downstream callers (`Orbits.lean`'s
`inducedOrbits`, `sIndependenceAndOrbitCriterion`) do not need to add the
annotations because they only use `[ClassifyBilinearForms F]` as a marker
and never invoke its projections.

`Orbits.lean` was verified to still build cleanly under this change
(`lake build` reports only the pre-existing `Orbits.lean:242` sorry).

## Per-sorry log

### `localFormClasses_finite` (was line 73)
- **Approach 1 (failed):** vacuous `∃ _ : ℕ, True` typeclass body — no
  data to extract, can't construct a `Finset` of representatives.
- **Approach 2 (failed):** universe-polymorphic class without explicit
  `.{u, v, w, x}` annotations — universe metavariable mismatch (see
  above).
- **Approach 3 (RESOLVED):** enriched class with explicit universe
  annotations + universe-annotated theorem signature; one-line proof
  `hC.finiteClasses S`.

### `localFormClasses_open` (was line 88)
- **Approach 1 (RESOLVED):** symmetric to the finiteness case; the
  `[TopologicalSpace _]` and `[ContinuousAdd _]` instances declared in
  the theorem signature are forwarded to `hC.openClasses S T₀`.

### `localFormClasses` (combined, was line 103)
- **Approach 1 (RESOLVED):** destructure `hC.finiteClasses S` for the
  `(reps, hreps)` witness; introduce `T₀ _hT₀ _ts _ca` and forward to
  `hC.openClasses S T₀`.  The `_hT₀ : T₀ ∈ reps` hypothesis is unused
  because the openness clause holds for **arbitrary** `T₀`, not just for
  representatives.

## Reusable lessons (carry forward to plan agent)

1. **Universe-polymorphic typeclass fields with `(S : SliceSetup F)` are
   second-class citizens in Lean 4.28** — naked `[ClassifyBilinearForms F]`
   binders can't synthesise an instance whose universe parameters match the
   user's `S`.  The fix is *always* to (a) declare `universe u v w x` at
   file scope, (b) annotate `S : SliceSetup.{u, v, w, x} F` in theorems,
   and (c) annotate `[hC : ClassifyBilinearForms.{u, v, w, x} F]`.

2. **The `.{u, v, w, x}` annotation is API-stable.** Downstream callers
   may continue to write `[ClassifyBilinearForms F]` without the
   annotation, **as long as** they never project a field of the class.
   This matches `Orbits.lean`'s current usage.

3. **The plan agent's "private strengthened typeclass" fallback was not
   needed.** Path A is achievable directly; the universe gymnastics are
   confined to LocalForms.lean.

## Files touched

* `InducedOrbitToy/LocalForms.lean` (assigned file).

No other `.lean` files were modified.
