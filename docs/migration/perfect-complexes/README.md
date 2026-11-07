# Native Stacks perfect complexes

Colib uses `AlgebraicGeometry.RingedSpace.IsPerfectComplex` directly, from the pinned
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties` module.
The underlying category is its native `ObjectProperty.FullSubcategory` of actual cochain
complexes. Morphisms are the original chain maps. There is no separately maintained Aglib
perfectness predicate, compatibility spelling, local-model category or adapter equivalence.

The upstream `Stacks.Cohomology.PerfectComplexes.IsPerfectComplex` spelling is definitionally
equal, as recorded by upstream `PerfectComplexes.IsPerfectComparison`; Colib does not add
another comparison. Derived-object statements use the upstream `RingedSpace.IsPerfect`.
A derived localization is not substituted for the chain category used by Waldhausen K-theory.

## Mathematical constructions retained

- `COL-0177`, `Waldhausen.complexes`: the generic structure on cochain complexes in an
  abelian category, with the actual zero, monomorphisms and quasi-isomorphisms.
- `COL-0178`, `RingedSpace.perfectComplexesWaldhausen`: the structure on the native perfect
  full subcategory. The actual cone-to-quotient quasi-isomorphism proves quotient closure
  for short exact sequences; the pushout short exact sequence proves closure for every
  displayed pushout along a monomorphism. The generic cofibration-closed-subcategory
  construction then retains the original zero, maps and weak equivalences.
- `COL-0179`, `Waldhausen.KEquivOfExactEquivalence`: the generic theorem that two-sided exact
  categorical equivalences induce mutually inverse canonical K-maps. It is not specific
  to any perfectness comparison, and does not require strict chosen-zero preservation.

Stacks supplies perfectness, cone closure, quasi-isomorphism invariance and representative
independence. Colib supplies the Waldhausen structures absent from the pinned upstream
library. These structures add mathematics on upstream objects rather than translate between
parallel perfect-complex models.

## Direct regressions

`ColibTest.PerfectWaldhausen` tests the native full subcategory alone: its actual zero,
cofibrations, weak equivalences, short exact quotients, ambient and subcategory pushouts,
and exactness of the inclusion into all cochain complexes.

`ColibTest.PerfectKTheory` checks the actual canonical K-map, identity and composition laws,
the reflexive exact-equivalence application, and the based homotopy-group formula on the
same native Waldhausen structure. It imports no private test implementation.

## Open restriction on the native objects

`COL-0229` proves that restriction to an open ringed subspace preserves the native
perfect-complex predicate. For a scheme `X` and `U : X.Opens`, ordinary degreewise
restriction to `U.toScheme` is Waldhausen-exact: it preserves zero objects,
monomorphisms, quasi-isomorphisms and displayed pushouts along monomorphisms.

`COL-0230` defines the resulting homomorphism on the existing nonnegative Waldhausen
K-groups. It is exactly the existing canonical `Waldhausen.KMap` of that restriction
functor, with no intermediate category or alternative perfectness predicate.
`ColibTest.PerfectRestriction` checks its literal degreewise objects and maps,
exactness properties and equality with the canonical K-map.

These results concern literal open subschemes. The pinned Quillen
`PerfectComplexes/Restriction.lean` uses an archived strict-perfect category and
arbitrary open immersions; its `Quillen/Aglib/.../PerfectComplexes/Restriction.lean`
uses an archived locally-perfect category. The new results do not identify either
model with Stacks perfect complexes or claim equality with archived `StrictK`.
Arbitrary-open-immersion generality, nested restriction coherence and localization
remain separate mathematical work.

## Removed comparison and permanent identifier

The former `LocalRepresentativeComparison` and `LocalRepresentativeEquivalence` modules,
their local-model tests, and the reconstructed source/target structures are removed.
`COL-0176` is retired, not reassigned. Its permanent page records the retirement and links
to the previous source revision. The removed comparison remains available in Git history; no old Aglib data or reconstructed
model is retained in the maintained tree. The maintained surface is recorded in
[source-crosswalk.json](source-crosswalk.json).

This change does not identify global bounded finite locally free complexes with Stacks
`StrictlyPerfect.IsStrictlyPerfect`: the latter requires global finite-free retract terms.
It also does not claim an equivalence with archived named `PerfectK`, Q/S comparison,
negative K-groups, or a nonconnective spectrum.

## Validation

Use `scripts/check.sh` for native builds, in-package tests, declaration and text lint,
production axiom auditing, compiled Library export and the website. Compilation,
source correspondence and independent mathematical review remain separate claims.
