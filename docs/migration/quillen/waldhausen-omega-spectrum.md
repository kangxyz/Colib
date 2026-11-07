# The actual connective Waldhausen Omega-spectrum

COL-0282 proves that every loop structure map of the actual iterated
quotient-row S-construction is a weak homotopy equivalence. This includes
path components and all finite based homotopy sets, at every source point.
The zero structure map remains the identity. No saturation, cylinder,
extension or Omega-spectrum assumption is added to the original Waldhausen
structure.

## Original maps and complete continuous families

The original augmented path diagram adds an initial row. Its ordinal clamp,
section and augmentation give the genuine simplicial contraction. The zero
rows have all arrows weak. Native bisimplicial realization and induction
therefore prove contractibility of each realized path stage.

Higher first/tail additivity is proved on the actual quotient rows. Its
fiber comparison retains the actual source coordinate and the whole path,
not merely its endpoints or a homotopy class. The original relative cylinder
lifts every original S-cylinder, with its complete time coordinate. The
identity `stageCylinderLoop_eq` identifies the resulting cylinder loop with
the literal `stageLoopMap`. The contraction of the path source, full fiber
comparison and cancellation of weak equivalences prove `stageLoopMap_weak`.

`Topology.LoopPrespectrum.IsOmega` is a property of the existing native
prespectrum. Its `OmegaSpectrum` is Mathlib's full subcategory for that
property; it does not duplicate the spaces, structure maps or morphisms.
`omegaSpectrumFunctor` lifts the original prespectrum functor on the same
native strict chosen-zero wide subcategory. Original category object and
morphism universes remain independent, with spectrum universe their maximum.

`originalOmegaSpectrumMap` retains the original strict-zero exact map.
For arbitrary exact functors, `exactOriginalOmegaSpectrumMap` packages the
existing canonical-zero-rebased map unchanged. The previously proved
zero-space naturality retains the original public `KMap`, including K-zero.
Source and target exact functors retain the original common universe pair.
This result does not assert nonconnective K-theory or spectrum localization.

## Source and literature correspondence

The implementation adapts Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving authorship and Apache-2.0
notices. Its `Quillen/Waldhausen/SConstruction/Iterated/Interchange`,
`PathObject`, `Additivity`, `FiberComparison`, `OmegaSpectrum` and `ExactMaps`
supply the unchanged maps and proof obligations. The first five ordinal
identities from `RelativeCylinder` have their lower `RelativeTime` owner;
the unused degree-zero relative-cylinder chain is not claimed as migrated.
The path-diagram algebra has its categorical owner, while realization and
contractibility remain in topology and K-theory. Generic cylinder comparison,
contractible maps and bisimplicial contractibility retain their lower native
owners rather than introducing application-specific copies.

Thomason--Trobaugh, Section 1.5.3, page 260, supplies the iterated-S
Omega-spectrum background. The formal endpoint records the precise actual
structure maps and weak-equivalence conclusion. The native path-space and
full-parameter comparison proofs are documented as implementation refinements.

## Verification boundary

The three source components passed strict Lean 4.35 compilation, focused
regressions, native text and declaration lint, and production axiom checks.
Regressions retain the original maps, all stages, path components, finite
homotopy sets, universe parameters and exact-functor KMap. Integration
revalidates changed tags and all affected coherent-track consumers before
its own original whole-library CI. A prior candidate's success does not
certify later changed sources. No local whole-library pass, kernel replay
or separate downstream-client check is inferred from these focused results.
Detailed internal validation records remain outside the repository.
