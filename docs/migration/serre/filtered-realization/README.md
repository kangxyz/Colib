# Arbitrary filtered realization and compact HELP

## Proven endpoint

For any small filtered category `J`, actual diagram `F : J ⥤ SSet`, specified cocone
`c`, and proof `IsColimit c`, suppose every actual realized transition `F.map u`
has a homotopy equivalence whose forward map is exactly its realization. Then
`Topology.FilteredRealization.stageHomotopyEquiv F c hc e he j` is an actual
homotopy equivalence from `|F.obj j|` to `|c.pt|`. Its forward continuous map is
definitionally the realized cocone leg. The inverse and both inverse homotopies
are constructed, not supplied as hypotheses.

There is no monomorphism, injectivity, countability, sequential-index, or based
inverse hypothesis. The index and simplicial sets use the original common
universe. Compact-source factorization allows an independent source universe.

## Proof chain and exact maps

1. Finite subcomplex support and finite simplicial presentability factor each
   compact-source continuous map exactly through an original stage.
2. Compress a finite simplicial source through its finite image in the colimit.
   Realization of that image inclusion is an embedding. This detects equality
   of compact-source continuous maps at a later stage without injecting the
   original stages into the colimit.
3. Factor a compact homotopy-commuting square, detecting both endpoints
   simultaneously. Its entire homotopy is retained under the cocone map.
4. Genuine transition homotopy equivalences satisfy compact homotopy extension
   and lifting, preserving the prescribed boundary homotopy at every parameter.
5. The compact-open mapping-path endpoint lifts against all realized simplex
   boundaries. The existing relative-skeleton theorem extends this to every
   realized simplicial monomorphism.
6. The empty inclusion provides one inverse and its right inverse homotopy.
   The realized simplicial-cylinder endpoint inclusion provides the other
   inverse homotopy. No Whitehead theorem is assumed.

## Native ownership and source comparison

Implementation source: Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The twelve source files retain the actual objects, forward maps, homotopies,
endpoint orientation, original mathematical hypotheses, and universes.

- The generic boundary-correction lemmas now belong to
  `Colib.Topology.Homotopy.BoundaryCorrection` and namespace `TopCat`. They use
  native `Mathlib.Topology.Homotopy.HSpaces` and `Path`, rather than importing a
  homotopy-fiber equivalence application.
- `MappingPath.Basic` retains the entire original declaration set, including
  its strict-fiber homeomorphism and arbitrary-parameter covering homotopy
  lifting. Its imports use the native homotopy-extension and homotopy-fiber
  foundations, with no backwards import of Theorem B.
- The coproduct cylinder endpoint map belongs to namespace `SSet`, and the
  realized endpoint lifting-to-homotopy construction belongs to `TopCat`.
- Existing native realization coproduct, cylinder, finite compactness,
  monomorphism HEP, relative skeletal lifting, mapping-cylinder and deformation
  retract results are reused directly. No alternate realization or adapter is
  introduced.
- The source's separate `isClosed_cubeBoundary` helper is not selected. It is
  not used in the retained general compact homotopy theorem.
- The source's `Realization.homotopyExtensionProperty_realizationBoundary`
  wrapper is not duplicated. Its consumer uses the already native general
  monomorphism HEP theorem directly.

## Validation and limits

The original local validation run serialized Lean through the shared lock,
compiled all twelve changed production leaves with the native strict options
and the in-package exact-map regressions, and inspected the transitive axiom
closures of 22 central declarations. Detailed source, command, log and output
bindings remain local. The axiom inspection permitted only `propext`,
`Classical.choice`, and `Quot.sound`. Current integrated checks use the
repository's `scripts/check.sh`.

The compatible native base is the separate integration checkout at `a36cec7`;
unchanged prerequisite artifacts are reused. This is changed-leaf verification,
not a fresh full-production build, independent mathematical review or kernel
replay. The final aggregate checks and Library IDs remain integration work.

The generic filtered-realization step is complete. Applying it to Serre
localization still requires the actual Serre index category and diagram,
filteredness, the colimit identification, and equivalences of actual
transition maps. None of those application-specific facts are claimed here.

No commit, push or publication has been performed by this worker.
