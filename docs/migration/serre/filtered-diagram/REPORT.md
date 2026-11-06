# Native Serre auxiliary filtered-diagram proof

## Result

All 55 named declarations from the six assigned pinned source files are migrated with their actual maps and conclusions. The native `quotientAuxiliaryNerveCoconeIsColimit` proves the universal property of the nerve of the actual isomorphism structured comma. The transition equivalences have precisely the realized postcomposition functor as their forward maps.

Source commit: `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Baseline: `output/serre-kzero-native-a36cec7`, corresponding to published `a36cec736`.

## Source coverage

| Pinned source file | Named declarations | Native owner |
|---|---:|---|
| AuxiliaryIsoComma | 12 | `Colib/KTheory/Quillen/Localization/Serre/AuxiliaryIsoComma.lean` |
| AuxiliaryPostcompose | 4 | `Colib/KTheory/Quillen/Localization/Serre/AuxiliaryPostcompose.lean` |
| AuxiliaryDiagram | 9 | same path, plus generic compatible-functor extensionality below |
| AuxiliaryArrowLift | 12 | `Colib/KTheory/Quillen/Localization/Serre/AuxiliaryArrowLift.lean` |
| AuxiliaryRefinement | 6 | same path, plus generic inflation faithfulness below |
| AuxiliaryColimit | 12 | `Colib/KTheory/Quillen/Localization/Serre/AuxiliaryColimit.lean` |

Full declaration-level mapping: `declaration-map.json`.

The main namespace is `CategoryTheory.ExactCategory.SerreLocalization`. General-purpose results are assigned to native lower owners:

- `Colib/CategoryTheory/QConstruction/FunctorExt.lean`: `CategoryTheory.QConstruction.CompatibleFunctor.ext_toFunctor`, with independent source/target object and morphism universes.
- `Colib/CategoryTheory/QConstruction/Abelian/InflationFaithful.lean`: `CategoryTheory.QConstruction.inflationArrow_injective`, with independent object/morphism universes.
- `Colib/CategoryTheory/Functor/FullSubcategoryExt.lean`: `CategoryTheory.Functor.ext_of_comp_fullSubcategory`, with independent source/target object and morphism universes. This is the supporting native proof extracted from the pinned FullSubcategoryExt dependency, beyond the 55 assigned declarations.

The six Serre files retain the original small-category universe. Their actual source and target categories, Q-spans, ordinary quotient arrows, chosen identifications, and commuting triangles are unchanged.

## Proof content

- Auxiliary quotient identifications are natural on actual representative Q-spans.
- Comparison functors retain the exact underlying ambient Q-object and Q-arrow.
- The strict cocone equation follows from the identity-component natural isomorphism, not an assumed comparison.
- A quotient-inverted Q-arrow lifts over its ordinary pushout, together with both endpoints. Whole-arrow lifting into the actual isomorphism comma retains both endpoint equalities and the exact triangle.
- Equal comparison objects become literally equal after an actual Serre-isomorphic denominator postcomposition obtained from the native calculus of fractions.
- The actual ordinary quotient-lift category indexes a strict Cat-valued diagram. Faithful legs, whole-arrow surjectivity, and eventual object equality prove its nerve cocone is a filtered colimit through the existing `CategoryTheory.FilteredNerveColimit` owner.
- Postcomposition homotopy equivalence uses the natural kernel-inclusion map and the already proved actual kernel equivalences. Its forward map is exactly postcomposition.

No Aglib or source Quillen imports, compatibility aliases, alternate Q-model, assumed colimit/HE conclusion, sorry, admit, axiom declaration, or unsafe definition was introduced.

## Dependencies

The isolated artifact overlay links current artifacts from:

- `serre-auxiliary-kernel-draft` for actual slice-Q categories, kernel equivalences and base change.
- `serre-comma-geometry-draft` for the actual isomorphism structured comma and its geometry.
- `serre-quotient-lifts-draft` for ordinary quotient-lift filteredness and fraction calculus.
- `serre-kernel-geometry-draft` for ordinary kernel geometry.
- Parent baseline plus existing native filtered-realization dependencies.

`overlay.py` creates symlinks only; it does not copy caches or artifacts. No shared checkout/catalog metadata, IDs, commit, or push was modified.

## Validation

`build.sh` uses the shared serial Lean lock and compiles with:

- `-DautoImplicit=false`
- `-DwarningAsError=true`
- `-Dweak.linter.mathlibStandardSet=true`

`ColibTest/SerreFilteredDiagram.lean` checks independent generic universes, exact underlying Q-arrows, strict identity/composition, actual filteredness, genuine denominator refinement, whole-arrow endpoint lifting, exact realization transition, actual comma nerve as cocone vertex, and colimit descent/factorization/uniqueness.

`ColibTest/SerreFilteredDiagramAxioms.lean` audits eight substantive endpoints. Every endpoint depends only on `propext`, `Classical.choice`, and `Quot.sound`.

Final aggregate log: `strict-validation.log` (nine implementation modules, regression client, and axiom audit). Earlier successful regression/audit log: `test.log`.
