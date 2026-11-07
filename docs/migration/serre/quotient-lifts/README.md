# Native Serre lift geometry draft

Baseline: `a36cec736`. Source adaptation: Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

## Owned sources

- `Colib/CategoryTheory/Localization/Lifts.lean`: actual full subcategory of costructured arrows whose structure morphism is invertible; nonemptiness, filteredness and cofilteredness from the native left/right fraction calculi. General declarations are in `CategoryTheory.Localization`.
- `Colib/CategoryTheory/Abelian/SerreClass/Lifts.lean`: Serre specialization, fixed-target monomorphism and fixed-source epimorphism lifts; surjective subobject map preserving binary meets and joins; Serre quotients of nested equal-image endpoints; actual interval lifts, join semilattice, nonemptiness, endpoint and cokernel comparison maps. Serre declarations use `CategoryTheory.ExactCategory.SerreLocalization`.
- `Colib/KTheory/Quillen/Localization/Serre/AuxiliaryLift.lean`: fixed-target admissible span lifts and actual Q-arrow lift through existing `mapQ`; compatibility with actual span upper/lower subobjects.
- `ColibTest/SerreLifts.lean`: separate-universe clients for general filtered/cofiltered lift categories and Serre subobject/interval statements.

All mathematical declarations from the two assigned source files are retained. General declarations moved to the general localization owner; Q and Devissage references use the existing native `QConstruction` and `Abelian.Devissage` owners. No Aglib imports, parallel quotient models, assumed lifting conclusions, new axioms, or placeholders.

## Dependencies and validation

Pinned Mathlib `Localization.CalculusOfFractions`, `Abelian.SerreClass.Localization`, `Subobject.Lattice` supply all general prerequisites. Existing Colib `Serre/Basic.lean` supplies actual `mapQ`; existing `Abelian/Devissage/SpanLayers.lean` supplies span endpoints. No new dependency sources were needed.

The four source/test modules compile using `/tmp/serre-lifts-compile.sh`, with the mandated serial Lean wrapper, `autoImplicit=false`, `warningAsError=true`, and `weak.linter.mathlibStandardSet=true`. The `.lake` overlay contains symlinks to existing dependency artifacts, not copied caches. `compile.log` records the final compile. `CheckAxioms.lean` and `axioms.log` are development-only endpoint checks: all nine checked endpoint declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

This is source compilation and endpoint axiom checking, not independent mathematical review or a repository-wide `scripts/check.sh` run. No git state was changed, no Library identifiers were reserved, and no shared catalogs were edited. Parent integration should register the mathematical item(s), imports, and final native checks.
