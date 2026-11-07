# Generic coherence source correspondence

Pinned upstream: `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

- `Quillen/CategoryTheory/TheoremB/Naturality.lean`: its first five generic nerve-cylinder / realized homotopy lemmas now live in `Colib/Topology/ClassifyingSpace/Naturality.lean`, namespace `CategoryTheory`; the actual comma and fiber-map declarations live in `Colib/CategoryTheory/TheoremB/Naturality.lean`, namespace `CategoryTheory.TheoremB`.
- `Quillen/CategoryTheory/TheoremB/{FunctorIso,StructuredFunctorIso}.lean`: same basename under `Colib/CategoryTheory/TheoremB`, namespace `CategoryTheory.TheoremB`. These transport the genuine transition homotopy-equivalence condition along a natural isomorphism; they do not claim the unconditional Theorem B conclusion.
- `Quillen/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean`: functor-chain, simplex-family and triangle geometry declarations live in `Colib/Topology/ClassifyingSpace/FunctorChain.lean` (`CategoryTheory`); inverse-isomorphism relative homotopies in `Colib/Topology/ClassifyingSpace/InverseHomotopy.lean` (`CategoryTheory`); `fiberLiftNullhomotopyHomotopy` in `Colib/Topology/HomotopyFiber/Nullhomotopy.lean` (`Topology.HomotopyFiber`); only the constant-natural-isomorphism nullhomotopies and induced fiber-lift homotopy remain in `Colib/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean` (`CategoryTheory.TheoremB`).
- `Quillen/Topology/ClassifyingSpace/FunctorChain.lean`: generic chain naturality and thin-target fixed-vertex theorem join native `FunctorChain`; the inverse-homotopy fixed-vertex theorem joins native `InverseHomotopy`.

No source aliases or Aglib imports. Actual source constructions and proofs are retained, with native namespaces and imports. Root product projections/extensionality are qualified to avoid collision with `CategoryTheory.Prod`.

Existing native `Comparison`, `StructuredComparison`, `Conditions`, `Comma.Transitions`, and `TheoremA.Conclusion` are reused unchanged from `output/theorem-b-native-a36cec7`. Existing realization and path-space foundations are reused from `output/serre-kzero-native-a36cec7`. Build artifacts in this isolated overlay are fallback symlinks, not cache copies. Missing old mathlib artifact links use the existing pinned-toolchain `live-main-integration-28fd2c9` artifact fallback.

The original migration used a finite-coordinate comparison layer. That layer has since been removed: the geometry now uses the pinned function-subtype `stdSimplex` and `SimplexCategory.toTopHomeo` directly. The triangle edge proof uses the native interval homeomorphism, preserving the orientation and exact `realizationInterval` path. The validation reports below describe the original migration, not the later coordinate rewrite.

`ColibTest/Topology/SerreIsoCoherence.lean` checks exact natural-transformation vertex paths, the inverse-homotopy initial face, its fixed source endpoint, the full two-parameter fixed-vertex property, fiber-lift projection and pointwise path coordinate. Nine separately printed endpoint dependencies contain only `propext`, `Classical.choice`, `Quot.sound`; no additional axioms or sorry dependencies. Audit-only commands live separately in `validation/Axioms.lean`, outside both library trees. The six substantive regression examples contain no hash commands or linter suppression.

Validation commands and outputs:
- `bash check.sh <owned files in dependency order>` uses pinned Lean 4.34.0-rc2, the shared serial wrapper, `autoImplicit=false`, `warningAsError=true`, and the standard mathlib linter set. Original complete production build output: `strict-build.log`. Final six-example regression rebuild output: `regression-build.log`.
- Cached mathlib `lint-style` over temporary import hubs of all eight owned production files and the regression file passed without diagnostics; output: `text-lint.log`. Temporary hubs were removed.

Final independent axiom audit: `validation/Axioms.lean`, run with command-line `-Dlinter.hashCommand=false` only; output `axiom-audit.log`. The original full production build log is preserved unchanged.
