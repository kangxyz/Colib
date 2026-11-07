# Mathematical organization

Colib develops cohomology and homotopy theory in algebraic geometry. Scheme and site
cohomology, finite correspondences and transfers, motivic constructions, exact-category
K-theory, and their homotopical comparison maps belong in their actual mathematical subjects.

The design follows Aglib's architecture at commit 1943d6eee4976a2d3a01b55e76d6d5890130ee63.
Use the Mathlib object and the pinned Stacks extension first. A module prefix records source
ownership. Declaration namespaces identify the mathematical object.

General algebra and categorical primitives precede site and sheaf operations. Those precede
scheme-specialized constructions and their motivic or K-theoretic applications. Select precise
imports from the implemented dependency graph.

Choose one canonical model for each object or map. A comparison retains actual object classes,
symbols, canonical maps, coefficient actions and signs. A field or finite-type specialization
keeps its hypotheses. Finite-dimensional, finite length, finite presentation, and local
freeness have separate interfaces.

The initial K-group uses CategoryTheory.GrothendieckGroup on Mathlib's FGModuleCat. The
canonical Milnor group is Stacks' MilnorKTheory. The earlier pair-symbol relation occurs
only at its comparison boundary. The affine cycle coefficient uses Mathlib's module length
and prime localizations. Its actual statement is about fields, rings and modules, so its
source owner is `Colib.RingTheory.Length.FiniteAlgebra`. The cycle chapter consumes that
result in its mathematical reading route. The initial cycle import provides a compatibility
reexport to the canonical ring-theoretic implementation.

The Library is the mathematical organization centre described in [LIBRARY.md](LIBRARY.md).
Chapters contain sections and typed permanent items. Defining modules and code imports come from Lean; the chapter and section sequence supplies
the reading organization. Lean annotations bind declarations and precise references to those items.
Bibliographic identity and editorial statements each have one maintained owner. Signatures,
defining modules and implementation references are generated from the compiled environment.
[CONTRIBUTING.md](../CONTRIBUTING.md) owns Mathlib/Stacks-aligned code style and agent assignments.

## General K-theory and ring or scheme applications

`Colib.KTheory` owns the general theory of exact and Waldhausen categories:
Grothendieck groups, Quillen K-groups, comparisons, resolution, devissage, Serre
localization, finite-support decompositions, additivity, approximation, fibration,
Gillet-Waldhausen and cofinality. A theorem about an arbitrary exact or Waldhausen
category stays here even when a later application uses modules or perfect complexes.

`Colib.RingTheory.KTheory` owns ring and field applications: finite-module dimension,
Milnor K-theory, finite-projective group completion, ring and field Quillen comparisons,
finite-field computations, finite-module G-localization, and scalar operations specialized
to module categories.
`Colib.AlgebraicGeometry.KTheory` owns K-theory of schemes and their perfect complexes.
Ring and scheme layers import the general theory, never the other way around.
Geometric categories and their exact structures keep their existing geometric owners.
General linear-category scalar operations stay in the general layer; their finite-module
specializations have a separate ring-owned module.

These are source owners, not replacement mathematical models or declaration namespaces.
Declarations continue to extend `CategoryTheory.ExactCategory`, `CategoryTheory.Waldhausen`,
`MilnorKTheory`, `ModuleCat.FiniteProjective`, `FGModuleCat` and
`AlgebraicGeometry.Scheme.Modules`, as appropriate. Moving a file does not introduce an
alias, an adapter or a compatibility reexport. Consumers import the new defining module.

The Library keeps **General algebraic K-theory** separate from **Algebraic K-theory of
rings and schemes**. Permanent item IDs, hypotheses, canonical maps, signs and references
survive a move. The chapter organization is a reading route; the actual Lean import graph
remains the authority for dependencies. `scripts/test_k_theory_layers.py` checks both the
chapter separation and the general layer's transitive independence from the application
layers.

## Source provenance

The architectural principles are adapted from
[Aglib](https://github.com/kangxyz/aglib/blob/1943d6eee4976a2d3a01b55e76d6d5890130ee63/docs/ARCHITECTURE.md).
The ordered-pair Steinberg relation retains the spelling from
[Aglib 2c34f185](https://github.com/kangxyz/aglib/blob/2c34f185fa859e862661f939cd216b07bcccfb26/Aglib/KTheory/MilnorK/K2/Basic.lean).
The portable CI workflow is adapted from that Aglib revision and retains its pinned native
auditor and action identities.
