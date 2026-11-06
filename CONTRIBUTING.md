# Contributing to Colib

Read docs/ARCHITECTURE.md for source ownership and docs/LIBRARY.md for mathematical items and
references. Follow the pinned Mathlib naming/style conventions and Stacks' source-correspondence
practice. The actual mathematical statement and selected interfaces determine placement.

## Assignments and concurrent work

Before editing, record the exact mathematical target, source/version/locator, Library section,
chosen definitions, proof obligations and owned paths in the assigned task or pull request.
Coordinate any new ID or shared chapter/bibliography edits with the other contributors. Use
separate branches or worktrees for overlapping changes. Other agents may be editing the checkout.
Preserve their work and serialize Git index/HEAD operations.

For a new item, reserve the next unused COL identifier in the assignment before creating its
entry file. One item has one entry file, so independent contributions have disjoint write owners.
The section order determines reading position. No approval is added for
routine choices inside an already authorized assignment.

## Mathematical and code style

- Search the Library, pinned Mathlib and Stacks first. Reuse their actual mathematical objects.
- Extend the native namespace. File prefixes record implementation ownership, while declarations
  use the mathematical object's namespace.
- Locate general algebra under Algebra or RingTheory, categorical primitives under CategoryTheory,
  sheaf/module constructions at their generic owner, and scheme specializations under
  AlgebraicGeometry. Applications consume those foundations through precise lower imports.
- Use modern module headers and the weakest appropriate public/private imports. Keep generic
  utilities below their applications. Generate the root entry with Mathlib mk_all.
- Use descriptive Mathlib-style names. Proposition/theorem names describe their conclusion,
  definitions identify the constructed object and naturality equations name the actual map.
- Preserve hypotheses, coefficients, universes, cohomological degrees, signs and canonical maps.
  State a genuine specialization or comparison explicitly in its reference annotation.
- Prefer short reusable proofs with explicit mathematical intermediate facts. Follow native
  simp and typeclass conventions and satisfy the pinned linters.
- Document public mathematical endpoints. Independently citable items receive permanent tags;
  ordinary supporting declarations can carry precise citations through their native Lean names.
  Preserve author, license and implementation provenance when adapting code.
- Production has no placeholders, new axioms or native_decide. Its transitive axiom closure uses
  only propext, Classical.choice and Quot.sound.

The normative external guides are
[Mathlib naming](https://leanprover-community.github.io/contribute/naming.html),
[Mathlib style](https://leanprover-community.github.io/contribute/style.html), and
[Stacks conventions](https://github.com/AxiomMath/Stacks/blob/f8e70c5dd04bfabcb423d5e325461f527c85a5d6/CONTRIBUTING.md).

## Work and validation

Prove and compile the changed leaf with its actual prerequisites. Retain completed artifacts and
compatible validation. If a needed lower primitive is in a higher application, extract the
minimal lower interface while preserving its hypotheses and consumers.

Update the item's kind, section, conditions and scope in its entry file.
Attach `@[colib_tag]`, existing `@[stacks]` and applicable `@[colib_ref]` annotations in Lean.
Add a checked bibliography record for each new paper or book. The generated declaration mapping
and references are consumed by the Library build.

At meaningful final delivery run the applicable native build, in-package tests, declaration and
text lint, generated-entry check, production axiom audit and Library validation through
scripts/check.sh. Reuse categories whose inputs are unchanged after a repair. Doc/website-only
changes use the compatible native export with their changed source/tooling checks. See
scripts/README.md and docs/DEVELOPMENT.md for commands.

New `ColibTest` modules are discovered automatically by the Lake test driver and text
linters. Do not add handwritten test-module lists to the workflow or check script.

A change reports its source revision, exact mathematical scope, literature correspondence,
commands and retained evidence. Independent review records its actual scope. Kernel replay and
separate downstream/client checks require an explicit user request. Push authorization belongs
to the active assignment.
