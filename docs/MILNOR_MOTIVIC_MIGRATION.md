# Milnor K-theory and Motivic migration plan

## Scope and fixed baseline

This plan covers the Milnor K-theory results and the Motivic-derived results present in Aglib,
including their necessary lower prerequisites. It is a plan for implementation. Completion and review claims are limited to the explicit
milestone records below and their declaration-level ledgers.

- Source Aglib revision: `101dbb8564fb0e29f28cfcb79168d878b5ab489f`.
- Initial Colib revision: `7603d2dba0e5c67646277ca269b76ec341bf3078`.
- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: `16edf57de7933555826307a3d81b4391a3657a09`.
- Stacks: `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`.

The initial static inventory identifies 186 Milnor modules within 301 Motivic-derived production
modules, with an Aglib production dependency closure of 350 modules. These numbers overlap;
they are not three additive workloads. Module counts are planning evidence, not declaration
coverage or a mathematical completeness certificate. Confirm the inventory against the fixed
source tree and its migration manifests, then reconcile every source declaration. The older
pilot revisions in [MIGRATION.md](MIGRATION.md) remain historical provenance.

Only Mathlib and Stacks are direct mathematical package dependencies. Mathlib's existing
transitive tooling packages are not additional mathematical libraries. Do not add Aglib,
Motivic, Quillen, or another application as a package dependency. Preserve the pinned basis;
a pin change is a separate compatibility decision, not a silent migration repair.

## Canonical objects and proof direction

Use Stacks' `MilnorKTheory` directly as the Milnor K-theory model. Rewrite source proofs against
its actual definitions, symbols, quotient relations and maps. Do not make an equivalence with
the complete Aglib model a prerequisite, and do not maintain a second general-purpose Milnor
K-theory implementation in Colib.

Search the pinned Mathlib and Stacks declarations before defining anything. Extend the native
mathematical namespace. A source model comparison is allowed only when a specific proof needs
it; keep that comparison local to its boundary, prove the exact generator/map equations it
uses, and do not expose a parallel downstream API. Reuse the existing degree-two comparison in
`Colib.RingTheory.KTheory.MilnorK.DegreeTwo` when relevant rather than recreating it. Its presence does not
require later results to factor through the pair presentation.

For every migrated statement preserve its actual field/ring/scheme assumptions, finiteness and
separability conditions, universes, coefficients, degree conventions, signs and canonical maps.
A theorem conditional on supplied norm data, compatibility, a reciprocity hypothesis, or a
complex structure remains conditional until those hypotheses are separately proved. Do not
replace a mathematical conclusion by a weaker statement and record it as full migration.

## Source reconciliation and evidence

Maintain a declaration-level migration ledger under `docs/migration/`, generated where possible
and reviewed where mathematical judgment is required. Record at least:

- Source repository, full revision, module, declaration name and original provenance/license.
- Exact statement and hypotheses, including implicit structures and universe parameters.
- Target owner, declaration or upstream declaration, and the selected canonical objects.
- Disposition: upstream reuse, direct proof rewrite, local comparison, prerequisite extraction,
  or unresolved obligation. Keep unresolved work visible; absence is not upstream reuse.
- Proof obligations, dependencies, source/literature locator and correspondence scope.
- Validation revision, commands, results and the relevant Library item, where applicable.

Reconcile source definitions, instances, public and supporting lemmas, notation and consumers.
When multiple source declarations become one upstream result, explain the statement-preserving
mapping. A removed alias still needs a ledger disposition. Include source tests as evidence of
intended interfaces, but do not count tests as migrated production theorems.

The 350-module closure is an upper bound on source modules needing inspection, not an instruction
to copy them. Replace dependencies by upstream results wherever possible. Extract only the
minimal missing lower primitive when a source proof depends on a higher application module.
Record exclusions with a concrete reason and show that no selected result is lost.

## Pinned upstream audit before construction

Audit the pinned Stacks interfaces before assigning any new mathematical construction, especially
intersection theory, cycles, finite correspondences and the Nisnevich site. These subjects may
already have the needed objects and lemmas upstream. Do not infer a gap from Aglib's old imports
or from a missing result under the same name. Inspect the actual declaration, defining module,
hypotheses, canonical maps and import closure at the pinned revision.

For each proposed local construction, record the closest Stacks/Mathlib interface and one of:
exact reuse; reuse after a proved specialization; a genuinely missing lemma on the upstream
object; or an unavailable construction with concrete evidence. Differences in packaging alone
do not justify rebuilding a site or an intersection-theoretic framework. Reuse the existing
upstream site, cycle and intersection objects whenever applicable. Only the verified difference
becomes Colib work, and every downstream lane consumes that chosen object.

The initial pinned survey has located `Stacks.Chow.intersectionProduct` and its bilinear interface in
`Chow/IntersectionProduct.lean`,
`Stacks.Intersection.ChowRing.chowMulFun` and `ChowRing` in
`Intersection/ChowRing/Basic.lean`, and relative-cycle composition interfaces in
`Chow/RelativeCycles/CompositionRelativeCyclesGeneral.lean` and `Composition.lean`.
Bind these candidates to exact declarations and hypotheses before use. In particular, the
Chow-ring construction for nonsingular projective varieties over an algebraically closed field
must not be presented as arbitrary smooth-scheme cycle-level correspondence composition.
The Nisnevich interface has not yet been located by name in the initial survey. That is not
evidence that Stacks lacks an equivalent interface, and does not authorize rebuilding it.

The detailed pinned-interface audit is a prerequisite for implementation in the corresponding
lane. Its findings may eliminate or reorder work below without reducing declaration coverage.

## Mathematical ownership and independent work

Use [ARCHITECTURE.md](ARCHITECTURE.md), [LIBRARY.md](LIBRARY.md) and
[CONTRIBUTING.md](../CONTRIBUTING.md) as the ownership rules. Suggested work lanes are:

1. **Inventory and upstream interfaces.** Own the ledger and dependency graph. Identify the
   Stacks symbol, graded product, quotient and map APIs and provide precise native signatures
   to other lanes. This lane does not build a complete alternate-model comparison.
2. **Generic prerequisites.** Own disjoint files under the appropriate `Colib.Algebra`,
   `Colib.RingTheory`, `Colib.CategoryTheory`, or generic sheaf/module owners. Prove reusable
   statements at their weakest valid hypotheses, below Milnor and motivic applications.
3. **Milnor symbols and operations.** Own new files under `Colib.RingTheory.KTheory.MilnorK`, extending the
   Stacks model with the required tuple-symbol, multilinearity, Steinberg, graded-product,
   functoriality and low-degree results.
4. **Milnor norms and residues.** Start from the accepted canonical symbol/map interfaces.
   Separate field-extension norms, local residue maps, compatibility equations, and complexes
   into disjoint owners. Do not let residue constructions depend on their later applications.
5. **Motivic geometric foundations.** Reuse audited Stacks intersection/cycle interfaces first.
   Own only missing finite-correspondence, cycle and finite-flat geometry
   under their actual `Colib.AlgebraicGeometry` owners, consuming generic length/module facts.
6. **Transfers and cohomological applications.** First locate and audit any applicable upstream
   Nisnevich-site interface, including equivalent presentations under other names. Start after the required geometric, site and
   sheaf interfaces are fixed. Own transfer structures, Nisnevich constructions, invariance,
   and the remaining source endpoints according to the verified dependency graph.

These are dependency lanes, not promises that every named topic is unconditional in the source.
Split a lane further only along verified import boundaries. Each assignment records its exact
mathematical targets, source locators, proof obligations and owned paths. Use separate worktrees
or branches for overlap. Serialize Git index/HEAD operations and integration commits. A single
integrator owns the root imports, shared chapter files, bibliography and ID reservations; workers
submit proposed edits for these shared paths rather than overwriting each other.

Do not create empty source families or chapters in anticipation of future work. Independent
lanes can begin concurrently once their interfaces and ownership are explicit. Routine choices
inside the authorized task do not require a new approval pause.

## Implementation milestones and acceptance

### M0. Close the inventory and establish the native interface

Verify the source and target revisions, clean/owned worktree status, all selected modules and
closure edges. Enumerate declarations and classify missing prerequisites. Inspect Stacks'
canonical APIs and select the smallest first proof chain. Record source-versus-target differences
without assuming that similarly named objects agree.

Acceptance: every selected source module has an owner; the declaration ledger has no unexplained
omissions; initial native interfaces and prerequisite contracts are explicit. The inventory can
still mark proof work pending. A plan/inventory-only commit must not claim theorem completion.

### M1. Migrate canonical symbol foundations

Rewrite the first closed chain directly on `MilnorKTheory`: required symbol constructors and
equations, relations, multiplication/functoriality, and the low-degree endpoints used downstream.
Use existing Stacks results or Colib's degree-two boundary where they fit. If a proof needs a local
presentation comparison, state exactly why and prove its symbol-preservation equation.

Acceptance: the migrated declarations use the canonical model; source hypotheses and signs are
preserved; changed leaves and relevant tests compile; no second general model has been added.
The ledger and Library identify the precise completed chain, not all 186 Milnor modules.

### M2. Close lower prerequisites and geometric foundations

After the pinned upstream audit, migrate only genuinely missing generic algebra/category/site/sheaf
primitives in dependency order. Do not recreate available intersection theory or Nisnevich sites. Reuse the
existing finite-algebra length formula at its RingTheory owner. Rewrite the actual finite
correspondence/cycle/finite-flat constructions and their composition or coefficient equations
against the chosen upstream objects. General lemmas stay below scheme and motivic applications.

Acceptance: each extracted primitive has an actual consumer and no upward import cycle; the
specific geometry equations are proved, not replaced by interfaces that merely assume them.
Independent completed chains may be integrated before the entire milestone is finished.

### M3. Migrate norms, residues and compatibility

Port source norm and residue results onto the canonical groups. Identify the exact extension,
valuation, degree, coefficient and generator conventions at every map. Prove the needed
projection, functoriality, base-change or residue equations only in their source-valid scope.

Treat norm tower independence as a distinct proof obligation. A norm defined using a chosen
tower is not automatically independent of that tower. A theorem assuming compatibility does
not construct it. Record choice-dependent or conditional results accurately until independence
is established by an actual proof.

Acceptance: each claimed map has its construction and defining equations; every independence
or compatibility assertion has proof evidence or remains explicitly unresolved/conditional.
No unrestricted norm API is inferred from a special or supplied-data construction.

### M4. Migrate transfers and motivic consumers

Build the transfer and cohomological chains in the verified dependency order, retaining ordinary
versus derived constructions and the exact Nisnevich, regularity, smoothness or field hypotheses
of the source. Transport only the maps and structures whose required equations are already
proved. Include the remaining Motivic-derived results identified by the ledger, not only the
representative topics named in this plan.

Treat every differential-square-zero assertion as its own proof obligation. A construction
parameterized by a proof of `d² = 0`, or a conditional complex API, is not a proof that the intended
residue maps square to zero. Do not claim Gersten/Rost/related complex completion merely because
a structure with that field compiles. Prove the required reciprocity/cancellation statements at
their actual hypotheses, or retain the source's conditional statement and disclose the gap.

Acceptance: the relevant diagrams, signs and differential equations are established at their
stated scope; consumer statements preserve the source assumptions and use the canonical maps.
Outstanding mathematical obligations remain visible in the ledger and delivery report.

### M5. Reconcile the complete selected surface

Revisit every source declaration and dependency disposition. Verify that no chosen endpoint was
lost in renaming, consolidation, extraction or upstream reuse. Remove unnecessary temporary
adapters, retain only justified local comparisons, and check the final production import graph.

Acceptance: every selected declaration has a checked target or a precise, reported blocker;
there is no Aglib/Motivic/Quillen production dependency and no newly invented axiom. Report partial
completion honestly if any required result is still blocked. A module-count match alone is not
acceptance, and compilation alone is not independent mathematical review.

## Library items, references and source credit

Update source, Library and relevant tests in the same mathematical contribution. Reserve IDs
centrally after checking the current tree. The initial baseline occupies `COL-0001` through
`COL-0012`; this document does not reserve future IDs. Preserve released IDs through renames.

Add `@[colib_tag]` for independently citable public items, ordinary names for helpers, native
`@[stacks]` for applicable Stacks correspondences, and precise `@[colib_ref]` locators for books
and papers. Reuse existing bibliography identities. Inspect and record new references with
their edition/version, relevant clause and actual scope before marking correspondence checked.
Do not present a related theorem as an exact citation for a stronger statement.

Keep implementation credit and license notices distinct from mathematical bibliography. Preserve
original contributors when adapting source. New chapters/sections have introductions and real
compiled items. Record `author_checked` only after the author's actual source comparison;
independent review requires separate evidence and a stated checked span.

## Validation, publication and stopping conditions

For each proof chain, compile changed leaves with their real prerequisites and reuse valid
artifacts. Add focused in-package tests for public interfaces, symbol/map normalization and
important specializations. Generate `Colib.lean` with Mathlib `mk_all`; do not hand-maintain an
incomplete root. Keep the explicit test-module text-lint lists in `scripts/check.sh` and
`.github/workflows/lean-ci.yml` synchronized when adding test modules.

At each meaningful integration milestone run applicable checks through `scripts/check.sh`:
Python tests and metadata validation, production build, in-package tests, declaration lint,
Mathlib text style, generated-root check, the pinned production axiom audit, native Library export
and site generation. Reuse only checks whose inputs remain unchanged after repairs. The permitted
production axiom closure is `propext`, `Classical.choice`, and `Quot.sound`. No placeholders,
new axioms or `native_decide` enter production. Kernel replay and separate client checks are not
part of this task unless explicitly requested.

The active task authorizes milestone pushes after planning and implementation without another
routine confirmation. The implementation integrator, not a read-only/planning worker, owns them.
Before every commit/push, inspect HEAD, status and remote changes; stage only owned paths; preserve
concurrent work; never force-push over it. Keep a milestone coherent and review its diff. Verify
that the intended commit reached `kangxyz/colib` and monitor that exact SHA's CI. Diagnose and fix
authorized recoverable failures before declaring the milestone complete. Record commands,
results, remote SHA and CI links. Do not describe a pushed but failing build as accepted.

The baseline default branch is `main`, with no branch protection or rulesets reported during the
initial survey. Recheck current repository policy before publication. Existing main CI also
publishes caches and the Library after success; do not introduce separate deployment changes as
part of mathematical migration.

Work continues until the selected declaration surface is reconciled and validated, or a concrete
mathematical, tooling or authorization blocker requires input. A blocker report identifies the
exact statement/action, completed work, missing evidence and smallest next step. Source
correspondence, native verification and independent mathematical review remain separate claims
in every milestone and final report.

## First prerequisite milestone (2026-11-05)

The first selected leaf is
`CategoryTheory.ShortComplex.quasiIso_of_liftCycles_of_reflectBoundaries` in
`Colib.Algebra.Homology.ShortComplex.ModuleQuasiIso`. It preserves the fixed Aglib
statement and proof over an arbitrary ring with independent scalar/carrier universes.
It uses Mathlib's canonical kernel/range homology and proves a sufficient criterion:
exact lifting of cycles and reflection of boundaries imply the native quasi-isomorphism.

[The declaration ledger](migration/motivic-short-complex.json) records exact source
hashes, provenance, upstream alternatives, compilation evidence and the independent
read-only mathematical/source review. The original Motivic archive was not re-read
in that review; its provenance was checked against Aglib's manifest. This supporting
primitive has no independent Library ID. Its existing Aglib consumer is the regular
single-Koszul tensor augmentation theorem, not migrated in that first milestone.
The later native coefficient augmentation endpoint is now supplied by COL-0163.

This milestone does not include the concurrently prepared Milnor symbol drafts, a
Koszul construction, or a motivic application. It neither completes M0 nor claims
completion of M1 or M2. Integration validation is recorded separately from the leaf
build and independent review; incomplete checks remain explicit in the ledger.

The isolated milestone passed the complete `scripts/check.sh` acceptance on 2026-11-05,
including production/test builds, lint, generated-root validation, the pinned axiom
audit and Library/site generation. The new leaf also passed a separate module-scoped
axiom audit. Kernel replay and downstream client checks were not run.

## Tuple-symbol milestone (2026-11-05)

The next closed chain supplies ordered homogeneous tuple symbols and seven coordinate
or adjacent-pair identities directly on Stacks' `MilnorKTheory`. Library items
`COL-0013` and `COL-0014` record the construction and identities. The declaration ledger
is [milnor-symbols.json](migration/milnor-symbols.json). It covers eight source
endpoints plus one target-only coercion lemma; it does not complete either source
module or assert a comparison with the old all-degree quotient.

The official Stacks Tag 0EAY, first paragraph, was inspected directly. It supplies
the tensor-algebra Steinberg quotient. Coordinate identities and adjacent Steinberg
vanishing follow from this presentation; adjacent skew is a derived result proved
using the pinned Stacks list theorem, not a verbatim statement of the remark. No new
Milnor1970 correspondence claim is made without inspecting that paper for this chain.
The old presentation machinery is not retained or counted as three equivalent target
objects. Universal properties and the other omitted source results remain unresolved.

The isolated tuple-symbol milestone passed the complete `scripts/check.sh` on
2026-11-05: all four in-package test modules, lint and generated-root checks,
91-declaration production axiom audit, and 14-item Library/site generation.
Kernel replay and separate downstream client checks were not run.

## Koszul quotient Ext milestone (2026-11-05)

Library item `COL-0021` records the projective-dimension bound and higher Ext
vanishing for quotients by finite weakly regular sequences. The implementation
uses Stacks' existing exterior-power Koszul resolution and augmentation; it does
not recreate or compare the source recursive tensor model. The native quotient,
coefficients and supported Ext universe agree with the source endpoints.

The source helper for vanishing at a zero term of a supplied projective resolution
is extracted at its categorical owner. The separate generic dimension helper is
still an unresolved upstream-reuse candidate, not counted as migrated. See
[motivic-koszul-ext.json](migration/motivic-koszul-ext.json) for exact dispositions.

Official Stacks Tags 062F and 0CXC were inspected and recorded only as ingredients:
weak regularity gives Koszul acyclicity, and finite projective resolutions give
dimension bounds. Neither tag is labeled as a verbatim statement of the combined
Ext endpoint. Tests include the empty sequence, arbitrary supported Ext universe,
the native finite-indexed quotient, and the singleton unit generating the improper
ideal. No nontrivial-ring, proper-ideal or Noetherian assumption is introduced.

After the remote Quillen contribution advanced main, this milestone was reapplied
without overwriting it on `bee0a67c18e023f641c64e701e833f1f6b7b3937`. The previously
unpublished Koszul item was allocated `COL-0021`, preserving remote IDs 0015-0020.
The full guarded check passed with all six test modules, the 217-declaration axiom
audit, and the 21-item Library/site. Dependency pins and resource limits were
unchanged; kernel replay and separate downstream client checks were not run.

## Native graded-product milestone (2026-11-05)

Library item `COL-0022` records three formulas: ordered tuple concatenation under
native graded multiplication, and left/right action of a degree-zero class by its
canonical integer value. Both degree-zero formulas explicitly transport from
`0+n` or `n+0` to `n`. The product and degree-zero equivalence are existing native
objects, not reconstructed operations. Stacks 0EAY is cited only for the underlying
tensor-algebra quotient and canonical degree-zero identification, whose consequences
are proved here. The [product ledger](migration/milnor-product.json) retains the
remaining source declarations as unresolved; this is not a complete Product-module
migration or an old-model equivalence. Tests cover empty/nonempty tuples and
negative integer scalar action with the actual degree transports.

On baseline `bb11e3ad22069f6cf78b1ff37919cb239dcb4e94`, the independent product
worktree passed the complete guarded `scripts/check.sh`, including all seven
in-package test modules, the 222-declaration axiom audit, and the 22-item Library/site.
Resource limits and dependency pins were unchanged; no kernel replay or separate
client checks were run.

## Homogeneous symbol extensionality milestone (2026-11-05)

Library item `COL-0030` closes the two source extensionality declarations for
additive and integer-linear maps on the native homogeneous Milnor groups. Source
and target universes remain independent, and degree zero is included. The proof
uses the native graded projection and existing all-list generation; it does not
import the higher residue-family fixed-length generation theorem or build a new
presentation. The [extensionality ledger](migration/milnor-ext.json) reconciles
the two earlier unresolved entries in the symbol ledger. Universal descent and
existence of lifts remain unresolved. Stacks 0EAY supplies the underlying tensor
quotient construction; extensionality is a derived consequence.

## Koszul coefficient milestone (2026-11-05)

Library item `COL-0031` records finite terms, Noetherian homology and the term/homology
coefficient-annihilator inclusions for the native Stacks coefficient complex. The
[ledger](migration/motivic-koszul-coefficients.json) records four direct canonical-object
rewrites and one upstream exterior-power instance reuse, without an old-model comparison.
Tests cover both stronger Noetherianity and term annihilation, including the empty sequence.
Stacks 0622/0623 are definition ingredients; 00IK is the Noetherian submodule ingredient.
They are not presented as verbatim coefficient theorems.

Both milestones are isolated on baseline `9dbeca3fac888032a93ed3580cb078c1021e1ddd`,
preserving all remote Serre localization files, tests and catalog fixtures. The unpublished
conflicting Ext allocation is replaced by `COL-0030`. Dependency pins and guard limits
remain unchanged. Kernel replay and separate downstream client checks are not run.

The complete guarded check passed for both milestones: 27 Python tests, all twelve
Lean test modules, declaration/text lint, the generated-entry check, the 335-declaration
production axiom audit, and the 31-item Library/site. The guard recorded no failure
and confirmed that the owned process group exited.

## Principal regular quotient Ext milestone (2026-11-05)

Library item `COL-0041` specializes the existing native Koszul dimension bound to
one ring-regular scalar, and combines it with coefficient-regular degree-zero
vanishing. The quotient is exactly `R / Ideal.span {a}`. The generic degree-zero
criterion is kept at its Ext owner and permits independent module and Ext universes.
The principal endpoints retain same-universe coefficients and arbitrary supported
Ext universe; the dimension bound needs no HasExt. Tests include the unit scalar.

The [ledger](migration/motivic-principal-ext.json) distinguishes four original
principal-ideal endpoints from the generalized supporting criterion. No degree-one
equivalence, nonvanishing, source scalar-quotient model or cocycle normalization is
claimed. Stacks 062F and 0CXC are ingredients only. No kernel replay is run.

## Universal homogeneous symbol descent (2026-11-05)

Library item `COL-0042` closes five source symbol-map and universal-lift endpoints
on the native homogeneous Milnor groups, in every nonnegative degree and independent
source/target universes. Generic homogeneous tensor extension and two-sided ideal
annihilation helpers stay at their linear-algebra owner. The proof kills arbitrary
left/right tensor multiples of Steinberg generators and then their additive closure,
not merely the listed generators. Tests include degree zero and recovery of the
identity from native symbols. Stacks 0EAY is construction background only.

The [descent ledger](migration/milnor-descent.json) updates the earlier symbol and
extensionality ledgers. Other source obligations remain scoped separately; this is
not a blanket completion of the entire Basic module or an old-model equivalence.

The combined isolated integration on `36f7d6169afeec2f0537896dd8f56b68bda27ba9`
passed complete guarded `scripts/check.sh`: 31 Python tests, eighteen Lean test
modules, declaration/text lint, generated-entry check, 510-declaration production
axiom audit and the 42-item Library/site. Remote Q-category contributions were
preserved. Pins and resource limits were unchanged; no kernel replay was run.

## Consolidated completed Milnor and Koszul migration (2026-11-05)

The isolated consolidation starts from main 6993f8b and retains all of its work.
The exact source branches, completed unpublished work, selected files and reassigned
permanent IDs are recorded in migration/milnor-motivic-consolidation.json. Reused
branch IDs are never treated as identities: mathematical item titles and compiled
bindings determine the fresh consolidated IDs. Each canonical leaf is selected once.
The four-universe specified e=1 residue proof is maintained once, with the original
common-universe APIs as wrappers. Top Ext determinant and positive-length ring
quotient results are complete in the native model. Old Aglib named-class/model
comparison, canonical arbitrary-uniformizer naturality, ramification e != 1 and
general coefficient top quotient equivalence remain distinct unfinished obligations.
No publication or branch deletion is performed by this integration task.

The complete unified guarded check passed: 52 Python tests,
68 Lean test modules, build/lint/style, generated-entry check,
1606-declaration axiom audit and 133-item Library/site with 398 indexed declarations.
The exact receipt hashes, source revisions, compiled declaration inventory and source/olean
hashes are recorded in the consolidation manifest and individual ledgers.
No kernel replay or publication was performed by the integration worker.

### Arbitrary-coefficient native top Ext

COL-0134 identifies N/IN with positive-length top Ext, linearly over R/I and
naturally in every coefficient module N, using the existing native top cocycle.
The quotient-source action belongs to Colib and uses Mathlib's annihilated-module
construction. No coefficient regularity or finiteness is required. The empty
sequence endpoint was later completed by COL-0137. Comparison with old named
Aglib classes remains pending. See
`migration/motivic-top-ext-coefficients.json` for the precise evidence.

### Module quasi-isomorphism criterion

The lower module criterion now characterizes quasi-isomorphisms by reflecting
boundaries and lifting cycles modulo boundaries, for noncommutative rings and
independent module universes. The old exact-lifting API is a short corollary of
this single proof. Equivalent private higher-level Stacks helpers are recorded
in `migration/motivic-short-complex-criterion.json`; no new mathematics or
additional source-model comparison is claimed.

### Explicit coefficient-field retractions

COL-0135 gives the coefficient-field specialization square in every degree.
Split injectivity additionally requires actual residue-field retraction data
with its composition equation. This is a native consequence, not a new norm
model or a claim that arbitrary DVRs admit coefficient fields or sections.
See `migration/milnor-coefficient-retraction.json`.

### Coefficient regularity on native Koszul terms

COL-0136 reuses flat-tensor preservation to retain scalar and weak-sequence
regularity on every term, with independently sized coefficients. Only the scalar
endpoint rewrites a source declaration; weak-sequence and scalar short-exact
statements are native consequences. This does not assert homology regularity,
properness, or equivalence with the old recursive model. See
`migration/motivic-koszul-coefficient-regularity.json`.

### Top Ext coefficient quotients in all lengths

COL-0137 closes the empty-sequence quotient endpoint using the degree-zero
projective-resolution cocycle criterion. Positive lengths reuse the existing
quotient equivalence definitionally. This supplies quotient endpoints and
representatives, not all-length naturality or old named Aglib class comparison.
The generic reduction retains Joël Riou's Mathlib attribution. See
`migration/motivic-top-ext-all-lengths.json`.

### All-length top Ext naturality and scalars

COL-0138 adds the actual coefficient mapQ/Yoneda square in every length,
including zero. Quotient scalars use source multiplication and ring representatives
also use coefficient scalar postcomposition. Existing native positive-length
naturality and quotient actions are reused; no old named Aglib class comparison
is claimed. See `migration/motivic-top-ext-all-naturality.json`.

### Degree-one residue and ramification

COL-0139 identifies native degree-one residue with integer order and its kernel
with actual DVR units. COL-0140 proves order scaling from j(pi)=u*rho^e and its
degree-one residue consequence in four independent universes. Exponent zero
is permitted in the conditional nonlocal statement; locality forces positivity.
This does not close all-degree ramification or canonical arbitrary-uniformizer
comparison. See the two degree-one migration ledgers.

### The native exact coefficient functor

COL-0141 packages seqComplexTensor itself as an additive coefficient functor,
with every coefficient map acting by the identity on the exterior factor.
It preserves actual short exact sequences without regularity or coefficient
flatness hypotheses, retaining independent ring and coefficient universes.
This is a new lower interface, not another source endpoint or recursive model.
See `migration/motivic-koszul-coefficient-functor.json`.

### Fixed-base top Ext coefficient localization

COL-0142 identifies Yoneda postcomposition by coefficient localization as an
actual localized-module map on native top Ext, in all finite lengths. The ring
and quotient source remain fixed; this is not base-ring localization or an old
named-class comparison. A lower ideal-quotient helper retains independent
module universes. See `migration/motivic-top-ext-localization.json`.

### All-degree ramification with specified uniformizers

COL-0143 closes the general-e specified-uniformizer actual local DVR residue
comparison in four universes. Its main component keeps the unit correction,
including negative integer orders, and its shift algebra uses native two-torsion
without inverting two. Canonical chosen-uniformizer comparison is supplied by COL-0150 below.
See `migration/milnor-ramified-map.json`.

### Canonical all-degree ramification

COL-0150 closes the canonical-uniformizer obligation of COL-0143. Uniformizer
independence follows from the already proved general-e identity-map case; the
bridge has the existing native conclusion without copying the high-import
Invariance twist proof. Four universes and the actual local-map, fraction-map
and ramification equation hypotheses remain explicit. See
`migration/milnor-canonical-ramified-map.json`.

### Native DVR residue and specialization milestone

COL-0150–COL-0152 complete one native functional chain: canonical all-degree
ramified residue, specialization with the literal right-plus unit correction,
uniformizer independence of specialization on the canonical residue kernel,
and canonical unit-prefix/repeated-uniformizer normalizations. Existing source
modules are reused rather than copied into a second model. Tests include four
independent universes, the empty prefix, repeated signs, and the residue kernel.
See `migration/milnor-dvr-normalization.json` for source and review evidence.

This earlier milestone did not assert completion or norm compatibility. The
completion obligation is discharged by COL-0168 below.
Norm/transfer still needs the native transfer construction and its residue
comparison with the exact finite-extension hypotheses. These are separate
mathematical obligations, not consequences of the ramified restriction square.

### Coefficient augmentation and native top Ext base change

COL-0163 identifies coefficient H0 with the actual ideal quotient and proves
the original augmentation is a quasi-isomorphism under coefficient Koszul
regularity. Ring and coefficient universes remain independent; ULift only
places the categorical quotient in the tensor-complex universe.

COL-0164–COL-0167 complete the native scalar-extension chain: exact-functor
compatibility of actual projective-resolution Ext cocycles, localization of
top Ext, the actual isomorphism F(R/I) to A/IA, and equality with the native
target-ring top cocycle of 1 tensor m. Flatness supplies target regularity and
exactness. All lengths, including zero, and independent source/target Ext
universes are retained. See migration/motivic-koszul-native-base-change-milestone.json.

This does not prove comparison with old named recursive Aglib classes,
geometric purity or norm/transfer compatibility. Component review, focused
compilation and final registered-tree aggregate validation are separate facts.

### Actual DVR completion compatibility

COL-0168 completes the native completion chain from the existing Stacks 0AP1
completion input to Mathlib's literal fraction lift, its uniqueness triangle,
the canonical all-degree residue square, the inverse actual residue-field
identification and preservation/reflection of residue vanishing. Arbitrary
classes and degree zero are tested. No second completion, valuation or Milnor
model is introduced, and no full Milnor-group injectivity, norm, transfer or
tensor decomposition is asserted. See migration/milnor-completion.json for
source provenance, component review and aggregate validation evidence.

### Principal Euler length and local associativity

COL-0169--COL-0173 migrate the complete five-leaf Principal Euler chain using
native periodic complexes, support, prime RelSeries and LocalizedModule.
Outer finiteness implies exact-sequence additivity; support containment gives
finite scalar homology of actual subquotients. A single prime filtration
controls both the Euler sum and localized multiplicities. The final local
associativity formula includes dimension zero, where the closed-point Euler
contribution is zero, and specializes to cokernel length for a regular scalar.
No second scalar-homology or prime-filtration model is introduced.
See migration/principal-euler.md and migration/motivic-principal-euler.json
for exact hypotheses, source correspondence and validation boundaries.

### Local-base finite-algebra length formula

COL-0180--COL-0181 complete the closed-fibre and local-base length chain.
For a module-finite algebra over a local ring, finite algebra-length implies
finite base-length, computed as localized lengths times residue degrees.
The proof uses the native semilocal decomposition and actual LocalizedModule
objects; the tensor presentation is transported through their existing equivalence.
No Noetherian or local-algebra hypothesis is added. This is the finite-algebra
specialization of Stacks 02M0, not the whole general semilocal statement.
See migration/motivic-finite-algebra-length.json for source and validation evidence.

### Finite-algebra and polynomial-fibre norms

COL-0182--COL-0184 complete the native determinant comparison, length-weighted
finite-algebra norm decomposition and polynomial evaluation-fibre unit norm
compatibility. Localized module lengths and actual quotient residue fields
are retained, including nonreduced and inseparable cases. Equality between
two fibres requires a global unit and finite freeness, or finite torsion-freeness
over the polynomial PID. The single-fibre product only requires finiteness.
No new fibre, norm or prime-filtration model is introduced. This remains an
algebraic norm statement, not a Milnor transfer or geometric cycle comparison.
See migration/motivic-finite-algebra-norm.json for source and validation evidence.

### Actual completion CRT and completed local branches

COL-0185--COL-0189 complete the finite-algebra completion comparison, canonical
CRT/positive-power/localization maps, explicit semilocal factorization and
Dedekind branch decomposition. Quotient evaluations identify the actual maps;
the completed-base scalar action precedes the tensor equivalence. Branches
are finite over the completed base. No second completion or inverse-limit
model is introduced. Arbitrary-module scalar extension, general monotone
reindexing, fraction-field decomposition and Milnor norms are not claimed.
See migration/motivic-completion-branches.json for hypotheses, provenance and
component versus registered-tree validation.

### Completed fraction branches and DVR residue norms

COL-0190--COL-0194 complete the native fraction-product and local residue-norm
chains. The completed fraction tensor product is identified with all actual
completed original branches, including integral, fraction and original-field
coordinate maps. Original residue fields and completed branch fraction fields
are finite where stated; the original localizations are not claimed finite.
The literal closed-fibre norm formula retains its full length, and an explicit
uniformizer equation proves that length equals the DVR exponent before the
actual integral and residue-unit norm formulas are deduced. There is no
separability, completeness or characteristic-zero restriction. This milestone
does not claim a Milnor norm, transfer or norm-residue-symbol comparison.
See migration/motivic-fraction-residue.json for provenance, precise scope and
component versus registered-tree validation.

### Henselian uniformizers and exact prime-degree norm coefficients

COL-0195--COL-0199 complete the principal-unit Hensel root, actual uniformizer
normalization, native DVR degree formula and exact norm-coefficient chain.
The fundamental identity proves the actual field degree equals the supplied
uniformizer exponent times residue degree, without perfectness or a norm-order
model. Eisenstein binomials determine the exact determinant sign; residue-one
adjustment and the existing unit-norm formula recover the original uniformizer
coefficient. The prime-degree theorem keeps its henselian target, invertible
exponent, actual integral-closure and compatible finite-dimensional field data.
The exponent-one case needs neither henselianity nor primality. No ordinary
norm-order, Milnor transfer or norm-residue-symbol theorem is claimed.
See migration/motivic-uniformizer-norm.json for precise scope and provenance.

### Native ordinary DVR norm orders

COL-0200--COL-0201 close the ordinary field-norm order endpoint omitted by the
preceding exact-coefficient milestone. The existing native fraction order is
identified with the literal negative logarithm of the maximal-ideal valuation.
Ordinary norms multiply it by the actual residue degree, for arbitrary field
units and explicit nonzero elements, including all negative orders. The proof
uses actual integral unit norms, the acyclic native e*f formula and cancellation
of a nonzero integer exponent. It needs no perfectness, separability, Hensel
lifting, prime degree or invertibility of the exponent. The finite torsion-free
DVR extension, actual compatible fraction fields and finite-dimensional field
data remain explicit. No second order model is introduced; the old relative
ideal-norm helper and Milnor transfer are not claimed.
See migration/motivic-dvr-norm-order.json for exact scope and source comparison.

### Actual characteristic polynomials and exact residue-branch counts

COL-0202--COL-0207 complete the actual multiplication characteristic-polynomial,
DVR residue, integral tensor-product and exact residue-branch multiplicity chain.
The integral product formula is derived from the supplied generic tensor algebra
equivalence and compatible integral elements, not accepted as a new hypothesis.
The general residue exponent retains the degree over the simple residue
intermediate field; reducing it to the ramification exponent requires the
specified residue power basis and generator equality. The final count retains
characteristic-zero residue, all original scalar towers and integral closures,
and the actual uniformizer equations. Literal monic irreducible polynomials
replace only the old nested branch wrapper. No additional multiplication, norm,
branch or order model is introduced. This is an algebraic branch-count theorem,
not a Milnor norm-residue or transfer theorem.
See migration/motivic-charpoly-branches.json for source comparison and checks.

### Finite Sylow fixed fields and original-branch degree reduction

COL-0208--COL-0211 complete the native finite Sylow fixed-field, literal
AdjoinRoot branch-embedding and normal prime-subfield chain. All fields,
subgroups, quotient algebras and maps are existing Mathlib objects. No adapter
layer, branch wrapper or alternate field model is introduced. The subgroup
interpolation and Galois correspondence are used directly, and native
restriction and range equivalences return the subfield inside the original
field. The remaining degree strictly decreases.
The supplied finite splitting family is retained, including zero and constant
polynomials. Relative Galoisness above the finite fixed field is native;
ambient Galoisness over the original base is needed for base-degree
coprimality, not for the original-branch normal-subfield consumer. This is a
finite field-theoretic reduction, not an infinite special-field construction
or a Milnor norm, reciprocity or transfer theorem.
See migration/motivic-sylow-branches.json for source comparison and checks.

### Prime Galois Milnor norm-residue compatibility

COL-0289 closes the actual chosen-norm/canonical-DVR-residue square for a finite
torsion-free local DVR extension whose fraction-field extension is Galois of prime
degree and whose actual base residue field has characteristic zero. The rings and fraction
fields share one universe. Every natural degree, including the degree-one to
residue-degree-zero case, is covered by both pointwise and additive-hom equality.

The proof uses one actual finite coprime coefficient field for each class, its
native tensor coordinates and every completed normalization branch. Residue norms
retract the ramification-weighted branch errors; the original-base weight sum
supplies the second annihilator. Together with the broader prime annihilation
result COL-0261, native integer gcd cancellation gives equality. No Henselianity
of the original rings, supplied auxiliary square or mixed witness, separate
integer cancellation, or torsion-freeness of a Milnor group is assumed.

This complete chain comprises 17 production modules and seven consumer modules
with 30 examples. The field-specific sources use the native
`Colib.RingTheory.KTheory.MilnorK` owner. Positive or mixed residue characteristic,
arbitrary finite generic degree, independent endpoint universes and a general
chosen-norm tower/independence theorem remain outside this milestone. Precise
source correspondence, final-byte compilation and project-check scope are
recorded in `migration/milnor-prime-galois-dvr-norm-residue.json`.
