# Original stable K-groups and the connective spectrum fibration

COL-0283 identifies every nonnegative stable homotopy group of the actual
Waldhausen S-spectrum with the original K-group. It includes K-zero and its
group law. The comparison is natural for the unchanged exact-functor KMap,
including arbitrary exact functors through canonical zero rebasing. The
spectrum map is a stable equivalence exactly when every original KMap is
bijective. All negative stable groups vanish by a proof using actual stage
connectivity. No negative-degree vanishing is assumed.

COL-0284 proves that the original canonical acyclic-to-homotopy-fiber
prespectrum map is a stable equivalence in every integer degree. Its
structural hypotheses are precisely coarse two-out-of-three, the coarse
extension axiom, genuine joint cylinder data, and its separate
second-endpoint section. The last input is not inferred from joint data.
No stable-equivalence, connectivity or K-zero-surjectivity premise is added.
The negative-one case derives actual K-zero surjectivity from the original
change-of-weak sequence; lower degrees use proved connectivity.

## Actual groups, maps and signs

The generic stable groups are Mathlib colimits of sequential diagrams in
`AddCommGrpCat`. The stage for integer degree `d` and natural index `n` is
`Pi_(d.toNat + n + 2)(E_((-d).toNat + n + 2))`. Its transition uses the
existing prespectrum structure map followed by the inverse loop-degree
shift. Sign correction and final tails act on these actual diagrams;
there is no alternative spectrum or sequential-system model.

The generic homotopy-fiber prespectrum uses the full path-space fiber and
keeps structure time, fiber-path time and nullhomotopy time independent.
Its stable long exact sequence is proved for all integer degrees without
an Omega-spectrum hypothesis. Strict-square and specified-nullhomotopy
naturality retain the actual maps. The connective Waldhausen application
uses the already proved actual Omega structure, not an additional premise.

The level-one comparison agrees with the original canonical fiber map on
the whole original acyclic nullhomotopy. Under the original K-group
comparison, the stable boundary equals minus the image of the original
change-of-weak K-boundary. The explicit natural-to-integer degree cast and
single minus sign remain in the statement, including K-one to K-zero.
This sign records the retained loop and path conventions; it is not
attributed as a literal sign formula in the cited articles.

Original object and morphism universes remain independent. Exact functors
retain the original common universe pair for source and target. General
topological spectra and colimits remain below general categorical
K-theory; no ring or scheme-specific construction is added here.

## Source and literature correspondence

The implementation adapts Quillen revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving original authorship
and license notices. The six `Quillen/Topology/Prespectrum/Stable*` files
and ten generic fiber files retain the original integer indexing,
transitions and complete continuous families. Four sequential-colimit
support modules use native Mathlib diagrams and colimits. Their Aglib
source provenance is retained where applicable, but production imports
only native Colib and Mathlib modules and has no Aglib dependency.

The five `Quillen/Waldhausen/SConstruction/Iterated/` sources
`ExactCoherence`, `ZeroMap`, `HomotopyTransport`, `StableHomotopy` and
`StableFunctoriality`, together with the four fibration sources
`Prespectrum`, `SpectrumComparison`, `LevelOneConnectingComparison` and
`StableConnectingComparison`, supply the original Waldhausen maps and
all 53 declarations of this application. Native small-category and
homotopy-group APIs replace their former owners without changing the
mathematical constructions or strengthening the assumptions.

Waldhausen, Section 1.6, Theorem 1.6.4 and its proof, pages 350-352,
supplies the fibration theorem. The formal adaptation records its precise
structural inputs instead of assuming a comparison conclusion.
Thomason--Trobaugh, Sections 1.8.1-1.8.2, page 263, supplies the spectrum
fiber-sequence background and the chosen zero nullhomotopy. Sections
1.5.3-1.5.4, pages 260-261, supply the spectrum/K-group comparison
background. The printed negative-degree clause in Section 1.5.3 is
`n < -1`; vanishing in every negative degree here is an additional proved
connectivity consequence, not a quotation of that clause.

This milestone does not construct Bass nonconnective K-theory, cone
excision or spectrum localization. Those require their own hypotheses,
canonical maps and proofs.

## Verification boundary

All 29 new production modules and both regression files passed strict
Lean 4.35 compilation in their source components. The Waldhausen test has
24 examples covering original maps, K-zero, integer degrees, whole null
tracks, universes and the signed lowest boundary. Its 53 new declarations
passed the transitive axiom audit using only `propext`, `Classical.choice`
and `Quot.sound`.

The integrated result was published as commit
`21081f04555a2bd9d5e52f4ad332de81730d1b5e` and advanced to main after its
[exact original whole-library CI](https://github.com/kangxyz/colib/actions/runs/42397700139)
passed production build, tests, native declaration/text lint, transitive axiom
audit and Library export. Its local focused integration checks also passed
all compiled bindings, applicable source consumers, native lint and the
11,424-declaration transitive audit with only the three permitted axioms.

That exact CI result does not certify a later integration tree. No local
whole-library pass, kernel replay or separate downstream-client check is
inferred. The separate [cone-excision milestone](waldhausen-cone-excision.md)
extends the scope using genuine finite excision and point HEP. Detailed
internal verification records remain outside the repository.
