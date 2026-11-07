# Native finite-module G-localization

This slice migrates the actual-target and small-model connective Serre
localization arguments and applies them to finite modules over a commutative
Noetherian ring at any multiplicative set. It uses Mathlib and the pinned Stacks
repository, with no Aglib dependency or additional category model.

## Actual maps and exactness

`Colib/KTheory/Quillen/Localization/Serre/Target.lean` constructs the native
localization lift to the specified target. It proves the lift is an exact
categorical equivalence and identifies its forward K-map by strict factorization.
The target boundary is the existing path-space boundary composed with the inverse
of that proved equivalence.

`Colib/KTheory/Quillen/Localization/SmallModel.lean` passes this sequence through
Mathlib's actual chosen small model. The transported and standard abelian exact
structures agree; their comparison functor is the identity. The ambient-to-target
map remains precisely the original `ExactFunctor.smallKMap`. These statements
form COL-0272. Source and target object/hom universes are independent, with a
common chosen smallness universe.

`Colib/Algebra/Category/FGModuleCat/Localization.lean` proves the categorical
localization for the literal restriction of `ModuleCat.localizedModuleFunctor S`
to `FGModuleCat`. Its proof generalizes the native denominator-clearing and Serre
quotient argument of Stacks `FGModulesModuloTorsion.lean`, Tag 0B0L. The separate
`Localization/EssSurj.lean` descends every finite localized module to the actual
finite base-ring submodule spanned by a generating family. This replaces only
the field-basis argument used in the native fraction-field specialization.

`Colib/KTheory/GTheory/FiniteModules/Localization.lean` gives COL-0273. For
`R : Type u` and module universe `v`, the groups use native `FGModuleCat.{v}` and
`SmallModel.{u}`. The ordinary hypothesis `Small.{v,u} R` permits the native
localized-module construction; it is automatic when `v = u`. All three recurring
range/kernel equalities hold, including supported degree zero, and the terminal
surjection is on the original homotopical G-zero.

The boundary retains the prescribed path orientation and degree shift. This
transport neither flips its sign nor introduces a new boundary chosen only to
make the sequence exact. Weibel, *The K-book*, V.5.1 supplies the localization
reference; no independent comparison of alternate boundary conventions is made.

## Supported objects and fraction-field specialization

The support condition means elementwise annihilation by members of `S`.
`Colib/Algebra/Module/LocalizedModule/FiniteTorsion.lean` proves that finite
generation makes this equivalent to one member of `S` annihilating the whole
module. For `S = Submonoid.powers r`, it is exactly annihilation by one uniform
natural power of `r`. Exponent zero, zero in `S`, zero divisors and the zero ring
are all admitted. Essential surjectivity and the uniform-annihilator argument
require no Noetherian hypothesis.

The previously constructed fraction-field specialization is retained in
`Colib/Algebra/Category/FGModuleCat/FractionLocalization.lean` and
`Colib/KTheory/GTheory/FiniteModules/FractionLocalization.lean`. At the
nonzerodivisors of a domain the general functor and torsion property are
literally the original Stacks constructions, and the G-map is definitionally
the existing fraction-field G-map. No replacement map or comparison model is
introduced.

## Pinned source crosswalk

At Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`:

- `Localization/Serre/LocalizationTarget.lean`: actual target lift and boundary.
- `Localization/SmallModel.lean`: canonical abelian exact-structure comparison.
- `GTheory/SmallModelLocalization.lean`: original small-model map and sequence.
- `GTheory/FiniteModules/LocalizationSequence.lean`, lines 37–120: the four
  connective clauses of finite-module localization.
- `Aglib/Algebra/Category/FGModuleCat/SmallModelLocalization.lean`, lines 104–139:
  represented torsion and principal-power support comparisons.

The finite-submodule descent argument follows
`StacksFrontier/RingTheory/Flat/FlatLocalExtension.lean`, lines 88–104, at Stacks
commit `f8e70c5dd04bfabcb423d5e325461f527c85a5d6`. Its proof is placed inside the
actual essential-surjectivity proof to avoid importing unrelated flat dévissage.

## Scope and validation

The Serre/G-theory theorem assumes a commutative Noetherian base ring. It is
connective: degrees are natural numbers. The supported term is K-theory of the
actual torsion Serre category. No additional identification with G-theory of
`R/(r)`, general scheme-open localization, negative G-theory, or scheme K/G
equivalence is claimed.

The regression examples check literal functor and map identities, all
lowest-degree exactness positions, principal powers including zero, and the
equal-universe specialization. Independent mathematical review covers the
actual maps and boundary, categorical localization, finite-module support,
universe assumptions and pinned-source correspondence. The current native
validation scope is recorded in the [batch overview](README.md#validation-scope).
The bounded-resolution bridge retains its separate mathematical source and
review scope within that same integration batch.

The separate [principal closed/open theorem](principal-closed-localization.md)
now supplies the quotient-ring identification by actual image-filtration
dévissage. The arbitrary-set result above retains its own precise source scope.
