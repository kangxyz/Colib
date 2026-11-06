# Native polynomial norm scalar-factor base change

## Result and verification boundary

This is an **uncompiled source draft**, not an established base-change theorem. The independent
branch is `work/native-simple-norm-base-change`, based on
`8a90269409024c63ca7c5203fc8faea01915de0c`, in `milnor-simple-base-change-8a90269`.

Seven production leaves contain twenty public theorem bodies and one private helper, with no
placeholder declarations. Six test leaves contain twenty-eight source consumers. No Lean/Lake
command, build, native lint, axiom audit, guard acquisition, main edit, pin change, shared cache
write, or push was performed.
The new sources require actual elaboration; static inspection does not establish compilation.

The unconditional mathematical supporting arguments now written in source are:

1. Contraction of a nonunit polynomial factor of a coefficient image of an irreducible.
2. Finite reciprocity for the existing `simpleMilnorNorm`, with a supplied complete finite
   residue support. The existing Stacks finite-support existence theorem supplies such supports.
3. Actual rational/local coefficient squares and the polynomial-quotient/residue-field dictionary.
4. A local unit-times-uniformizer equation with the native factor multiplicity, including its
   identification with the count in the actual normalized-factor multiset.

A separate leaf contains two **conditional single-lift reductions**. They retain every missing
comparison premise explicitly. They are not a construction of scalar base change, norm
presentation independence, field-norm compatibility, or a norm tower law.

## Native objects and ownership

No definitions, norm structures, field wrappers, or alternate Milnor groups are introduced.
The files use `MilnorKRing`, `MonicIrreducibleOfDegree`, `monicIrreducibleResidue`,
`infinityResidueRing`, `simpleMilnorNorm`, `IsSingleResidueLift`, `milnorKRingMap`, and the literal
`AdjoinRoot.map`. The polynomial quotient is definitionally Mathlib's `AdjoinRoot`; no quotient
comparison wrapper is inserted.

The first Milnor leaf imports only native `SimpleNorm`. It does not add imports of `FieldNorm`
or the higher `MilnorExactSequence` assembly. Its proof uses the lower exactness result already
in the SimpleNorm dependency closure. The existing geometric dependency of native infinity
residue is not changed or reconstructed.

The parent integrator owns Library IDs, registration, source-reference entries, root imports,
and release acceptance. Supporting names are ordinary native-namespace declarations.

## Consolidation of the finite-reciprocity drafts

The canonical implementation is this branch's
`Colib/KTheory/MilnorK/Norm/FiniteReciprocity.lean`. It retains one generic finite-family
lift/exactness proof. The prescribed-residue version and the two added sigma-index corollaries
all consume it. The same source continues to expose the all-zero finite-residue consequence.
There is no second total norm, point type, field model, or independent reciprocity proof.

Compared with source commit `e9f2574f11c589e8a92a9ecda0fbfc87eaa5e843`, consolidation adds:

- `sum_simpleMilnorNorm_residue_add_infinity_eq_zero`: specialize the generic theorem to the
  literal sigma of native degree-indexed irreducibles, then rewrite `sum = -infinity`.
- `exists_finset_sum_simpleMilnorNorm_residue_add_infinity_eq_zero`: pull back the native finite
  polynomial support along the injective polynomial projection, then apply the sigma corollary.
- One private sigma extensionality helper, obtained from equality of polynomial degrees followed
  by the native same-degree `poly_injective`.

The sigma statements avoid the larger `MilnorExactSequence` import. Their finite support may
include extra zero-residue points. No characteristic, separability, perfection, finite-field,
or homogeneous-class assumption is added. The generic index still has an independent universe.
The polynomial injectivity condition in the generic API is essential: repeated indices must not
count the same residue twice. Factor multiplicities belong in explicit weights on distinct factors.

`ScalarFactorReduction.lean` and its tests are unchanged. They continue to consume the generic
prescribed-residue interface, which avoids reindexing actual factors through a sigma type. The
conditional finite-place, support, and infinity premises are not discharged by consolidation.

`ColibTest/MilnorFiniteReciprocity.lean` retains its five consumers and adds the six earlier
degree/sign tests plus one finite-support existence consumer, for twelve examples in that leaf:

1. Native norm of `1` includes the polynomial degree exactly once.
2. The polynomial symbol has negative-degree infinity residue.
3. Native simple norm preserves grading.
4. The sigma corollary applies to empty support.
5. The polynomial symbol has singleton support and satisfies the new sigma corollary.
6. A constant on the right introduces the native residue involution sign.
7. A whole-ring, possibly nonhomogeneous class has a finite support satisfying reciprocity.

The first five pre-existing consumers still cover a varying-degree family in an independent
index universe, all-zero finite residues, a general singleton lift, the zero class, and a
homogeneous source class. Tests for actual scalar base change remain outstanding.

### Static API review and validation handoff

The independent read-only comparison included the historical source drafts
`norm-finite-reciprocity-20261105T1451/FiniteReciprocity.lean`, `FiniteReciprocityTest.lean`, and
`finite-reciprocity-static-review-20261105T2240.md`. Their hashes are recorded in the source
receipt. They remain unchanged historical records, not alternate production targets.

The pinned source checks confirm the following, without establishing elaboration:

- Mathlib `Algebra/BigOperators/Group/Finset/Defs.lean:181` declares `sum` notation with ordinary
  `syntax`, not scoped syntax. An extra `open scoped BigOperators` is unnecessary.
- Native `PolyResidueRing.lean:215-218` transports zero residue in the direction used by
  `monicIrreducibleResidue_eq_zero_of_poly_eq hpoly.symm` in the generic proof.
- Mathlib `Algebra/BigOperators/Group/Finset/Basic.lean:355` generates `Finset.sum_eq_single`
  with implicit set and summand. The off-diagonal polynomial inequality has the required direction.
- `Set.Finite.preimage` and native `MilnorExactSequence.lean:73-79` support the chosen finite
  preimage construction. The latter is a source comparison, not an added import.
- Native norm equals negative infinity residue. Its value on `1` already carries the field
  degree, so the sum must not receive a second degree multiplier.

The text-only audit checks direct import paths, placeholder tokens, line widths, trailing
whitespace, theorem/example counts, unique occurrence of the generic lift construction, and
unchanged scalar-factor consumer hashes. `git diff --check` is also run. None of these is a
Lean parse, elaboration, native lint, test execution, axiom audit, or kernel replay.

After the pinned native SimpleNorm closure finishes, the norm validation owner should compile
the canonical `Colib.KTheory.MilnorK.Norm.FiniteReciprocity` and
`ColibTest.MilnorFiniteReciprocity` files at the handed-off commit, then check the unchanged
`ScalarFactorReduction` consumers against that same implementation. The historical top-level
`FiniteReciprocity.lean` is not a second compilation or delivery target. Any elaboration fixes
belong on this same independent branch before a later authorized main integration.

## Mathematical proof already written

### Actual factor contraction

For a field `k`, any commutative ring `A`, a map `phi : k ->+* A`, an irreducible `p`, and a
nonunit `q` dividing `p.map phi`, the proof establishes, for every `r : k[X]`,

`q | r.map phi` if and only if `p | r`.

If the latter divisibility fails, `p` and `r` are coprime in the polynomial PID. Their coefficient
images remain coprime. A common divisor `q` would then be a unit, a contradiction. The reverse
implication is divisibility under a ring map. The second theorem rewrites this as the exact
equality of actual ideals

`(span {q}).comap (Polynomial.mapRingHom phi) = span {p}`.

No monicity, irreducibility of `q`, separability, characteristic, or finiteness is needed. The
source and coefficient target have independent universes. For a field target and irreducible
`q`, the reversed ideal equality is precisely Mathlib `localRingHom`'s required argument.

### Finite reciprocity

Let `s` index distinct actual monic irreducibles `psi i`, with varying degrees. Suppose all
other finite residues of `y` vanish. Choose the existing single-residue lift `z i` of
`residue (psi i) y` and subtract their finite sum from `y`.

At a listed point, every other lift vanishes, and its own lift cancels that residue. At an
unlisted point all terms vanish. The native exactness lemma places the difference in degree-zero
polynomial filtration, and native infinity residue kills it. Since each simple norm is the
negative infinity residue of its lift, the desired finite sum follows.

This works for arbitrary, not necessarily homogeneous classes. The norm input and output
retain their existing grading. There is no field-norm or tower-independence argument.

### Conditional scalar-factor reduction

For one source single lift `y` of `x`, a ring map `Phi : RatFunc k ->+* RatFunc K`, and a
coefficient map `phi`, the reduction consumes exactly:

- the image's residue at each listed target factor;
- absence of every other target residue;
- the infinity comparison on this very `y`.

The weighted version spells the first input as

`res_q (map Phi y) = m_q * map (AdjoinRoot.map phi p q hq) x`.

It concludes the expected weighted sum of existing simple norms by finite reciprocity and
additivity. Its weights are supplied natural numbers; it does **not** prove that they equal
factor multiplicities. The same-universe restriction is inherited from native `milnorKRingMap`.

## Actual-map source milestone and remaining obligations

Obligations A-C now have explicit source implementations in this branch. They remain uncompiled,
so they are not established Lean results. D-G are still unfinished mathematical/formal work;
their premises must not be hidden in the final endpoint. For a first complete norm formula,
finite separable coefficient extensions remain a useful target. The A-C supporting statements
themselves do not need finiteness, separability, perfection, or a characteristic hypothesis.

### A. Use the actual rational coefficient map

Written in `Colib/FieldTheory/RatFunc/CoefficientMap.lean`:

- `Polynomial.nonZeroDivisors_le_comap_mapRingHom` supplies the exact denominator certificate
  from injectivity of a field coefficient map and polynomial-map injectivity.
- `RatFunc.mapRingHom_algebraMap` proves evaluation on every polynomial by applying the native
  fraction formula with denominator `1`.

Written in `Colib/KTheory/MilnorK/Norm/CoefficientResidueFields.lean`:

- `ratFunc_mapRingHom_comp_algebraMap_localizationAtPrime` proves the literal ring-hom equality
  between actual rational coefficient change after the source local inclusion, and the target
  local inclusion after native `Localization.localRingHom`.
- `ratFunc_mapRingHom_algebraMap_localizationAtPrime` evaluates that equality on every local
  element, supplying exactly the `hf` input of native ramified residue naturality.

The local-square statements work for arbitrary source and target prime ideals whose contraction
equality is given. At an actual irreducible scalar factor, `FactorContraction.lean` constructs
that equality. The proof uses native localization extensionality and the native polynomial/local/
rational scalar towers. No rational-function map is defined or left unspecified.

### B. Identify the actual residue-field map

Write `P = span {p}`, `Q = span {q}` and let `j` be native `localRingHom P Q` from A. The new
`CoefficientResidueFields.lean` proves both directions of the literal ring-hom dictionary,
including

`quotientEquiv(Q)^(-1) o ResidueField.map(j) o quotientEquiv(P)
  = AdjoinRoot.map phi p q hq`.

The endpoints take only actual native monic irreducibles and the divisibility of the coefficient
image, not an assumed comparison equation. Their theorem names are
`residueField_map_comp_quotientRingEquivResidueField` and
`quotientRingEquivResidueField_symm_comp_residueField_map`.

The proof reduces to polynomial classes using native quotient extensionality, then applies
`residue_algebraMap_eq_quotientRingEquivResidueField`, `ResidueField.map_residue`, and
`localRingHom_to_map`. The new lower leaf `Colib/RingTheory/AdjoinRoot/Map.lean` contributes
`AdjoinRoot.map_mk`, a calculation of the existing map on polynomial classes by native
`lift_mk`, `Polynomial.eval₂_map`, and `AdjoinRoot.aeval_eq`. It defines no additional map.

### C. Supply the actual multiplicity and uniformizer equation

Written in `Colib/RingTheory/Polynomial/FactorMultiplicity.lean`:

- `exists_map_eq_pow_multiplicity_mul_and_not_dvd` extracts
  `p.map phi = q ^ multiplicity q (p.map phi) * r` with `q` not dividing `r`, directly from native
  finite-multiplicity extraction. This only needs nonzero `p` and nonunit `q`.
- `exists_atPrime_unit_mul_pow_multiplicity_map` turns `r` into a unit in the native localization
  at `span {q}`, gives image `p = unit * image q ^ m`, and proves `0 < m` from factor divisibility.
  It assumes the target principal ideal is prime; actual irreducible factors supply this instance.
- `multiplicity_map_eq_count_normalizedFactors` identifies `m` with the count of literal `q`
  in the actual normalized-factor multiset when `q` is monic irreducible. Only this count-format
  statement takes `[DecidableEq K]`; the extraction and unit statements do not.

`CoefficientResidueFields.lean` adds `exists_localRingHom_unit_mul_pow_multiplicity`, substituting
the actual native local coefficient map into this equation. It is exactly the `hπmap` input of
ramified residue naturality, with the exponent proved to be the actual multiplicity rather than
an arbitrary supplied natural number. The source and target polynomial images are native
uniformizers by the existing `irreducible_algebraMap_self` theorem.

No separate order, valuation, product decomposition, or factor model is introduced. The
normalized-factor finite indexing and its support proof still belong to the eventual norm
endpoint, but the local multiplicity and its positive unit equation are now written.

### Source review and new consumers for A-C

All new fields and rings have independent source and target universes. These are field/ring
equations; they do not use the same-universe-only native `milnorKRingMap`. Later Milnor equations
must respect that separate universe boundary.

Three new test leaves add eleven source consumers:

- `ColibTest/RatFuncCoefficientMap.lean`: polynomial evaluation, arbitrary fractions, preservation
  of `X`, and evaluation of the native quotient map, four consumers.
- `ColibTest/PolynomialFactorMultiplicity.lean`: extraction, local unit/positivity, actual count,
  and a repeated-factor input whose local exponent remains two, four consumers. The last one is
  a repeated-polynomial regression, not a proved inseparable field-extension base-change formula.
- `ColibTest/MilnorCoefficientResidueFields.lean`: local-element fraction square, residue-field
  dictionary on a quotient class, and actual local-uniformizer equation, three consumers.

Independent static review caught a missing `Polynomial` scope in the new AdjoinRoot leaf; this
was corrected before handoff. It otherwise found the checked API argument order, scalar-tower
instances, maximal/prime instances, and dictionary orientations consistent with pinned source.
This is not compiler evidence. Dependent instances, definitional equality between `AdjoinRoot`
and the native quotient, rewrite elaboration, and the new tests still require real validation.

### D. Derive finite-place Milnor naturality

Apply existing `dvrMilnorTameSymbol_map_ramified` at the specified polynomial uniformizers,
or its canonical version after the native normalization comparison. Combine A, B, and C to
obtain the all-degree equation

`res_q (map Phi y) = m_q * map (AdjoinRoot.map phi p q hq) (res_p y)`.

The named polynomial residue is the native shift map followed by the quotient/residue-field
equivalence. Its dictionary is `monicIrreducibleResidue_apply`. For arbitrary ring classes,
extend the tuple-symbol equation by the existing additive generation lemma, or first prove
the homogeneous equation and use finite homogeneous generation. Do not silently identify
specified and canonical uniformizer maps.

### E. Prove the image support statement

In the finite algebraic coefficient-extension range, every target closed point lies over an
actual source closed point. Prove this by taking a root of its actual `AdjoinRoot`, using its
integrality over the finite coefficient extension and then over the source, and taking the
source minimal polynomial. The target polynomial divides the coefficient image of this
minimal polynomial. Apply D.

If the target point is not a factor of `p.map phi`, its contracted source polynomial is not
`p`, so the original single-lift condition kills its residue. This proves the exact `hsupport`
premise in the reduction. For arbitrary transcendental coefficient extensions, this argument
does not apply: points with zero contraction need a separate numerator/denominator unit proof.

### F. Prove infinity naturality

First use A-D at `p = X`, `q = X`, where the coefficient uniformizer has exponent one. Then
prove the actual coefficient map commutes with native `projectiveLineChartInversion`.
Both compositions agree on polynomial constants and `X`; fraction-ring extensionality gives
the ring-hom equality. Use the actual residue-field-at-origin equivalences, not a new
specialization map. This yields

`infinityResidueRing K (map Phi y) = map phi (infinityResidueRing k y)`.

The minus sign in `simpleMilnorNorm_eq` is already retained by the reduction, and the finite
residue convention places the uniformizer last.

### G. Close the actual endpoint

Instantiate the reduction with the native chosen single lift, actual normalized factors,
the proved multiplicities, and D-F. Remove all supplied compatibility premises from the final
scalar-factor theorem. Its conclusion must still mention `simpleMilnorNorm` at actual factors,
not an unproved identification with `milnorKNorm`.

## Suggested validation order

After explicit authorization to compile: the lower coefficient-map, AdjoinRoot evaluation,
factor-contraction, and factor-multiplicity leaves; then `CoefficientResidueFields` and their new
test leaves. Also validate finite reciprocity, conditional reduction, and their consumers at
the same commit. Continue D-F incrementally on this same branch. The main
elaboration risks currently untested are dependent quotient field instances, finite-sum binder
rewrites, `Finset.sum_eq_single`'s inferred functions, and definitional equality between the native
polynomial quotient and `AdjoinRoot` in the weighted reduction.

Actual endpoint tests should include the identity coefficient map, one irreducible scalar
factor, complete splitting, a repeated-factor/inseparable case for the weighted API, the empty
Milnor prefix, degree zero, and two fields in each promised universe range. The current twenty-eight
consumers test only the written supporting statements, not these future unconditional cases.

## Source provenance and limitations

The mathematical code uses the pinned native statements listed in `SCALAR_BASE_CHANGE_SCOPE.md`.
The consolidated sigma corollaries and six regression consumers also draw on the historical
source drafts identified above. No deleted Aglib checkout was read, reconstructed, or
claimed as an available source. No external theorem is asserted to have been ported line by
line. The mathematical ownership remains native Stacks/Mathlib, with Colib theorem extensions.

The exact remaining blocker is unfinished formal mathematical work at D-G and the absence of
elaboration evidence for the A-C supporting sources, not a permission denial or an uncertain
tool action. No failed Lean run occurred because none was launched.
