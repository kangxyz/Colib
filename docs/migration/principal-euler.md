# Principal Euler length and associativity

## Chosen objects and normalization

The owner is `Colib/RingTheory/Multiplicity/PrincipalEuler/`. The scalar Euler
integer is `Module.principalEuler (N := M) t`, a transparent abbreviation for
Stacks' `AlgebraicGeometry.periodicLength` of the existing `twoPeriodicComplex`
with degree-zero differential zero and degree-one differential multiplication
by `t`. The concrete formula is

`length(M / tM).toNat - length(ker(t : M → M)).toNat`, with both terms cast to
integers before subtraction. The sign is cokernel minus kernel.

The expression is defined for every module. Its finite-length interpretation
requires separate hypotheses, since `ENat.toNat` sends infinity to zero.
`Module.FinitePrincipal M t` states that the two native scalar homology modules
have finite length. There is no second scalar-homology, periodic-complex,
prime-filtration, or localization datatype.

The ring and module universes are independent. Additivity permits all three
modules of a short exact sequence to occupy different universes.

## Reading and dependency order

1. `Basic.lean` identifies the native periodic length with the concrete
   expression (Stacks 0EA6), proves finite-length cancellation (0EA8), and
   removes the kernel contribution for a regular scalar. Regularity alone
   does not assert finite quotient length.
2. `Additivity.lean` specializes
   `Module.lengthIndex_add_of_ladder` to scalar multiplication. Finite scalar
   kernels and cokernels at the two ends of a short exact sequence imply
   middle finiteness and Euler additivity. Linear equivalence preserves both
   the Euler integer and finite scalar homology. The three-finiteness source
   signature is retained as a corollary, with its redundant binder named `_hV`.
3. `Support.lean` uses the native support criterion for finite length. Over a
   Noetherian ring, if `M` and `N` are finite and `Supp N ⊆ Supp M`, finite
   `M / tM` implies finite scalar homology of `N`. Submodules and actual
   subquotients inherit this property. No local or regularity hypothesis is
   needed here.
4. `Filtration.lean` uses `RelSeries` for
   `Submodule.IsQuotientEquivQuotientPrime`. The actual successive quotients,
   together with the supplied linear equivalences to `A / pᵢ`, give the Euler
   sum. Native finite-sum identities telescope it. Stacks 00L7 supplies the
   equality between minimal prime-label occurrence counts and the lengths of
   the original module localized at those points. Both conclusions use the
   same filtration. The generic statements take the filtration and finiteness
   conditions explicitly; the Noetherian finite-module corollaries derive them.
5. `Associativity.lean` depends only on `Basic.lean` and native upstream
   results. It directly specializes Stacks 02QF rather than repeating the
   filtration proof. The resulting intrinsic sum is independent of any
   selected filtration.

## Final endpoints and conditions

`Module.principalEuler_associativity_of_supportDim` assumes a finite module
over a Noetherian local ring, support dimension at most one, and finite scalar
cokernel length. It states that the Euler integer is the sum over minimal
points `q` of `Supp M` of

`length_{A_q}(M_q).toNat * principalEuler(A / q, t)`, in the integers.

The local module is the native
`LocalizedModule q.asIdeal.primeCompl M`, over `Localization.AtPrime q.asIdeal`.
The restricted `finsum` is a finite sum: native `finite_minimal_support` proves
the index set finite. Native `localized_length_ne_top` proves the weights
finite. The scalar-cokernel finiteness of each contributing prime quotient
also follows from the support theorem, since its support is contained in
`Supp M`.

`Module.principalEuler_associativity` replaces the dimension hypothesis with
`t ∈ IsLocalRing.maximalIdeal A`. The finite scalar cokernel then gives support
dimension at most one through Mathlib's dimension-drop inequality.

`Module.principalCokernel_associativity` additionally assumes
`IsSMulRegular M t`. It replaces the Euler expressions with principal-cokernel
lengths. Regularity on the prime quotients is derived from avoidance of the
minimal primes over the annihilator, not assumed separately.

No Cohen--Macaulay, equidimensional, domain, coefficient-flatness, or
nontrivial-module condition is added to these endpoints.

## The zero-dimensional case

Stacks 02QF sums orders of vanishing over nonclosed support points. Under a
dimension bound of at most one, these points are minimal, but the converse
can fail in dimension zero: the closed point can itself be minimal. Thus
`minimal_support_eq_nonclosed`, which assumes dimension exactly one, does not
apply to the final theorem's hypotheses.

The proof first identifies the order with the prime quotient's Euler integer
at each nonclosed point. Finite `M / tM` guarantees that the scalar avoids
those primes. It then extends the Euler-weighted sum to all minimal points;
every added point is the closed point, and its residue-field Euler integer
is zero. This includes the zero module and zero-dimensional modules.

The distinction is necessary. Over a field, for the zero scalar, the Euler
integer is zero but the order of vanishing is one. Extending the raw order
sum to the closed point would therefore give the wrong result. The test file
contains this zero-dimensional regression explicitly.

## Source correspondence and scope

The five Aglib source files under
`Aglib/RingTheory/Multiplicity/PrincipalEuler/` are read at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Their SHA-256 values, selected
declaration correspondence, and validation evidence are recorded in
`motivic-principal-euler.json`. The source headers retain the R5Lab
implementation credits at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.

This migration preserves the mathematical chain while replacing the source's
auxiliary scalar-homology and `PrimeFiltrationFrom` interfaces with native
objects. It does not claim literal compatibility with every source helper.
`Int.integer_telescope` is not copied: existing `Fin.sum_univ_succ` and
`Fin.sum_univ_castSucc` are used directly. Native 00L0 and 00L7 replace the
separate prime-filtration existence and multiplicity infrastructure.

The final formula is indexed by native minimal support points rather than an
ideal-indexed custom finite-set wrapper. `AlgebraicGeometry.minimal_support_iff`
identifies these with minimal primes over the annihilator. If a tensor-form
localization interface is needed later, native
`LocalizedModule.equivTensorProduct` transports the length; no new object is
needed. This is a local algebraic construction supporting the source's motivic
applications, not an original-object face-cycle equality or full motivic
comparison theorem.

## Validation boundary

`ColibTest/PrincipalEuler.lean` exercises independent universes, the exact
sequence with only outer finiteness, equivalence transport, support and actual
subquotients, the native filtration and local multiplicities, zero-dimensional
cancellation, and both final associativity endpoints.

Component validation and its source hashes are recorded in the adjacent JSON
ledger. COL-0169--COL-0173 register the five mathematical items in the
commutative-algebra chapter. The final registered tree passed scripts/check.sh,
including production build, tests, declaration and text lint, generated root
imports, allowlisted axiom audit and Library export. Final source and receipt
hashes are recorded separately from reconstructed component snapshots.
Compilation, source correspondence, and mathematical source review are
separate claims. No kernel replay was run.
