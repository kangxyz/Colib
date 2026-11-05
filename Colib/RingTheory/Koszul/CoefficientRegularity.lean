/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import StacksFrontier.RingTheory.Koszul.Defs
public import Colib.Util.References
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Regular.Category

/-!
# Regularity on coefficient Koszul terms

Scalar regularity and weak regular sequences on the coefficient module remain
regular on every term of the native exterior-power Koszul complex. This is a
thin application of Mathlib's preservation by flat tensor products: exterior
powers of the finite free sequence module are free.

The scalar endpoint rewrites `ChainComplex.Koszul.coefficientComplex_isSMulRegular`
from `Aglib.Algebra.Homology.Koszul.Coefficient` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, originally from Motivic's
`KoszulCoefficientComplex.lean`. No recursive tensor model or coordinate maps
are retained. The weak-regular-sequence and scalar short-exact endpoints are
consequences on the same native terms. No assertion of homology regularity or
of properness of the generated submodule is made.
-/

@[expose] public section

universe u v

open scoped ExteriorAlgebra

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}
variable (f : Fin r → R) (M : Type v) [AddCommGroup M] [Module R M]

/-- A scalar regular on the coefficients is regular on every native Koszul term. -/
theorem seqComplexTensor_isSMulRegular_X (a : R) (ha : IsSMulRegular M a) (n : ℕ) :
    IsSMulRegular ((seqComplexTensor f M).X n) a :=
  ha.lTensor (⋀[R]^n (Fin r → R))

/-- Weak regular sequences on the coefficients remain weakly regular on every term.
This does not assert properness; the terms above the sequence length are zero. -/
theorem seqComplexTensor_isWeaklyRegular_X (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular M s) (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular ((seqComplexTensor f M).X n) s :=
  hs.isWeaklyRegular_lTensor

/-- Scalar multiplication and its actual scalar quotient form a short exact
sequence on every Koszul term when the scalar is regular on the coefficients. -/
theorem seqComplexTensor_smulShortComplex_shortExact (a : R)
    (ha : IsSMulRegular M a) (n : ℕ) :
    (ModuleCat.smulShortComplex ((seqComplexTensor f M).X n) a).ShortExact :=
  (seqComplexTensor_isSMulRegular_X f M a ha n).smulShortComplex_shortExact

end Koszul

attribute [colib_tag "COL-0136"] Koszul.seqComplexTensor_isSMulRegular_X
  Koszul.seqComplexTensor_isWeaklyRegular_X Koszul.seqComplexTensor_smulShortComplex_shortExact

attribute [stacks 0622 "Definition ingredient: exterior-power terms, not coefficient regularity"]
  Koszul.seqComplexTensor_isSMulRegular_X
attribute [stacks 0623 "Definition ingredient: finite-sequence Koszul complex"]
  Koszul.seqComplexTensor_isWeaklyRegular_X
