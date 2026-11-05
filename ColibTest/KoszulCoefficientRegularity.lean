/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

import Colib.RingTheory.Koszul.CoefficientRegularity

/-! Term-level regularity, independent coefficient universes and boundary degrees. -/

universe u v

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
variable (M : Type v) [AddCommGroup M] [Module R M]

-- Coefficients have an independent universe and need not be finite or flat.
example (a : R) (ha : IsSMulRegular M a) (n : ℕ) :
    IsSMulRegular ((Koszul.seqComplexTensor f M).X n) a :=
  Koszul.seqComplexTensor_isSMulRegular_X f M a ha n

-- The coefficient regularity sequence is independent of the Koszul sequence.
example (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular M s) (n : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular ((Koszul.seqComplexTensor f M).X n) s :=
  Koszul.seqComplexTensor_isWeaklyRegular_X f M s hs n

example (a : R) (ha : IsSMulRegular M a) (n : ℕ) :
    (ModuleCat.smulShortComplex ((Koszul.seqComplexTensor f M).X n) a).ShortExact :=
  Koszul.seqComplexTensor_smulShortComplex_shortExact f M a ha n

-- Empty Koszul sequence and degree zero are both included.
example (a : R) (ha : IsSMulRegular M a) :
    IsSMulRegular ((Koszul.seqComplexTensor (Fin.elim0 : Fin 0 → R) M).X 0) a :=
  Koszul.seqComplexTensor_isSMulRegular_X _ M a ha 0

-- No claim of properness is needed even above the length of the sequence.
example (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular M s) :
    RingTheory.Sequence.IsWeaklyRegular ((Koszul.seqComplexTensor f M).X (r + 1)) s :=
  Koszul.seqComplexTensor_isWeaklyRegular_X f M s hs (r + 1)
