/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.TopExtRingQuotient

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) (x : R) :
    Koszul.seqTopExtClass f hf (ModuleCat.of R R) x = 0 ↔ x ∈ Ideal.span (Set.range f) :=
  Koszul.seqTopExtClass_ring_eq_zero_iff f hf x

example (f : Fin 2 → R) (hf : Koszul.IsKoszulRegular f) :
    Koszul.seqTopExtRingQuotientLinearEquiv f hf 1 =
      Koszul.seqTopExtClass f hf (ModuleCat.of R R) 1 :=
  Koszul.seqTopExtRingQuotientLinearEquiv_apply_mk f hf 1

-- The parameter n = 0 is length one, not the empty sequence.
example (f : Fin 1 → R) (hf : Koszul.IsKoszulRegular f) (x : R) :
    Koszul.seqTopExtClass f hf (ModuleCat.of R R) x = 0 ↔ x ∈ Ideal.span (Set.range f) :=
  Koszul.seqTopExtClass_ring_eq_zero_iff f hf x

example {n : ℕ} (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f) (x : R) :
    Koszul.seqTopExtRingQuotientLinearEquiv f hf
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) x) =
        Koszul.seqTopExtClass f hf (ModuleCat.of R R) x :=
  Koszul.seqTopExtRingQuotientLinearEquiv_apply_mk f hf x

example {n : ℕ} (f : Fin (n + 1) → R) (hf : Koszul.IsKoszulRegular f)
    (a y : R ⧸ Ideal.span (Set.range f)) :
    letI := Ext.quotientSourceModule (Ideal.span (Set.range f)) (ModuleCat.of R R) (n + 1)
    Koszul.seqTopExtRingQuotientLinearEquiv f hf (a • y) =
      a • Koszul.seqTopExtRingQuotientLinearEquiv f hf y := by
  let := Ext.quotientSourceModule (Ideal.span (Set.range f)) (ModuleCat.of R R) (n + 1)
  exact (Koszul.seqTopExtRingQuotientLinearEquiv f hf).map_smul a y
