/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Koszul.Ext

open CategoryTheory CategoryTheory.Abelian

universe u w

variable {R : Type u} [CommRing R]

-- Empty sequences are included, with no nontrivial-ring assumption.
example :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.ofList ([] : List R))) 0 :=
  Koszul.quotient_hasProjectiveDimensionLE_of_weaklyRegular [] (by simp)

-- The original list quotient and an arbitrary Ext universe are retained.
example [HasExt.{w} (ModuleCat.{u} R)] (a : R)
    (ha : RingTheory.Sequence.IsWeaklyRegular R [a]) (N : ModuleCat.{u} R)
    (e : Ext (ModuleCat.of R (R ⧸ Ideal.ofList [a])) N 2) : e = 0 :=
  Koszul.ext_eq_zero_above_length [a] ha N 2 (by simp) e

-- The primary sequence API uses precisely the upstream span-of-range quotient.
example {r : ℕ} (f : Fin r → R)
    (hf : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f)) :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.span (Set.range f))) r :=
  Koszul.hasProjectiveDimensionLE_quotient_of_isWeaklyRegular f hf

-- A unit generates the improper ideal; weak regularity still applies.
example :
    HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ Ideal.ofList ([1] : List R))) 1 := by
  apply Koszul.quotient_hasProjectiveDimensionLE_of_weaklyRegular ([1] : List R)
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact IsSMulRegular.one R

example : Ideal.ofList ([1] : List R) = ⊤ := by simp
