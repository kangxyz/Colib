/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Additivity.SubdivisionEquivalence

/-! # Waldhausen additivity for the original chosen-zero KMap

Source: Quillen/Waldhausen/Additivity/BasedAdditivity.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual global subdivision
comparison now discharges the only remaining comparison parameter.
This is the map-of-sum-functor equality; no separate group multiplication
formula or strict/normalized S-construction comparison is asserted here.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) [HasBinaryCoproducts D]
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

/-- Additivity of the actual canonically normalized diagonal group maps. -/
theorem diagonalKMap_additivity (n : ℕ) :
    diagonalKMap V W hs.exactG n =
      diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  Conditional.diagonalKMap_additivity SSet.OrdinalSubdivision.realizationComparison V W a b hs n

/-- Additivity of the original public KMap, with the actual sum functor H coproduct F. -/
theorem KMap_additivity (n : ℕ) :
    KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n :=
  Conditional.KMap_additivity SSet.OrdinalSubdivision.realizationComparison V W a b hs n

end CategoryTheory.Waldhausen.Additivity

attribute [colib_tag "COL-0219",
  colib_ref "WeibelKBook" "V, Additivity Theorem 1.2 and proof, page 2"
    "adaptation"
    "Original KMap equality with the actual quotient-before-subobject coproduct functor"]
  CategoryTheory.Waldhausen.Additivity.diagonalKMap_additivity
  CategoryTheory.Waldhausen.Additivity.KMap_additivity
