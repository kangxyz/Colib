/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.OrdinalSubdivisionConditional
public import Colib.Topology.Homotopy.HomotopyGroup.Equivalence
public import Colib.KTheory.Waldhausen.Additivity.SubdivisionGroupMap

/-! # Conditional cancellation of the actual horizontal subdivision map

Every conclusion explicitly takes the actual global ordinary-subdivision realization
comparison. Its existence is not proved or assumed implicitly in this file.
The final conclusion is equality of the original public KMap homomorphisms.
Adapted from Quillen/Waldhausen/Additivity/SubdivisionBasepoint.lean and
BasedAdditivity.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity.Conditional
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (comparison : SSet.OrdinalSubdivision.RealizationComparison.{max u v})
variable (V : Structure C) (W : Structure D)

/-- The conditional equivalence has the actual based subdivision endpoint as forward map. -/
def subdivisionPiEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      |SSet.diagonalSSet (SSet.OrdinalSubdivision.horizontal (bisimplicialSSet V))|
      (subdivisionBasepoint V) ≃*
    HomotopyGroup.Pi (n + 1) |SSet.diagonalSSet (bisimplicialSSet V)|
      (SSet.realizationPoint (diagonalZeroVertex V)) :=
  Topology.homotopyEquivPiEquiv
    (comparison.horizontalRealizationHomotopyEquiv (bisimplicialSSet V))
    (horizontalEndpoint_basepoint V) n

/-- The forward homomorphism is exactly the existing actual subdivision piMap. -/
@[simp]
theorem subdivisionPiEquiv_coe (n : ℕ) :
    ↑(subdivisionPiEquiv comparison V n) = subdivisionPiMap V n := rfl

include comparison

/-- Surjectivity is conditional on the supplied genuine global comparison. -/
theorem subdivisionPiMap_surjective (n : ℕ) :
    Function.Surjective (subdivisionPiMap V n) :=
  (subdivisionPiEquiv comparison V n).surjective

variable [HasBinaryCoproducts D] {F G H : C ⥤ D}
variable (a : F ⟶ G) (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The supplied comparison cancels the actual forward subdivision group map. -/
theorem diagonalKMap_additivity (n : ℕ) :
    diagonalKMap V W hs.exactG n =
      diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n := by
  ext q
  obtain ⟨p, rfl⟩ := subdivisionPiMap_surjective comparison V n q
  exact DFunLike.congr_fun (subdividedDiagonalKMap_additivity V W a b hs n) p

/-- Conditional additivity of the original KMap, with no replacement K-map or basepoint. -/
theorem KMap_additivity (n : ℕ) :
    KMap hs.exactG n = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n := by
  have hg := diagonalKMap_naturality V W hs.exactG n
  have hs' := diagonalKMap_naturality V W (sumFunctor_isExact V W hs.exactH hs.exactF) n
  have he := diagonalKMap_additivity comparison V W a b hs n
  ext q
  obtain ⟨p, rfl⟩ := (diagonalPiEquiv V n).surjective q
  calc
    KMap hs.exactG n (diagonalPiEquiv V n p) =
        diagonalPiEquiv W n (diagonalKMap V W hs.exactG n p) :=
      (DFunLike.congr_fun hg p).symm
    _ = diagonalPiEquiv W n
        (diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n p) :=
      congrArg (diagonalPiEquiv W n) (DFunLike.congr_fun he p)
    _ = KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n (diagonalPiEquiv V n p) :=
      DFunLike.congr_fun hs' p

end CategoryTheory.Waldhausen.Additivity.Conditional
