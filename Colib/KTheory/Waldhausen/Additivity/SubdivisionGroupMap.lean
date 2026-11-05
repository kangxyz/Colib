/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.KTheory.Waldhausen.Additivity.DiagonalKMap
public import Colib.KTheory.Waldhausen.Additivity.SubdividedBasedHomotopy

/-! # Actual group maps before cancellation of horizontal subdivision

These consequences retain the original subdivision endpoint. No surjectivity
of that endpoint is asserted. The full KMap additivity theorem is not established here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D)

/-- The exact forward map whose surjectivity is needed for subdivision cancellation. -/
def subdivisionPiMap (n : ℕ) :
    HomotopyGroup.Pi (n + 1)
      |SSet.diagonalSSet (SSet.OrdinalSubdivision.horizontal (bisimplicialSSet V))|
      (subdivisionBasepoint V) →*
    HomotopyGroup.Pi (n + 1) |SSet.diagonalSSet (bisimplicialSSet V)|
      (SSet.realizationPoint (diagonalZeroVertex V)) :=
  HomotopyGroup.piMap n
    (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))
    (horizontalEndpoint_basepoint V)

variable [HasBinaryCoproducts D] {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H)
variable (hs : IsCofibrationSequence V W a b)

/-- The two actual diagonal maps agree after the displayed subdivision map. -/
theorem subdividedDiagonalKMap_additivity (n : ℕ) :
    (diagonalKMap V W hs.exactG n).comp (subdivisionPiMap V n) =
      (diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n).comp
        (subdivisionPiMap V n) := by
  let H := (subdividedBasedAdditivityHomotopy V W a b hs).trans
    (subdividedBasedAdditivityHomotopy V W (sumInr H F) (sumProjection W H F)
      (splitIsCofibrationSequence V W hs.exactH hs.exactF)).symm
  let hf := (congrArg
    (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase))
      (horizontalEndpoint_basepoint V)).trans (rebasedDiagonalMap_basepoint V W hs.exactG)
  have he := HomotopyGroup.piMap_eq_of_based_homotopy n
    (f := (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hs.exactG.rebase)).comp
      (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))))
    (g := (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq
      (sumFunctor_isExact V W hs.exactH hs.exactF).rebase)).comp
      (realizedDiagonalMap (SSet.OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)))) hf
    ((congrArg _ (horizontalEndpoint_basepoint V)).trans
      (rebasedDiagonalMap_basepoint V W (sumFunctor_isExact V W hs.exactH hs.exactF)))
    H.toHomotopy (fun t ↦ (H.eq_fst t (Set.mem_singleton _)).trans hf)
  exact (HomotopyGroup.mapHom_comp (N := Fin (n + 1))
    _ (horizontalEndpoint_basepoint V) _ (rebasedDiagonalMap_basepoint V W hs.exactG)).symm.trans
      (he.trans (HomotopyGroup.mapHom_comp (N := Fin (n + 1))
        _ (horizontalEndpoint_basepoint V) _
          (rebasedDiagonalMap_basepoint V W (sumFunctor_isExact V W hs.exactH hs.exactF))))

/-- The same equality uses the original public KMap after the actual diagonal comparison. -/
theorem subdividedKMap_additivity (n : ℕ) :
    (KMap hs.exactG n).comp ((diagonalPiEquiv V n).toMonoidHom.comp (subdivisionPiMap V n)) =
      (KMap (sumFunctor_isExact V W hs.exactH hs.exactF) n).comp
        ((diagonalPiEquiv V n).toMonoidHom.comp (subdivisionPiMap V n)) := by
  ext q
  calc
    _ = diagonalPiEquiv W n (diagonalKMap V W hs.exactG n (subdivisionPiMap V n q)) :=
      (DFunLike.congr_fun (diagonalKMap_naturality V W hs.exactG n) _).symm
    _ = diagonalPiEquiv W n
        (diagonalKMap V W (sumFunctor_isExact V W hs.exactH hs.exactF) n
          (subdivisionPiMap V n q)) :=
      congrArg (diagonalPiEquiv W n)
        (DFunLike.congr_fun (subdividedDiagonalKMap_additivity V W a b hs n) q)
    _ = _ := DFunLike.congr_fun
      (diagonalKMap_naturality V W (sumFunctor_isExact V W hs.exactH hs.exactF) n) _

end CategoryTheory.Waldhausen.Additivity
