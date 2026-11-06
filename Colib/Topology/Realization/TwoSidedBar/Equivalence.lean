/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.TwoSidedBar.AugmentationEquivalence

/-!
# Classifying-space equivalence from the two-sided bar

The two-sided bar augmentations provide the stated classifying-space comparison under the
    specified homotopy equivalence hypotheses.


Implementation provenance:
`Quillen/Topology/Realization/TwoSidedBar/Equivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA



noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace SSet.TwoSidedBar
open TheoremA
variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})

/-- The original diagonal evaluation augmentation, with the constant-outer
identification made explicit. -/
def evaluationMap : diagonalSSet (bar H) ⟶ diagonalSSet H :=
  diagonalMap (evaluation H) ≫ (diagonalConstantIso (diagonalSSet H)).hom

/-- Evaluation is a realization equivalence by the actual transposed
resolution-category contraction and diagonal invariance. -/
theorem evaluationMap_isRealizationEquivalence :
    IsRealizationEquivalence (evaluationMap H) := by
  have ht := BisimplicialRealization.diagonalMap_isRealizationEquivalence
    ((flipFunctor _ _ _).map (evaluation H))
    (fun n ↦ evaluationColumn_isRealizationEquivalence H (op ⦋n⦌))
  have hd : IsRealizationEquivalence (diagonalMap (evaluation H)) := by
    apply IsRealizationEquivalence.of_iso_square _ _
      (diagonalFlipIso (bar H)).symm
      (diagonalFlipIso ((Functor.const SimplexCategoryᵒᵖ).obj (diagonalSSet H))).symm _ ht
    apply NatTrans.ext
    funext p
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  apply IsRealizationEquivalence.of_iso_square _ _ (Iso.refl _)
    (diagonalConstantIso (diagonalSSet H)).symm _ hd
  simp [evaluationMap]

/-- The second actual augmentation realizes to a homotopy equivalence with
exactly the original evaluation map as its forward map. -/
def evaluationRealizationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |diagonalSSet (bar H)| |diagonalSSet H| := by
  let E := (evaluationMap_isRealizationEquivalence H).choose
  have hE := (evaluationMap_isRealizationEquivalence H).choose_spec
  exact {
    toFun := (SSet.toTop.map (evaluationMap H)).hom
    invFun := E.invFun
    left_inv := by rw [← hE]; exact E.left_inv
    right_inv := by rw [← hE]; exact E.right_inv }

@[simp] theorem evaluationRealizationHomotopyEquiv_toFun :
    (evaluationRealizationHomotopyEquiv H).toFun =
      (SSet.toTop.map (evaluationMap H)).hom := rfl

/-- The augmentation retains strict naturality in the original diagram. -/
theorem evaluationMap_naturality {H J : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : H ⟶ J) :
    diagonalMap (map indexProjection (Functor.whiskerLeft indexProjection η)) ≫ evaluationMap J =
      evaluationMap H ≫ diagonalMap η := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.hom_ext
  intro z
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality
      (indexProjection.map (fullEdge z.1) ≫ z.2.2.down.op)) p) z.2.1 |>.symm

/-- The canonical bar vertex over the actual degree-zero ordinal. -/
def vertex (x : (diagonalSSet H) _⦋0⦌) : (diagonalSSet (bar H)) _⦋0⦌ :=
  ⟨(Functor.const (Fin 1)).obj (AsSmall.up.obj (op ⦋0⦌)), x, ULift.up (𝟙 ⦋0⦌)⟩

/-- The evaluation augmentation preserves the prescribed original vertex. -/
@[simp] theorem evaluationMap_vertex (x : (diagonalSSet H) _⦋0⦌) :
    (evaluationMap H).app (op ⦋0⦌) (vertex H x) = x := by
  change (H.map (𝟙 (op ⦋0⦌))).app (op ⦋0⦌) x = x
  rw [H.map_id]
  rfl

/-- The first augmentation keeps the original coefficient at its chosen
index, with no basepoint transport hidden in its path. -/
@[simp] theorem drop_vertex (x : (diagonalSSet H) _⦋0⦌) :
    (diagonalMap (drop indexProjection (liftedDiagram H))).app (op ⦋0⦌) (vertex H x) =
      ⟨(Functor.const (Fin 1)).obj (AsSmall.up.obj (op ⦋0⦌)), x⟩ := rfl

end SSet.TwoSidedBar

end
