/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Comma.AsSmall
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-!
# Quillen's Theorem A in independent object and morphism universes

The common-universe theorem transports along the actual classifying-space
universe-lifting homeomorphisms. The comma categories are compared using the
standard precomposition and postcomposition equivalences. The resulting
homotopy equivalence has the original functor's cross-universe realization as
its forward map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u₁ v₁ u₂ v₂
namespace CategoryTheory.TheoremA

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Contractibility of the original comma spaces passes to the common-universe model. -/
theorem asSmallComma_contractible (F : C ⥤ D)
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d)))
    (d : AsSmall.{max u₁ v₁ u₂ v₂} D) :
    ContractibleSpace (ClassifyingSpace (CostructuredArrow
      ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙ AsSmall.up) d)) := by
  let := h (ULift.down d)
  exact (equivalenceClassifyingHomotopyEquivUniversal
    (CostructuredArrow.asSmallEquivalence F d)).contractibleSpace

/-- Quillen's Theorem A for arbitrary source and target object and morphism universes. -/
def contractibleCommaClassifyingHomotopyEquivUniversal (F : C ⥤ D)
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d))) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) :=
  ((classifyingSpaceUniverseHomeomorph.{u₁, v₁, max u₁ v₁ u₂ v₂} C).toHomotopyEquiv.trans
    (contractibleCommaClassifyingHomotopyEquiv
      ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙ AsSmall.up)
      (asSmallComma_contractible F h))).trans
    (classifyingSpaceUniverseHomeomorph.{u₂, v₂, max u₁ v₁ u₂ v₂} D).symm.toHomotopyEquiv

/-- The arbitrary-universe theorem preserves the original functor's exact realized map. -/
@[simp] theorem contractibleCommaClassifyingHomotopyEquivUniversal_toFun (F : C ⥤ D)
    (h : ∀ d : D, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d))) :
    (contractibleCommaClassifyingHomotopyEquivUniversal F h).toFun =
      classifyingSpaceMapUniversal F := by
  change (classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D)).comp
    ((classifyingSpaceMap
      ((AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C) ⋙ F ⋙ AsSmall.up)).hom.comp
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C))) = _
  rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
    ← classifyingSpaceMapUniversal_comp]
  rfl

end CategoryTheory.TheoremA
