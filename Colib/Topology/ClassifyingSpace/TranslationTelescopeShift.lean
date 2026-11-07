/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescopeShift
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.ClassifyingSpace.Map
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Right stabilization in the original monoidal telescope

The original index shift and stabilization arrows give inverse homotopies.
Their natural transformations are transported through the actual categorical
model equivalence before realization, so every realization map has the common
universe of the original telescope.

The functors and stabilization arrows are those of
`Quillen/Topology/ClassifyingSpace/TranslationTelescopeShift.lean` and
`Quillen/Topology/ClassifyingSpace/TelescopeShift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Grothendieck
universe u v

namespace CategoryTheory.MonoidalCategory.TranslationTelescope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)

/-- Transport the actual stabilization arrows to the common-universe model. -/
def rightStabilizationIndexShiftUnit :
    𝟭 (Model e) ⟶ rightStabilization e ⋙ indexShift e :=
  (modelEquivalence e).unitIso.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (modelEquivalence e).functor
      (EndofunctorTelescope.stabilizationShiftUnit (tensorRight e)))
      (modelEquivalence e).inverse ≫
    Functor.whiskerLeft
      ((modelEquivalence e).functor ⋙ EndofunctorTelescope.stabilization (tensorRight e))
      (Functor.whiskerRight (modelEquivalence e).counitIso.inv
        (EndofunctorTelescope.shift (tensorRight e) ⋙ (modelEquivalence e).inverse))

/-- The reverse order uses the original second stabilization transformation. -/
def indexShiftRightStabilizationUnit :
    𝟭 (Model e) ⟶ indexShift e ⋙ rightStabilization e :=
  (modelEquivalence e).unitIso.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (modelEquivalence e).functor
      (EndofunctorTelescope.shiftStabilizationUnit (tensorRight e)))
      (modelEquivalence e).inverse ≫
    Functor.whiskerLeft
      ((modelEquivalence e).functor ⋙ EndofunctorTelescope.shift (tensorRight e))
      (Functor.whiskerRight (modelEquivalence e).counitIso.inv
        (EndofunctorTelescope.stabilization (tensorRight e) ⋙ (modelEquivalence e).inverse))

/-- The original right stabilization is a homotopy equivalence, with index-shift inverse. -/
def rightStabilizationClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Model e)) (ClassifyingSpace (Model e)) where
  toFun := (classifyingSpaceMap (rightStabilization e)).hom
  invFun := (classifyingSpaceMap (indexShift e)).hom
  left_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using
      (classifyingSpaceNaturalTransformationHomotopy (rightStabilizationIndexShiftUnit e)).symm⟩
  right_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using
      (classifyingSpaceNaturalTransformationHomotopy (indexShiftRightStabilizationUnit e)).symm⟩

/-- The forward map is exactly the original stagewise stabilization. -/
theorem rightStabilizationClassifyingHomotopyEquiv_toFun :
    (rightStabilizationClassifyingHomotopyEquiv e).toFun =
      (classifyingSpaceMap (rightStabilization e)).hom := rfl

/-- The inverse is exactly the original index shift. -/
theorem rightStabilizationClassifyingHomotopyEquiv_invFun :
    (rightStabilizationClassifyingHomotopyEquiv e).invFun =
      (classifyingSpaceMap (indexShift e)).hom := rfl

/-- Right stabilization reflects the actual path-component relation. -/
theorem rightStabilization_joined_iff (x y : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (rightStabilization e) x)
      (classifyingSpaceMap (rightStabilization e) y) ↔ Joined x y := by
  let h := rightStabilizationClassifyingHomotopyEquiv e
  obtain ⟨H⟩ := h.left_inv
  constructor
  · intro hxy
    exact (show Joined x (h.invFun (h.toFun x)) from ⟨(H.evalAt x).symm⟩).trans
      ((hxy.map h.invFun.continuous).trans ⟨H.evalAt y⟩)
  · exact fun hxy ↦ hxy.map h.toFun.continuous

/-- Every component is reached by the actual right-stabilization map. -/
theorem exists_joined_rightStabilization (y : ClassifyingSpace (Model e)) :
    ∃ x, Joined (classifyingSpaceMap (rightStabilization e) x) y := by
  obtain ⟨H⟩ := (rightStabilizationClassifyingHomotopyEquiv e).right_inv
  exact ⟨(rightStabilizationClassifyingHomotopyEquiv e).invFun y, ⟨H.evalAt y⟩⟩

end CategoryTheory.MonoidalCategory.TranslationTelescope
