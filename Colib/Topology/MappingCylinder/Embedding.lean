/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MappingCylinder.SourceCollar

/-! # The original mapping-cylinder embedding and projection equivalence

Extracted from the geometric declarations of
`Quillen/Topology/LocalCoefficients/MappingCylinderAcyclicity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No relative chain model or
acyclicity assumption is imported into this lower topological owner.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u

namespace TopCat.MappingCylinder
variable {X Y M : TopCat.{u}} {f : X ⟶ Y}
  {l : X ⊗ TopCat.I ⟶ M} {c : Y ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) f l c)

include sq

/-- The actual source inclusion is an embedding, witnessed by its product collar. -/
theorem mappingCylinderStart_isEmbedding : Topology.IsEmbedding (TopCat.ι₀ ≫ l) := by
  let e := SourceCollar.collarHomeomorph sq 1
  have h : Topology.IsEmbedding (fun x : X ↦
      (e (x, (⟨0, zero_lt_one⟩ : SourceCollar.Interval 1))).val) :=
    Topology.IsEmbedding.subtypeVal.comp
      (e.isEmbedding.comp (isEmbedding_prodMkLeft _))
  exact h

/-- The genuine projection is exactly the inverse map of the established deformation retract. -/
def mappingCylinderProjectionHomotopyEquiv : ContinuousMap.HomotopyEquiv M Y :=
  (mappingCylinderTargetStrongDeformationRetract sq).toHomotopyEquiv.symm

@[simp]
theorem mappingCylinderProjectionHomotopyEquiv_toFun :
    (mappingCylinderProjectionHomotopyEquiv sq).toFun =
      (mappingCylinderProjection sq).hom := rfl

end TopCat.MappingCylinder
