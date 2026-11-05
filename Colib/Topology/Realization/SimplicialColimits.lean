/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Monoidal.Closed.Types
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Simplicial cylinders preserve colimits

Products with fixed simplicial sets preserve colimits pointwise in types. Shape-specific
statements retain separate object and morphism universes and the necessary type-category
colimit hypothesis.

## Implementation provenance

Adapted from `Quillen/Topology/Realization/SimplicialColimits.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected declarations retain the source
constructions and mathematical universe parameters. Namespace and dependency ownership
are changed to the underlying Mathlib objects.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial

universe u w w'

namespace SSet

/-- Pointwise products preserve all diagram shapes for which the type category
has colimits, including diagrams with distinct object and morphism universes. -/
instance simplicialTensorLeft_preservesColimitsOfShape (X : SSet.{u})
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorLeft X) := by
  infer_instance

/-- The corresponding arbitrary-shape preservation result for the interval
on the right. -/
instance simplicialCylinder_preservesColimitsOfShape
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorRight (Δ[1] : SSet.{u})) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

/-- Product on the left with a fixed simplicial set preserves colimits. -/
instance simplicialTensorLeft_preservesColimits (X : SSet.{u}) :
    PreservesColimits (tensorLeft X) where
  preservesColimitsOfShape := by infer_instance

/-- Product with the simplicial interval preserves arbitrary colimits. -/
instance simplicialCylinder_preservesColimits :
    PreservesColimits (tensorRight (Δ[1] : SSet.{u})) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

end SSet

attribute [colib_tag "COL-0064",
  stacks 00VB "Pointwise presheaf colimits, applied to fixed simplicial products",
  stacks 0038 "(1), left-adjoint preservation for the pointwise Type product ingredient"]
  SSet.simplicialTensorLeft_preservesColimitsOfShape
  SSet.simplicialCylinder_preservesColimitsOfShape
  SSet.simplicialTensorLeft_preservesColimits
  SSet.simplicialCylinder_preservesColimits
