/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.EdgePath
public import Colib.Topology.ClassifyingSpace.Basic
public import Mathlib.CategoryTheory.Category.ULift

/-!
# An actual nerve isomorphism for common-universe models

Up/down postcomposition is strictly inverse on original nerves. Its realized
homeomorphism preserves the original object vertices, without changing the
maximum realization universe.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/AsSmall.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u v
namespace CategoryTheory
open scoped Simplicial
variable (C : Type u) [Category.{v} C]

/-- The original nerve is strictly isomorphic to its common-universe lifted nerve. -/
def asSmallNerveIso : nerve C ≅ nerve (AsSmall.{0} C) where
  hom := {
    app _ := ↾fun F ↦ F ⋙ AsSmall.up
    naturality _ _ _ := by ext F; rfl }
  inv := {
    app _ := ↾fun F ↦ F ⋙ AsSmall.down
    naturality _ _ _ := by ext F; rfl }
  hom_inv_id := by ext n F; rfl
  inv_hom_id := by ext n F; rfl

/-- The classifying-space homeomorphism obtained by realizing the nerve isomorphism to the
common-universe model `AsSmall C`. -/
def asSmallClassifyingHomeomorph : ClassifyingSpace C ≃ₜ ClassifyingSpace (AsSmall.{0} C) :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (asSmallNerveIso C))

@[simp] theorem asSmallClassifyingHomeomorph_point (c : C) :
    asSmallClassifyingHomeomorph C (classifyingSpacePoint c) =
      classifyingSpacePoint (AsSmall.up.obj c) := by
  change SSet.toTop.map (asSmallNerveIso C).hom (SSet.realizationPoint (nerveVertex c)) = _
  rw [SSet.realizationPoint_naturality]
  rfl

end CategoryTheory
