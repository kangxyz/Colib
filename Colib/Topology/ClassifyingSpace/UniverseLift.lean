/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.UniverseMap
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Genuine universe lifting of classifying spaces

Lifting the objects and morphisms of a category produces a homeomorphic
classifying space in an arbitrary larger universe. Both directions are
realizations of the original categorical up/down functors, so the comparison
preserves every original simplex coordinate and object vertex.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite SSet
open scoped Simplicial Topology
universe u v w
namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-- Lifting both categorical universes preserves the original classifying space. -/
def classifyingSpaceUniverseHomeomorph :
    ClassifyingSpace C ≃ₜ ClassifyingSpace (AsSmall.{w} C) where
  toFun := classifyingSpaceMapUniversal AsSmall.up
  invFun := classifyingSpaceMapUniversal AsSmall.down
  left_inv x := by
    change ((classifyingSpaceMapUniversal AsSmall.down).comp
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{w} C))) x = x
    rw [← classifyingSpaceMapUniversal_comp]
    change classifyingSpaceMapUniversal (𝟭 C) x = x
    rw [classifyingSpaceMapUniversal_id]
    rfl
  right_inv x := by
    change ((classifyingSpaceMapUniversal AsSmall.up).comp
      (classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{w} C ⥤ C))) x = x
    rw [← classifyingSpaceMapUniversal_comp]
    change classifyingSpaceMapUniversal (𝟭 (AsSmall.{w} C)) x = x
    rw [classifyingSpaceMapUniversal_id]
    rfl
  continuous_toFun := (classifyingSpaceMapUniversal AsSmall.up).continuous
  continuous_invFun := (classifyingSpaceMapUniversal AsSmall.down).continuous

@[simp] theorem classifyingSpaceUniverseHomeomorph_point (c : C) :
    classifyingSpaceUniverseHomeomorph.{u, v, w} C (classifyingSpacePoint c) =
      classifyingSpacePoint (AsSmall.up.obj c) :=
  classifyingSpaceMapUniversal_point _ _

@[simp] theorem classifyingSpaceUniverseHomeomorph_symm_point (c : AsSmall.{w} C) :
    (classifyingSpaceUniverseHomeomorph C).symm (classifyingSpacePoint c) =
      classifyingSpacePoint (ULift.down c) :=
  classifyingSpaceMapUniversal_point _ _

@[simp] theorem classifyingSpaceUniverseHomeomorph_simplex (n : SimplexCategory)
    (x : (nerve C).obj (op n)) (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    classifyingSpaceUniverseHomeomorph.{u, v, w} C (realizationSimplex x t) =
      realizationSimplex (x ⋙ AsSmall.up) t :=
  classifyingSpaceMapUniversal_simplex _ _ _ _

end CategoryTheory
