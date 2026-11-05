/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.EdgePath
public import Colib.Topology.ClassifyingSpace.Basic

/-!
# Paths represented by categorical arrows

Extracted from `Quillen/Topology/Realization/Homotopy.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, endpoints,
relative homotopies, universe parameters and multiplication order are retained.
Only native namespace and import ownership change unless noted below.

-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval
open SSet

namespace CategoryTheory

/-- The path in a classifying space represented by a morphism. -/
def classifyingSpacePath {C : Type u} [Category.{v} C] {c d : C} (f : c ⟶ d) :
    Path (classifyingSpacePoint c) (classifyingSpacePoint d) :=
  realizationEdgePath (CategoryTheory.nerve.edgeMk f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem classifyingSpacePath_id {C : Type u} [Category.{v} C] (c : C) :
    classifyingSpacePath (𝟙 c) = Path.refl (classifyingSpacePoint c) := by
  unfold classifyingSpacePath
  erw [CategoryTheory.nerve.edgeMk_id, realizationEdgePath_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem classifyingSpacePath_naturality {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {c d : C} (f : c ⟶ d) (t : unitInterval) :
    classifyingSpaceMap F (classifyingSpacePath f t) =
      classifyingSpacePath (F.map f) t := by
  unfold classifyingSpaceMap classifyingSpacePath
  erw [realizationEdgePath_naturality_apply]
  simp only [SSet.Edge.map_edge,
    CategoryTheory.nerve.edgeMk_edge, CategoryTheory.nerveMap_app_mk₁]
  rfl

/-- A natural transformation provides paths between the images of each object. -/
def naturalTransformationPointPath {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) :
    Path (classifyingSpacePoint (F.obj c)) (classifyingSpacePoint (G.obj c)) :=
  classifyingSpacePath (α.app c)

end CategoryTheory

attribute [colib_tag "COL-0084",
  colib_ref "WeibelKBook" "IV, Recipe 3.1.1 and Definition 3.1.4"
    "adaptation"
    "Paths of actual categorical arrows, including natural-transformation components"]
  CategoryTheory.classifyingSpacePath
  CategoryTheory.classifyingSpacePath_naturality
  CategoryTheory.naturalTransformationPointPath
