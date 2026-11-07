/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Naturality
public import Colib.Topology.Homotopy.HomotopyGroup.MovingBasepoint

/-!
# Exact vertex tracks of realized natural transformations

The existing native vertex-track theorem is reused in independent object and
morphism universes. The track of an object vertex is the actual edge path of the corresponding
component arrow. This retains the path required for moving-basepoint transport.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval

namespace CategoryTheory

/-- The vertex track after recording the actual functorial endpoint identifications. -/
def classifyingSpaceNaturalTransformationTrack
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) :
    Path (classifyingSpacePoint (F.obj c)) (classifyingSpacePoint (G.obj c)) :=
  ((classifyingSpaceNaturalTransformationHomotopy α).evalAt (classifyingSpacePoint c)).cast
    (classifyingSpaceMap_point F c).symm (classifyingSpaceMap_point G c).symm

@[simp]
lemma classifyingSpaceNaturalTransformationTrack_eq
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) :
    classifyingSpaceNaturalTransformationTrack α c = classifyingSpacePath (α.app c) := by
  ext t
  exact classifyingSpaceNaturalTransformationHomotopy_vertex_general α c t

/-- The change of basepoint for a natural transformation is its original component edge. -/
theorem pathTransport_classifyingSpaceMap_naturalTransformation
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace C) (classifyingSpacePoint c)) :
    pathTransport (classifyingSpacePath (α.app c)) n
      (HomotopyGroup.map (classifyingSpaceMap F).hom (classifyingSpaceMap_point F c) a) =
        HomotopyGroup.map (classifyingSpaceMap G).hom (classifyingSpaceMap_point G c) a := by
  rw [← classifyingSpaceNaturalTransformationTrack_eq α c]
  exact pathTransport_homotopyGroupMap_homotopy_cast
    (classifyingSpaceNaturalTransformationHomotopy α) (classifyingSpacePoint c)
    (classifyingSpaceMap_point F c) (classifyingSpaceMap_point G c) n a

end CategoryTheory
