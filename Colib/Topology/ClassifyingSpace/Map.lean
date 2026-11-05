/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.ClassifyingSpace.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Functor maps on based classifying-space homotopy groups

The continuous map is the realization of the actual nerve map. Its action
on shifted homotopy groups is based at the original object and its image.

## Implementation provenance

Extracted from `Quillen/Topology/HomotopyGroups/Map.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The source maps, basepoints,
universes and degree shift are retained. Only ownership and lower imports change.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory

section ClassifyingSpaces

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]

/-- A functor induces a homomorphism on the shifted homotopy groups of
classifying spaces, based at an object and its image. -/
def shiftedHomotopyGroupMap (F : C ⥤ D) (c : C) (n : ℕ) :
    ShiftedHomotopyGroup C c n →* ShiftedHomotopyGroup D (F.obj c) n :=
  HomotopyGroup.piMap n (classifyingSpaceMap F).hom (classifyingSpaceMap_point F c)

/-- Realization of the nerve preserves identity functors. -/
@[simp]
theorem classifyingSpaceMap_id :
    classifyingSpaceMap (𝟭 C) = 𝟙 (ClassifyingSpace C) := by
  unfold classifyingSpaceMap
  change SSet.toTop.map (𝟙 (CategoryTheory.nerve C)) = _
  exact SSet.toTop.map_id _

/-- Realization of the nerve preserves composition of functors. -/
@[simp]
theorem classifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMap (F ⋙ G) = classifyingSpaceMap F ≫ classifyingSpaceMap G := by
  unfold classifyingSpaceMap
  change SSet.toTop.map (CategoryTheory.nerveMap F ≫ CategoryTheory.nerveMap G) = _
  exact SSet.toTop.map_comp _ _

@[simp]
theorem shiftedHomotopyGroupMap_id (c : C) (n : ℕ) :
    shiftedHomotopyGroupMap (𝟭 C) c n = MonoidHom.id (ShiftedHomotopyGroup C c n) := by
  unfold shiftedHomotopyGroupMap HomotopyGroup.piMap
  simp only [classifyingSpaceMap_id, TopCat.hom_id]
  exact HomotopyGroup.mapHom_id

@[simp]
theorem shiftedHomotopyGroupMap_comp {E : Type u} [Category.{v} E]
    (F : C ⥤ D) (G : D ⥤ E) (c : C) (n : ℕ) :
    shiftedHomotopyGroupMap (F ⋙ G) c n =
      (shiftedHomotopyGroupMap G (F.obj c) n).comp (shiftedHomotopyGroupMap F c n) := by
  unfold shiftedHomotopyGroupMap HomotopyGroup.piMap
  simp only [classifyingSpaceMap_comp, TopCat.hom_comp]
  exact HomotopyGroup.mapHom_comp _ _ _ _

end ClassifyingSpaces


end CategoryTheory

attribute [colib_tag "COL-0053",
  colib_ref "WeibelKBook"
    "IV, Characterization 3.1(1), naturality" "ingredient"
    "The actual realized nerve map preserves identity and composition"]
  CategoryTheory.shiftedHomotopyGroupMap
  CategoryTheory.shiftedHomotopyGroupMap_id
  CategoryTheory.shiftedHomotopyGroupMap_comp

attribute [colib_ref "HatcherAT"
    "Section 4.1, p. 342, functoriality of homotopy groups" "ingredient"
    "Pointed postcomposition induces the homomorphism in shifted degree"]
  CategoryTheory.shiftedHomotopyGroupMap
