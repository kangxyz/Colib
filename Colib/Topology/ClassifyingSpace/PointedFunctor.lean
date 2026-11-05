/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.Functor.Rebase
public import Colib.Topology.ClassifyingSpace.Map

/-!
# Pointed classifying-space maps from a specified object isomorphism

Rebasing makes the image of the selected object literally the target object.
Realization is then pointed and induces a genuine homotopy-group map.
No independence of the chosen object isomorphism is asserted.

## Implementation provenance

Extracted from `Quillen/Topology/ClassifyingSpace/PointedFunctor.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The source maps, basepoints,
universes and degree shift are retained. Only ownership and lower imports change.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]

/-- Realization of the rebased functor preserves the specified basepoints. -/
theorem rebaseFunctor_map_point (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    classifyingSpaceMap (rebaseFunctor F c d e) (classifyingSpacePoint c) =
      classifyingSpacePoint d := by
  rw [classifyingSpaceMap_point, rebaseFunctor_obj_base]

/-- The genuine homomorphism between shifted homotopy groups at prescribed
base objects, associated to a functor and a specified base-object isomorphism. -/
def pointedShiftedHomotopyGroupMap (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) (n : ℕ) :
    ShiftedHomotopyGroup C c n →* ShiftedHomotopyGroup D d n :=
  HomotopyGroup.piMap n (classifyingSpaceMap (rebaseFunctor F c d e)).hom
    (rebaseFunctor_map_point F c d e)

set_option backward.isDefEq.respectTransparency false in
/-- The pointed construction preserves the identity functor. -/
@[simp]
theorem pointedShiftedHomotopyGroupMap_id (c : C) (n : ℕ) :
    pointedShiftedHomotopyGroupMap (𝟭 C) c c (Iso.refl c) n =
      MonoidHom.id (ShiftedHomotopyGroup C c n) := by
  have hF : rebaseFunctor (𝟭 C) c c (Iso.refl c) = 𝟭 C :=
    rebaseFunctor_refl (𝟭 C) c
  have hT : classifyingSpaceMap (rebaseFunctor (𝟭 C) c c (Iso.refl c)) =
      𝟙 (ClassifyingSpace C) := by rw [hF, classifyingSpaceMap_id]
  apply MonoidHom.ext
  intro a
  change HomotopyGroup.map (classifyingSpaceMap (rebaseFunctor (𝟭 C) c c (Iso.refl c))).hom
    (rebaseFunctor_map_point (𝟭 C) c c (Iso.refl c)) a = a
  simpa only [hT, TopCat.hom_id] using HomotopyGroup.map_id a



end CategoryTheory

attribute [colib_tag "COL-0054",
  colib_ref "WeibelKBook"
    "IV, Characterization 3.1(1), naturality" "ingredient"
    "Realization after explicit rebasing; no independence of the chosen isomorphism"]
  CategoryTheory.pointedShiftedHomotopyGroupMap
  CategoryTheory.pointedShiftedHomotopyGroupMap_id

attribute [colib_ref "HatcherAT"
    "Section 4.1, p. 342, functoriality of homotopy groups" "ingredient"
    "The strictly pointed realized map induces the shifted homotopy-group homomorphism"]
  CategoryTheory.pointedShiftedHomotopyGroupMap
