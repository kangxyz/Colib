/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.Terminal
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.ClassifyingSpace.Map
public import Mathlib.Topology.Homotopy.Equiv
/-!
Adapted from `Quillen/Topology/ClassifyingSpace/GrothendieckTerminal.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# Actual realization retraction to a terminal Grothendieck fiber

The explicit terminal projection and fiber inclusion give a homotopy equivalence
of actual classifying spaces. Its forward map is the original projection, and
restriction to every fiber is exactly the classifying map of its original
transition. A comparison with ordinary or fat topological telescopes is separate.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section
universe u
namespace CategoryTheory.Grothendieck.Terminal
variable {J : Type u} [SmallCategory J] (F : J ⥤ Cat.{u, u})
  {t : J} (ht : IsTerminal t)

/-- The explicit base arrows realize to the deformation homotopy. -/
def unitClassifyingHomotopy :
    (ContinuousMap.id (ClassifyingSpace (Grothendieck F))).Homotopy
      ((classifyingSpaceMap (Grothendieck.ι F t)).hom.comp
        (classifyingSpaceMap (projection F ht)).hom) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (projectionInclusionUnit F ht)

/-- The strict terminal-fiber section realizes to the other endpoint homotopy. -/
def counitClassifyingHomotopy :
    ((classifyingSpaceMap (projection F ht)).hom.comp
      (classifyingSpaceMap (Grothendieck.ι F t)).hom).Homotopy
        (ContinuousMap.id (ClassifyingSpace (F.obj t))) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (counitIso F ht).hom

/-- The genuine classifying-space equivalence with the original projection as forward map. -/
def classifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Grothendieck F))
      (ClassifyingSpace (F.obj t)) where
  toFun := (classifyingSpaceMap (projection F ht)).hom
  invFun := (classifyingSpaceMap (Grothendieck.ι F t)).hom
  left_inv := ⟨(unitClassifyingHomotopy F ht).symm⟩
  right_inv := ⟨counitClassifyingHomotopy F ht⟩

theorem fiber_classifying_projection (j : J) :
    classifyingSpaceMap (Grothendieck.ι F j) ≫ classifyingSpaceMap (projection F ht) =
      classifyingSpaceMap (F.map (ht.from j)).toFunctor := by
  rw [← classifyingSpaceMap_comp, inclusion_projection]

end CategoryTheory.Grothendieck.Terminal
