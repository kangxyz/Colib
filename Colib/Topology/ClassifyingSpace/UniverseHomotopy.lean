/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.UniverseLift
public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.ClassifyingSpace.Naturality
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Natural transformations of classifying-space maps across universes

The existing realized natural-transformation homotopy transports through the
actual universe-lifting homeomorphisms. Its endpoints are the original
cross-universe classifying-space maps. Adjunctions and equivalences of categories
therefore give homotopy equivalences in arbitrary object and morphism universes.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory SSet
open scoped Simplicial Topology
universe u₁ v₁ u₂ v₂
namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Cross-universe classifying-space maps preserve the original parametrized arrow paths. -/
@[simp] theorem classifyingSpaceMapUniversal_path (F : C ⥤ D)
    {c d : C} (f : c ⟶ d) (t : unitInterval) :
    classifyingSpaceMapUniversal F (classifyingSpacePath f t) =
      classifyingSpacePath (F.map f) t := by
  change classifyingSpaceMapUniversal F
    (realizationSimplex (ComposableArrows.mk₁ f) (stdSimplexHomeomorphUnitInterval.symm t)) = _
  rw [classifyingSpaceMapUniversal_simplex]
  have h : ComposableArrows.mk₁ f ⋙ F = ComposableArrows.mk₁ (F.map f) :=
    ComposableArrows.ext₁ rfl rfl (by simp)
  rw [h]
  rfl

/-- A natural transformation gives a homotopy of the original classifying spaces
in any universes. -/
def classifyingSpaceUniversalHomotopy {F G : C ⥤ D} (α : F ⟶ G) :
    (classifyingSpaceMapUniversal F).Homotopy (classifyingSpaceMapUniversal G) := by
  let C' := AsSmall.{max u₁ v₁ u₂ v₂} C
  let D' := AsSmall.{max u₁ v₁ u₂ v₂} D
  let U : C ⥤ C' := AsSmall.up
  let V : D' ⥤ D := AsSmall.down
  let F' : C' ⥤ D' := AsSmall.down ⋙ F ⋙ AsSmall.up
  let G' : C' ⥤ D' := AsSmall.down ⋙ G ⋙ AsSmall.up
  let α' : F' ⟶ G' := Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up)
  let H := classifyingSpaceNaturalTransformationHomotopy α'
  refine ((ContinuousMap.Homotopy.refl (classifyingSpaceMapUniversal V)).comp
    (H.compContinuousMap (classifyingSpaceMapUniversal U))).cast ?_ ?_
  · change (classifyingSpaceMapUniversal V).comp
      ((classifyingSpaceMap F').hom.comp (classifyingSpaceMapUniversal U)) = _
    rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
      ← classifyingSpaceMapUniversal_comp]
    rfl
  · change (classifyingSpaceMapUniversal V).comp
      ((classifyingSpaceMap G').hom.comp (classifyingSpaceMapUniversal U)) = _
    rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp,
      ← classifyingSpaceMapUniversal_comp]
    rfl

/-- Any categorical adjunction gives a homotopy equivalence in arbitrary universes. -/
def adjunctionClassifyingHomotopyEquivUniversal {F : C ⥤ D} {G : D ⥤ C}
    (a : F ⊣ G) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) where
  toFun := classifyingSpaceMapUniversal F
  invFun := classifyingSpaceMapUniversal G
  left_inv := ⟨(classifyingSpaceUniversalHomotopy a.unit).symm.cast
    (classifyingSpaceMapUniversal_comp F G) classifyingSpaceMapUniversal_id⟩
  right_inv := ⟨(classifyingSpaceUniversalHomotopy a.counit).cast
    (classifyingSpaceMapUniversal_comp G F) classifyingSpaceMapUniversal_id⟩

/-- An equivalence of categories preserves the original classifying spaces in any universes. -/
def equivalenceClassifyingHomotopyEquivUniversal (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) :=
  adjunctionClassifyingHomotopyEquivUniversal e.toAdjunction

@[simp] theorem adjunctionClassifyingHomotopyEquivUniversal_toFun
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) :
    (adjunctionClassifyingHomotopyEquivUniversal a).toFun =
      classifyingSpaceMapUniversal F := rfl

@[simp] theorem equivalenceClassifyingHomotopyEquivUniversal_toFun (e : C ≌ D) :
    (equivalenceClassifyingHomotopyEquivUniversal e).toFun =
      classifyingSpaceMapUniversal e.functor := rfl

/-- Universe lifting preserves the full parametrized component-edge track. -/
theorem classifyingSpaceUniversalHomotopy_vertex_track
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceUniversalHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t := by
  change classifyingSpaceMapUniversal (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D)
    (classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C)
        (Functor.whiskerRight α AsSmall.up))
      (t, classifyingSpaceMapUniversal AsSmall.up (classifyingSpacePoint c))) = _
  rw [classifyingSpaceMapUniversal_point,
    classifyingSpaceNaturalTransformationHomotopy_vertex,
    classifyingSpaceMapUniversal_path]
  rfl

end CategoryTheory
