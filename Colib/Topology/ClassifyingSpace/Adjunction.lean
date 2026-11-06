/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.HomotopyBridge
public import Colib.Topology.ClassifyingSpace.Map
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Adjunctions and classifying-space homotopy equivalences

The unit and counit of an adjunction give explicit simplicial homotopies.
The proved realization cylinder bridge turns them into genuine continuous
homotopies and hence a homotopy equivalence of actual classifying spaces.
Equivalences of categories are a special case. Initial and terminal objects
give explicit contractions of the classifying space.

This is an adjunction special case of the behavior underlying Quillen's
Theorem A, not a proof of the general comma-category criterion.
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial Topology unitInterval

universe u v

namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- The unit of an adjunction gives the nerve homotopy from the identity
to the composite of the induced forward and backward maps. -/
def adjunctionUnitNerveHomotopy (a : F ⊣ G) :
    SSet.Homotopy (𝟙 (nerve C)) (nerveMap F ≫ nerveMap G) :=
  naturalTransformationNerveHomotopy a.unit

/-- The counit gives the nerve homotopy from the other composite to the
identity. No invertibility of the unit or counit is needed. -/
def adjunctionCounitNerveHomotopy (a : F ⊣ G) :
    SSet.Homotopy (nerveMap G ≫ nerveMap F) (𝟙 (nerve D)) :=
  naturalTransformationNerveHomotopy a.counit

/-- The equivalence-of-categories unit supplies the corresponding simplicial
homotopy of actual nerve maps. -/
def equivalenceUnitNerveHomotopy (e : C ≌ D) :
    SSet.Homotopy (𝟙 (nerve C)) (nerveMap e.functor ≫ nerveMap e.inverse) :=
  adjunctionUnitNerveHomotopy e.toAdjunction

/-- The equivalence-of-categories counit supplies the other simplicial
homotopy of actual nerve maps. -/
def equivalenceCounitNerveHomotopy (e : C ≌ D) :
    SSet.Homotopy (nerveMap e.inverse ≫ nerveMap e.functor) (𝟙 (nerve D)) :=
  adjunctionCounitNerveHomotopy e.toAdjunction

/-- The realized unit homotopy runs from the identity to the composite
of the classifying maps of the two adjoint functors. -/
def adjunctionUnitClassifyingHomotopy (a : F ⊣ G) :
    (ContinuousMap.id (ClassifyingSpace C)).Homotopy
      ((classifyingSpaceMap G).hom.comp (classifyingSpaceMap F).hom) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using classifyingSpaceNaturalTransformationHomotopy a.unit

/-- The realized counit homotopy runs from the other composite to the identity. -/
def adjunctionCounitClassifyingHomotopy (a : F ⊣ G) :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap G).hom).Homotopy
      (ContinuousMap.id (ClassifyingSpace D)) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using classifyingSpaceNaturalTransformationHomotopy a.counit

/-- Any genuine categorical adjunction induces a homotopy equivalence of
actual classifying spaces, with the two functors as its continuous maps. -/
def adjunctionClassifyingHomotopyEquiv (a : F ⊣ G) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) where
  toFun := (classifyingSpaceMap F).hom
  invFun := (classifyingSpaceMap G).hom
  left_inv := ⟨(adjunctionUnitClassifyingHomotopy a).symm⟩
  right_inv := ⟨adjunctionCounitClassifyingHomotopy a⟩

@[simp]
theorem adjunctionClassifyingHomotopyEquiv_apply (a : F ⊣ G)
    (x : ClassifyingSpace C) :
    adjunctionClassifyingHomotopyEquiv a x = classifyingSpaceMap F x := rfl

@[simp]
theorem adjunctionClassifyingHomotopyEquiv_symm_apply (a : F ⊣ G)
    (y : ClassifyingSpace D) :
    (adjunctionClassifyingHomotopyEquiv a).symm y = classifyingSpaceMap G y := rfl

/-- An equivalence of categories induces a homotopy equivalence of their
geometric realizations. -/
def equivalenceClassifyingHomotopyEquiv (e : C ≌ D) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) :=
  adjunctionClassifyingHomotopyEquiv e.toAdjunction

@[simp]
theorem equivalenceClassifyingHomotopyEquiv_apply (e : C ≌ D)
    (x : ClassifyingSpace C) :
    equivalenceClassifyingHomotopyEquiv e x = classifyingSpaceMap e.functor x := rfl

@[simp]
theorem equivalenceClassifyingHomotopyEquiv_symm_apply (e : C ≌ D)
    (y : ClassifyingSpace D) :
    (equivalenceClassifyingHomotopyEquiv e).symm y = classifyingSpaceMap e.inverse y := rfl

/-- The same construction for a functor carrying an `IsEquivalence` instance. -/
def classifyingHomotopyEquivOfIsEquivalence (F : C ⥤ D) [F.IsEquivalence] :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) :=
  equivalenceClassifyingHomotopyEquiv F.asEquivalence

end CategoryTheory

attribute [colib_tag "COL-0231",
  colib_ref "WeibelKBook" "IV, 3.2, pages 25-26" "clause"
    "Adjunctions and actual classifying spaces"]
  CategoryTheory.adjunctionClassifyingHomotopyEquiv
  CategoryTheory.classifyingHomotopyEquivOfIsEquivalence
