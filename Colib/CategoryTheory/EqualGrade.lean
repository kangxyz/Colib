/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Adjunction
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # Actual categorical contraction for equality-of-grade weak maps

For a category with actual zero morphisms and a surjective object grading,
the category of all grade-preserving arrows has the actual homotopy type of
the discrete grading set. The homotopies use zero natural transformations;
no chosen contraction or higher filling hypothesis is present. This will
apply to actual graded S-construction rows once their grade realizability
and simplicial compatibility have been established.

Implementation provenance: `Quillen/CategoryTheory/EqualGrade.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits
universe u
namespace CategoryTheory.EqualGrade
variable {C B : Type u} [SmallCategory C] [HasZeroMorphisms C] (g : C → B)

/-- All original arrows whose endpoints have equal grade. -/
def weak : MorphismProperty C := fun X Y _ ↦ g X = g Y

instance weak_multiplicative : (weak g).IsMultiplicative where
  id_mem _ := rfl
  comp_mem _ _ hf hg := hf.trans hg

/-- The literal grading functor on original grade-preserving arrows. -/
def projection : WideSubcategory (weak g) ⥤ Discrete B where
  obj X := .mk (g X.obj)
  map f := eqToHom (congrArg Discrete.mk f.property)

variable (h : Function.Surjective g)

/-- Choose representatives only at the discrete grading set. -/
def sectionFunctor : Discrete B ⥤ WideSubcategory (weak g) :=
  Discrete.functor (fun b ↦ ⟨(h b).choose⟩)

/-- Every original object maps to the representative of its own grade by the
actual zero arrow; these components commute with every original arrow. -/
def identityToSection : 𝟭 (WideSubcategory (weak g)) ⟶ projection g ⋙ sectionFunctor g h where
  app X := ⟨0, (h (g X.obj)).choose_spec.symm⟩
  naturality X Y f := by
    apply WideSubcategory.hom_ext
    change f.hom ≫ 0 = 0 ≫ _
    simp

/-- On the discrete grading target the representative projection is naturally the identity. -/
def sectionToIdentity : sectionFunctor g h ⋙ projection g ⟶ 𝟭 (Discrete B) where
  app b := eqToHom (congrArg Discrete.mk (h b.as).choose_spec)
  naturality _ _ _ := Subsingleton.elim _ _

/-- Actual homotopy equivalence onto the discrete grade space, with the original
projection map forward and no contractibility assumption. -/
def projectionHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (WideSubcategory (weak g)))
      (ClassifyingSpace (Discrete B)) where
  toFun := (classifyingSpaceMap (projection g)).hom
  invFun := (classifyingSpaceMap (sectionFunctor g h)).hom
  left_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id, TopCat.hom_comp]
      using (classifyingSpaceNaturalTransformationHomotopy (identityToSection g h)).symm⟩
  right_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id, TopCat.hom_comp]
      using classifyingSpaceNaturalTransformationHomotopy (sectionToIdentity g h)⟩

/-- The forward equivalence is literally the original grade functor's realization. -/
@[simp] theorem projectionHomotopyEquiv_toFun :
    (projectionHomotopyEquiv g h).toFun = (classifyingSpaceMap (projection g)).hom := rfl

variable (P : MorphismProperty C) [P.IsMultiplicative]
  (hP : ∀ {X Y : C} (f : X ⟶ Y), P f ↔ g X = g Y)

/-- Identifying the actual weak predicate with equal grades changes no object or arrow. -/
def equivalenceOfIff : WideSubcategory P ≌ WideSubcategory (weak g) where
  functor := {
    obj X := ⟨X.obj⟩
    map f := ⟨f.hom, (hP f.hom).mp f.property⟩ }
  inverse := {
    obj X := ⟨X.obj⟩
    map f := ⟨f.hom, (hP f.hom).mpr f.property⟩ }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    apply WideSubcategory.hom_ext
    simp)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intros
    apply WideSubcategory.hom_ext
    simp)

/-- The original grading on the actually given weak category. -/
def projectionOfIff : WideSubcategory P ⥤ Discrete B :=
  (equivalenceOfIff g P hP).functor ⋙ projection g

/-- An actual weak class identified with equal grades has the same explicit homotopy type. -/
def projectionOfIffHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (WideSubcategory P))
      (ClassifyingSpace (Discrete B)) :=
  (equivalenceClassifyingHomotopyEquiv (equivalenceOfIff g P hP)).trans
    (projectionHomotopyEquiv g h)

/-- The comparison retains the original grading functor's actual realization. -/
@[simp] theorem projectionOfIffHomotopyEquiv_toFun :
    (projectionOfIffHomotopyEquiv g h P hP).toFun =
      (classifyingSpaceMap (projectionOfIff g P hP)).hom := by
  change (classifyingSpaceMap (projection g)).hom.comp
    (classifyingSpaceMap (equivalenceOfIff g P hP).functor).hom = _
  exact congrArg TopCat.Hom.hom (classifyingSpaceMap_comp _ _).symm

end CategoryTheory.EqualGrade
