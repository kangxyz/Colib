/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/CoproductFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original coproduct comparisons as coherent monoidal structure

The canonical initial and binary-coproduct comparison maps make every functor
lax monoidal for the chosen coproduct structures. Preservation of finite
coproducts makes these actual comparison maps invertible. All coherence is
proved with the original universal properties.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
universe u v u' v'
namespace CategoryTheory.CoproductMonoidal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [HasInitial C] [HasBinaryCoproducts C]
  {D : Type u'} [Category.{v'} D] [HasInitial D] [HasBinaryCoproducts D]
attribute [local instance] monoidalOfHasFiniteCoproducts symmetricOfHasFiniteCoproducts

/-- The original initial and coproduct comparison maps, with their canonical coherence. -/
@[instance_reducible]
def laxMonoidal (F : C ⥤ D) : F.LaxMonoidal where
  ε := initialComparison F
  μ X Y := coprodComparison F X Y
  μ_natural_left f X := by
    change coprod.map (F.map f) (𝟙 _) ≫ coprodComparison F _ _ =
      coprodComparison F _ _ ≫ F.map (coprod.map f (𝟙 X))
    simpa only [F.map_id] using (coprodComparison_natural F f (𝟙 X)).symm
  μ_natural_right X f := by
    change coprod.map (𝟙 _) (F.map f) ≫ coprodComparison F _ _ =
      coprodComparison F _ _ ≫ F.map (coprod.map (𝟙 X) f)
    simpa only [F.map_id] using (coprodComparison_natural F (𝟙 X) f).symm
  associativity X Y Z := by
    change coprod.map (coprodComparison F X Y) (𝟙 _) ≫ coprodComparison F (X ⨿ Y) Z ≫
        F.map (coprod.associator X Y Z).hom =
      (coprod.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
        coprod.map (𝟙 _) (coprodComparison F Y Z) ≫ coprodComparison F X (Y ⨿ Z)
    apply coprod.hom_ext
    · apply coprod.hom_ext <;>
        simp only [coprod.associator_hom, Category.assoc, coprod.inl_map_assoc,
          coprod.inr_map_assoc, inl_coprodComparison_assoc, inr_coprodComparison_assoc,
          coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.id_comp,
          ← F.map_comp, coprod.inl_desc, coprod.inr_desc,
          inl_coprodComparison, inr_coprodComparison]
    · simp only [coprod.associator_hom, Category.assoc, coprod.inr_map_assoc,
        inr_coprodComparison_assoc, coprod.inr_desc_assoc, Category.id_comp,
        ← F.map_comp, coprod.inr_desc, inr_coprodComparison]
  left_unitality X := by
    change (coprod.leftUnitor (F.obj X)).hom =
      coprod.map (initialComparison F) (𝟙 _) ≫ coprodComparison F (⊥_ C) X ≫
        F.map (coprod.leftUnitor X).hom
    apply coprod.hom_ext
    · apply Subsingleton.elim
    · simp [coprod.leftUnitor, ← F.map_comp]
  right_unitality X := by
    change (coprod.rightUnitor (F.obj X)).hom =
      coprod.map (𝟙 _) (initialComparison F) ≫ coprodComparison F X (⊥_ C) ≫
        F.map (coprod.rightUnitor X).hom
    apply coprod.hom_ext
    · simp [coprod.rightUnitor, ← F.map_comp]
    · apply Subsingleton.elim

attribute [local instance] laxMonoidal

/-- Preserving finite coproducts upgrades the original comparison maps to strong monoidal data. -/
@[instance_reducible]
def monoidal (F : C ⥤ D) [PreservesFiniteCoproducts F] : F.Monoidal := by
  letI : IsIso (Functor.LaxMonoidal.ε F) :=
    inferInstanceAs (IsIso (initialComparison F))
  letI (X Y : C) : IsIso (Functor.LaxMonoidal.μ F X Y) :=
    inferInstanceAs (IsIso (coprodComparison F X Y))
  exact Functor.Monoidal.ofLaxMonoidal F

/-- The original coproduct braiding is respected by the canonical comparisons. -/
@[instance_reducible]
def laxBraided (F : C ⥤ D) : F.LaxBraided where
  braided X Y := by
    change coprodComparison F X Y ≫ F.map (coprod.braiding X Y).hom =
      (coprod.braiding (F.obj X) (F.obj Y)).hom ≫ coprodComparison F Y X
    apply coprod.hom_ext <;> simp [coprod.braiding, ← F.map_comp]

/-- Every original natural transformation respects the canonical coproduct comparisons. -/
lemma natTrans_isMonoidal {F G : C ⥤ D} (α : F ⟶ G) : α.IsMonoidal where
  unit := by
    change initialComparison F ≫ α.app (⊥_ C) = initialComparison G
    apply Subsingleton.elim
  tensor X Y := by
    change coprodComparison F X Y ≫ α.app (X ⨿ Y) =
      coprod.map (α.app X) (α.app Y) ≫ coprodComparison G X Y
    apply coprod.hom_ext <;> simp

end CategoryTheory.CoproductMonoidal
