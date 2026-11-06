/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EqToHom

/-! # Equality of functors into a full subcategory

Adapted from Quillen/Aglib/CategoryTheory/Functor/FullSubcategoryExt.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The direct equality theorem uses
independent object and morphism universes, with the native full-subcategory inclusion.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.Functor

/-- Equality after the full-subcategory inclusion reflects equality of functors. -/
theorem ext_of_comp_fullSubcategory
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {P : ObjectProperty D} {F G : C ⥤ P.FullSubcategory}
    (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  refine Functor.ext (fun X => ObjectProperty.FullSubcategory.ext (Functor.congr_obj h X)) ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  simpa only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom] using Functor.congr_hom h f

end CategoryTheory.Functor
