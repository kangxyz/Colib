/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Algebra.Homology.DerivedCategory.SingleCocycle
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Degree-one resolution cocycles and connecting classes

A lift of the augmentation through a short exact sequence gives a cocycle
representing the negative of its standard extension class. The sign follows
from the native cone triangle and the actual projective-resolution Ext API.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CochainComplex CochainComplex.HomComplex

universe w

namespace CategoryTheory.ProjectiveResolution

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C} (P : ProjectiveResolution S.X₃) (hS : S.ShortExact)
  (b : P.complex.X 0 ⟶ S.X₂) (c : P.complex.X 1 ⟶ S.X₁)
  (hc : P.complex.d 2 1 ≫ c = 0)
  (h : c ≫ S.f = P.complex.d 1 0 ≫ b)
  (hb : b ≫ S.g = P.π.f 0)

include h hb in
/-- The degree-one cocycle from an augmentation lift represents the negative extension class. -/
theorem extMk_eq_neg_extClass : P.extMk c 2 rfl hc = -hS.extClass := by
  let := HasDerivedCategory.standard C
  let b' := (P.cochainComplexXIso 0 0 rfl).hom ≫ b
  let c' := (P.cochainComplexXIso (-1) 1 rfl).hom ≫ c
  have hc' : P.cochainComplex.d (-2) (-1) ≫ c' = 0 := by
    dsimp only [c']
    rw [P.cochainComplex_d (-2) (-1) 2 1 rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hc, Limits.comp_zero]
  have h' : c' ≫ S.f = P.cochainComplex.d (-1) 0 ≫ b' := by
    dsimp only [b', c']
    rw [P.cochainComplex_d (-1) 0 1 0 rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, h]
  have hb' : P.π'.f 0 = b' ≫ S.g ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv := by
    rw [P.π'_f_zero]
    dsimp only [b']
    erw [← hb, Category.assoc, Category.assoc]
    rfl
  have hδ := hS.map_comp_singleδ_eq_neg_cocycle b' c' hc' h' P.π' hb'
  ext
  rw [P.extMk_hom, Ext.neg_hom, hS.extClass_hom]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Iso.refl_inv, ShiftedHom.mk₀_comp]
  erw [ShiftedHom.comp_mk₀_id]
  change inv (DerivedCategory.Q.map P.π') ≫
    (DerivedCategory.Q.map (Cocycle.equivHomShift.symm
      (Cocycle.toSingleMk c' (show (-1 : ℤ) + 1 = 0 by decide) (-2) (by decide) hc')) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((singleFunctor C 0).obj S.X₁)) =
    -hS.singleδ
  apply (cancel_epi (DerivedCategory.Q.map P.π')).1
  rw [IsIso.hom_inv_id_assoc, Preadditive.comp_neg, hδ, neg_neg]

end CategoryTheory.ProjectiveResolution

attribute [colib_tag "COL-0126"] CategoryTheory.ProjectiveResolution.extMk_eq_neg_extClass

attribute [stacks 06XP
  "Ingredient: Yoneda extension classes; the explicit native cone-sign comparison is proved here"]
  CategoryTheory.ProjectiveResolution.extMk_eq_neg_extClass
