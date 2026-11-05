/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Exact functors and cycles in actual projective resolutions

The target resolution is supplied, and need not be the image of a projective
resolution. An exact functor need not preserve projective objects. The comparison
uses an actual augmented cochain map from the target resolution to the mapped
source resolution. Both derived localization comparisons and shift comparisons
are retained.

The proof is the projective counterpart of
`Aglib.CategoryTheory.Abelian.Injective.ExactFunctor` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex Abelian

universe u₁ v₁ u₂ v₂ w₁ w₂

namespace CategoryTheory.ProjectiveResolution.ExactFunctor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {A : C} {B : D} (R : ProjectiveResolution A) (S : ProjectiveResolution B)

/-- The actual shifted cochain map associated to a resolution cocycle. -/
def cycleHom {T : C} {n : ℕ} (f : R.complex.X n ⟶ T)
    (hf : R.complex.d (n + 1) n ≫ f = 0) :
    ShiftedHom R.cochainComplex ((CochainComplex.singleFunctor C 0).obj T) (n : ℤ) :=
  Cocycle.equivHomShift.symm
    (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-(n + 1)) (by lia) (by
        rw [R.cochainComplex_d _ _ (n + 1) n (by simp) rfl]
        simp [hf]))

/-- The canonical derived roof defining `extMk`, with no change of Ext model. -/
theorem extMk_hom_formula [HasExt.{w₁} C] [HasDerivedCategory C] {T : C} {n : ℕ}
    (f : R.complex.X n ⟶ T) (hf : R.complex.d (n + 1) n ≫ f = 0) :
    (R.extMk f (n + 1) rfl hf).hom =
      inv (DerivedCategory.Q.map R.π') ≫ (cycleHom R f hf).map DerivedCategory.Q := by
  rw [R.extMk_hom]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 _ ≫ inv (DerivedCategory.Q.map R.π'))).comp
    (((cycleHom R f hf).map DerivedCategory.Q).comp
      (ShiftedHom.mk₀ 0 rfl (𝟙 _)) (zero_add _)) (add_zero _) = _
  simp only [Category.id_comp, ShiftedHom.comp_mk₀_id, ShiftedHom.mk₀_comp]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The shifted cycle comparison is determined by the actual degree `-n` component.
The equation compares the native resolution coordinates, not chosen Ext representatives. -/
theorem cycleHom_map_of_component
    (φ : S.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex)
    {T : C} {n : ℕ} (f : R.complex.X n ⟶ T)
    (hf : R.complex.d (n + 1) n ≫ f = 0)
    (g : S.complex.X n ⟶ F.obj T) (hg : S.complex.d (n + 1) n ≫ g = 0)
    (hcomp : (S.cochainComplexXIso (-n) n rfl).hom ≫ g =
      φ.f (-n) ≫ F.map ((R.cochainComplexXIso (-n) n rfl).hom ≫ f)) :
    cycleHom S g hg = φ ≫
      (cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ)) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app T)⟦(n : ℤ)⟧' := by
  apply Cocycle.equivHomShift.injective
  apply Subtype.ext
  apply (Cochain.toSingleEquiv (show -(n : ℤ) + n = 0 by simp)).injective
  simp only [neg_add_cancel, Cochain.toSingleEquiv, Cochain.toSingleMk, Cochain.single, XIsoOfEq,
    eqToIso.inv, eqToIso.hom, Category.assoc, cycleHom, Cocycle.equivHomShift_symm_apply,
    Cocycle.equivHomShift_apply,
    Cocycle.ofHom_homOf_eq_self, Cocycle.rightUnshift_coe, Cochain.rightUnshift,
    shiftFunctor_obj_X', Cocycle.rightShift_coe, Cochain.rightShift,
    Cocycle.toSingleMk_coe, Cochain.mk_v, shiftFunctor_obj_X,
    shiftFunctorObjXIso, eqToHom_trans, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    and_self, ↓reduceDIte, eqToHom_refl, Category.id_comp, Category.comp_id,
    Functor.comp_obj, Functor.mapCochainComplexSingleFunctor,
    ShiftedHom.map, Cocycle.ofHom_coe, Cochain.ofHom, Cochain.ofHoms]
  have hsingle : F.map (singleObjXSelf (.up ℤ) 0 T).inv ≫
      F.map (singleObjXSelf (.up ℤ) 0 T).hom = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  simpa [Cochain.rightShift, Cochain.toSingleMk, Cochain.single, Cochain.mk_v,
    shiftFunctorObjXIso, XIsoOfEq, eqToHom_map, eqToHom_trans, Functor.map_comp, Category.assoc,
    reassoc_of% hsingle,
    singleMapHomologicalComplex_hom_app_self] using hcomp

/-- Naturality of the derived localization comparison on the original shifted cycle. -/
theorem derived_cycle_map [HasDerivedCategory C] [HasDerivedCategory D]
    {T : C} {n : ℕ} (f : R.complex.X n ⟶ T)
    (hf : R.complex.d (n + 1) n ≫ f = 0) :
    ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app T)⟦(n : ℤ)⟧' =
      F.mapDerivedCategoryFactors.hom.app R.cochainComplex ≫
        ((cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q ≫
          (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app T))⟦(n : ℤ)⟧' := by
  have hh := ShiftedHom.map_naturality (cycleHom R f hf) F.mapDerivedCategoryFactors.hom
  simp only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hh
  have hs : (F.mapDerivedCategorySingleFunctor 0).hom.app T =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj T) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app T) := by
    apply (cancel_epi (F.mapDerivedCategoryFactors.inv.app
      ((CochainComplex.singleFunctor C 0).obj T))).mp
    rw [Iso.inv_hom_id_app_assoc]
    exact F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app T
  rw [hs, Functor.map_comp, ← Category.assoc, hh, Category.assoc]

/-- The actual augmentation triangle after derived localization. -/
theorem derived_augmentation [HasDerivedCategory C] [HasDerivedCategory D]
    (a : B ⟶ F.obj A)
    (φ : S.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex)
    (hφ : φ ≫ (F.mapHomologicalComplex (.up ℤ)).map R.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app A =
        S.π' ≫ (CochainComplex.singleFunctor D 0).map a) :
    DerivedCategory.Q.map S.π' ≫ (DerivedCategory.singleFunctor D 0).map a ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app A ≫
        F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) ≫
          F.mapDerivedCategoryFactors.hom.app R.cochainComplex =
      DerivedCategory.Q.map φ := by
  apply (cancel_mono (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map R.π'))).mp
  simp only [Category.assoc]
  rw [← F.mapDerivedCategoryFactors_hom_naturality]
  rw [← Functor.map_comp_assoc, IsIso.inv_hom_id, Functor.map_id, Category.id_comp]
  erw [F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  apply (cancel_mono (DerivedCategory.Q.map
    ((F.mapCochainComplexSingleFunctor 0).hom.app A))).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [hφ]
  change DerivedCategory.Q.map S.π' ≫
    DerivedCategory.Q.map ((CochainComplex.singleFunctor D 0).map a) ≫
    DerivedCategory.Q.map (𝟙 _) = _
  simp only [Functor.map_id, Category.comp_id, Functor.map_comp]

/-- A compatible map between the actual cochain resolutions computes the original
exact-functor Ext map, including arbitrary source precomposition. -/
theorem mk₀_comp_extMk_mapExactFunctor_of_cycleHom
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    (a : B ⟶ F.obj A)
    (φ : S.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex)
    (hφ : φ ≫ (F.mapHomologicalComplex (.up ℤ)).map R.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app A =
        S.π' ≫ (CochainComplex.singleFunctor D 0).map a)
    {T : C} {n : ℕ} (f : R.complex.X n ⟶ T)
    (hf : R.complex.d (n + 1) n ≫ f = 0)
    (g : S.complex.X n ⟶ F.obj T) (hg : S.complex.d (n + 1) n ≫ g = 0)
    (hcycle : cycleHom S g hg = φ ≫
      (cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ)) ≫
        ((F.mapCochainComplexSingleFunctor 0).hom.app T)⟦(n : ℤ)⟧') :
    (Ext.mk₀ a).comp ((R.extMk f (n + 1) rfl hf).mapExactFunctor F) (zero_add n) =
      (S.extMk g (n + 1) rfl hg : Ext.{w₂} B (F.obj T) n) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  have hRmap : (R.extMk f (n + 1) rfl hf : Ext.{w₁} A T n).hom.map F.mapDerivedCategory =
      F.mapDerivedCategory.map (inv (DerivedCategory.Q.map R.π')) ≫
        ((cycleHom R f hf).map DerivedCategory.Q).map F.mapDerivedCategory := by
    rw [extMk_hom_formula R]
    rw [← ShiftedHom.mk₀_comp 0 rfl, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
      ShiftedHom.mk₀_comp]
  apply Ext.ext
  rw [Ext.comp_hom, Ext.mk₀_hom, Ext.mapExactFunctor_hom, ShiftedHom.mk₀_comp,
    hRmap, extMk_hom_formula S]
  apply (cancel_epi (DerivedCategory.Q.map S.π')).mp
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [derived_cycle_map F R f hf]
  rw [reassoc_of% derived_augmentation F R S a φ hφ]
  have hcycle' : cycleHom S g hg =
      (ShiftedHom.mk₀ 0 rfl φ).comp
        (((cycleHom R f hf).map (F.mapHomologicalComplex (.up ℤ))).comp
          (ShiftedHom.mk₀ 0 rfl ((F.mapCochainComplexSingleFunctor 0).hom.app T))
          (zero_add _)) (add_zero _) := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] using hcycle
  rw [hcycle', ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]


/-- Exact functoriality of native projective-resolution cocycles, for any supplied
augmentation-compatible cochain comparison and its literal degree component. -/
theorem mk₀_comp_extMk_mapExactFunctor
    [HasExt.{w₁} C] [HasExt.{w₂} D]
    (a : B ⟶ F.obj A)
    (φ : S.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex)
    (hφ : φ ≫ (F.mapHomologicalComplex (.up ℤ)).map R.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app A =
        S.π' ≫ (CochainComplex.singleFunctor D 0).map a)
    {T : C} {n : ℕ} (f : R.complex.X n ⟶ T)
    (hf : R.complex.d (n + 1) n ≫ f = 0)
    (g : S.complex.X n ⟶ F.obj T) (hg : S.complex.d (n + 1) n ≫ g = 0)
    (hcomp : (S.cochainComplexXIso (-n) n rfl).hom ≫ g =
      φ.f (-n) ≫ F.map ((R.cochainComplexXIso (-n) n rfl).hom ≫ f)) :
    (Ext.mk₀ a).comp ((R.extMk f (n + 1) rfl hf).mapExactFunctor F) (zero_add n) =
      (S.extMk g (n + 1) rfl hg : Ext.{w₂} B (F.obj T) n) :=
  mk₀_comp_extMk_mapExactFunctor_of_cycleHom F R S a φ hφ f hf g hg
    (cycleHom_map_of_component F R S φ f hf g hg hcomp)

end CategoryTheory.ProjectiveResolution.ExactFunctor

attribute [colib_tag "COL-0164",
  colib_ref "mathlib_koszul_pin"
    "CategoryTheory/Abelian/Projective/Ext.lean; extMk_hom"
    "background" "Ingredient: the original projective-resolution derived Ext roof",
  colib_ref "mathlib_koszul_pin"
    "Algebra/Homology/DerivedCategory/Ext/Map.lean; mapExactFunctor_hom"
    "background" "Ingredient: the actual exact-functor map on derived Ext"]
  CategoryTheory.ProjectiveResolution.ExactFunctor.mk₀_comp_extMk_mapExactFunctor
