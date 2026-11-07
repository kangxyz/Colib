/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived
public import Colib.CategoryTheory.Abelian.RightDerived.CochainNaturality

/-!
# Coefficient naturality and resolution independence of the normalized Ext comparison

The existing additive equivalence intertwines original Yoneda postcomposition with the
actual coefficient map of the right-derived additive Hom functor. Consequently it is
independent of the supplied injective resolution. The comparison itself is unchanged.

The statements are adapted from `Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived`
at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f`. The proof works on native `extMk`
representatives and their actual cycle projections. It does not copy the source's private
Hom-complex map, cocycle map, cohomology-class map, or homology-data construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex

universe u v w

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

private theorem extMk_cochain_closed (f : X ⟶ I.cocomplex.X n)
    (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫
      I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0 := by
  rw [I.cochainComplex_d (n : ℤ) ((n : ℤ) + 1) n (n + 1) rfl (by omega)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, zero_comp] using
    congrArg (fun k => k ≫
      (I.cochainComplexXIso ((n : ℤ) + 1) (n + 1) (by omega)).inv) hf

variable [EnoughInjectives C] [HasExt.{w} C]

private theorem extRightDerivedAddEquiv_extMk_homology
    (f : X ⟶ I.cocomplex.X n) (hf : f ≫ I.cocomplex.d n (n + 1) = 0) :
    I.extRightDerivedAddEquiv X n (I.extMk f (n + 1) rfl hf) =
      let H := coyonedaComplex X I.cochainComplex
      (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
        (H.homologyπ (n : ℤ) ((H.sc (n : ℤ)).abCyclesIso.inv
          ⟨f ≫ (I.cochainComplexXIso n n rfl).inv, by
            change (f ≫ (I.cochainComplexXIso n n rfl).inv) ≫
              I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
            rw [CochainComplex.next ℤ (n : ℤ)]
            exact I.extMk_cochain_closed X n f hf⟩)) := by
  simpa only [extMk, Nat.cast_add, Nat.cast_one] using I.extRightDerivedAddEquiv_cocycle X n
    (f ≫ (I.cochainComplexXIso n n rfl).inv) (I.extMk_cochain_closed X n f hf)

/-- The comparison retains every original coefficient map and any supplied resolution lift. -/
theorem extRightDerivedAddEquiv_naturality_right
    {Y' : C} {J : InjectiveResolution Y'} {g : Y ⟶ Y'}
    (φ : Hom I J g) (x : Abelian.Ext.{w} X Y n) :
    J.extRightDerivedAddEquiv X n (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g
        (I.extRightDerivedAddEquiv X n x) := by
  obtain ⟨a, ha, rfl⟩ := I.extMk_surjective x (n + 1) rfl
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let H₀ := coyonedaComplex X I.cochainComplex
  let H₁ := coyonedaComplex X J.cochainComplex
  let ψ := (F.mapHomologicalComplex (.up ℤ)).map φ.hom'
  have ha' : (a ≫ φ.hom.f n) ≫ J.cocomplex.d n (n + 1) = 0 := by
    simp [reassoc_of% ha]
  let z₀ : H₀.cycles (n : ℤ) := (H₀.sc (n : ℤ)).abCyclesIso.inv
    ⟨a ≫ (I.cochainComplexXIso n n rfl).inv, by
      change (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫
        I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
      rw [CochainComplex.next ℤ (n : ℤ)]
      exact I.extMk_cochain_closed X n a ha⟩
  let z₁ : H₁.cycles (n : ℤ) := (H₁.sc (n : ℤ)).abCyclesIso.inv
    ⟨(a ≫ φ.hom.f n) ≫ (J.cochainComplexXIso n n rfl).inv, by
      change ((a ≫ φ.hom.f n) ≫ (J.cochainComplexXIso n n rfl).inv) ≫
        J.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
      rw [CochainComplex.next ℤ (n : ℤ)]
      exact J.extMk_cochain_closed X n (a ≫ φ.hom.f n) ha'⟩
  have hi₀ : H₀.iCycles (n : ℤ) z₀ = a ≫ (I.cochainComplexXIso n n rfl).inv := by
    dsimp only [z₀]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  have hi₁ : H₁.iCycles (n : ℤ) z₁ =
      (a ≫ φ.hom.f n) ≫ (J.cochainComplexXIso n n rfl).inv := by
    dsimp only [z₁]
    erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  have hc : cyclesMap ψ (n : ℤ) z₀ = z₁ := by
    apply (AddCommGrpCat.mono_iff_injective (H₁.iCycles (n : ℤ))).mp inferInstance
    rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply, hi₀, hi₁]
    change (a ≫ (I.cochainComplexXIso n n rfl).inv) ≫ φ.hom'.f (n : ℤ) =
      (a ≫ φ.hom.f n) ≫ (J.cochainComplexXIso n n rfl).inv
    simp [φ.hom'_f n n rfl, Category.assoc]
  have hH : homologyMap ψ (n : ℤ) (H₀.homologyπ (n : ℤ) z₀) =
      H₁.homologyπ (n : ℤ) z₁ := by
    rw [← ConcreteCategory.comp_apply, homologyπ_naturality,
      ConcreteCategory.comp_apply, hc]
  rw [extMk_comp_mk₀ _ _ _ _ φ, extRightDerivedAddEquiv_extMk_homology,
    extRightDerivedAddEquiv_extMk_homology]
  change (J.isoRightDerivedObjCochain F n).inv (H₁.homologyπ (n : ℤ) z₁) =
    (F.rightDerived n).map g
      ((I.isoRightDerivedObjCochain F n).inv (H₀.homologyπ (n : ℤ) z₀))
  rw [← hH]
  exact ConcreteCategory.congr_hom
    (isoRightDerivedObjCochain_inv_naturality F φ n) (H₀.homologyπ (n : ℤ) z₀)

/-- The unchanged additive equivalence is independent of the supplied injective resolution. -/
theorem extRightDerivedAddEquiv_eq (J : InjectiveResolution Y) :
    I.extRightDerivedAddEquiv X n = J.extRightDerivedAddEquiv X n := by
  let φ : Hom I J (𝟙 Y) :=
    ⟨desc (𝟙 Y) J I, by
      simpa only [CochainComplex.single₀_map_f_zero] using desc_commutes_zero (𝟙 Y) J I⟩
  ext x
  have h := I.extRightDerivedAddEquiv_naturality_right X n φ x
  rw [Abelian.Ext.comp_mk₀_id, Functor.map_id] at h
  exact h.symm

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] (X : C) (n : ℕ) {H : C ⥤ AddCommGrpCat.{v}}
  (e : (preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n ≅ H)

/-- Composing with a specified natural isomorphism preserves the actual coefficient map. -/
theorem extRightDerivedAddEquiv_trans_naturality
    {Y Y' : C} {I : InjectiveResolution Y} {J : InjectiveResolution Y'}
    {g : Y ⟶ Y'} (φ : Hom I J g) (x : Abelian.Ext.{w} X Y n) :
    ((J.extRightDerivedAddEquiv X n).trans
      (e.app Y').addCommGroupIsoToAddEquiv) (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
    H.map g (((I.extRightDerivedAddEquiv X n).trans
      (e.app Y).addCommGroupIsoToAddEquiv) x) := by
  change e.hom.app Y' (J.extRightDerivedAddEquiv X n
    (x.comp (Abelian.Ext.mk₀ g) (add_zero _))) =
      H.map g (e.hom.app Y (I.extRightDerivedAddEquiv X n x))
  rw [I.extRightDerivedAddEquiv_naturality_right X n φ x]
  exact ConcreteCategory.congr_hom (e.hom.naturality g)
    (I.extRightDerivedAddEquiv X n x)

/-- The composed comparison is independent of the supplied injective resolution. -/
theorem extRightDerivedAddEquiv_trans_eq
    {Y : C} (I J : InjectiveResolution Y) :
    (I.extRightDerivedAddEquiv X n).trans (e.app Y).addCommGroupIsoToAddEquiv =
      (J.extRightDerivedAddEquiv X n).trans (e.app Y).addCommGroupIsoToAddEquiv := by
  rw [I.extRightDerivedAddEquiv_eq X n J]

end CategoryTheory.InjectiveResolution

attribute [colib_tag "COL-0266"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_naturality_right
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_eq
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_trans_naturality
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_trans_eq

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean:309-332"
  "adaptation"
  "Original Ext coefficient maps through the unchanged comparison and every supplied lift"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_naturality_right

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean:532-544"
  "adaptation"
  "Direct resolution independence of the unchanged equivalence, before any natural isomorphism"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_eq

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean:516-544"
  "adaptation"
  "Coefficient naturality and resolution independence after a specified natural isomorphism"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_trans_naturality
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_trans_eq
