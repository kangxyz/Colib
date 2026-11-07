/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Algebra.Homology.HomotopyCategory.SingleHomology
public import Colib.CategoryTheory.Abelian.RightDerived.Cochain
public import Colib.CategoryTheory.Abelian.Injective.ExtZero

/-!
# Original Ext and the normalized right-derived additive Hom comparison

A supplied native injective resolution computes Ext in any declared Ext universe and the
actual natural-indexed right-derived additive Hom functor. The comparison retains the actual
resolution cocycle and sends it to the literal homology projection of its evaluated cycle.
The Ext universe is independent of the category's morphism universe.

Adapted from `Aglib.Algebra.Homology.DerivedCategory.ExtRightDerived` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. Its single-source comparison is replaced by the
existing Stacks `homComplexSingleIsoCoyonedaComplex`; its extension comparison is replaced
by the existing Stacks `mapExtendIso`. No alternate Ext, Hom complex, resolution or
localization object is defined.

The degree-zero comparison takes the actual `Ext.mk₀` class to the actual
`toRightDerivedZero` transformation. Coefficient naturality and resolution independence
remain separate obligations and are not inferred from the existence of this equivalence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex CochainComplex CochainComplex.HomComplex

universe u v w

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

/-- Native single-source evaluation followed by the supplied cochain resolution comparison. -/
def homComplexHomologyRightDerivedIso :
    (HomComplex ((singleFunctor C 0).obj X) I.cochainComplex).homology (n : ℤ) ≅
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y :=
  (homologyFunctor _ _ (n : ℤ)).mapIso
      (homComplexSingleIsoCoyonedaComplex X I.cochainComplex) ≪≫
    (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).symm

variable [HasExt.{w} C]

/-- Original Ext, with independent Ext universe, computes the actual right-derived Hom functor. -/
def extRightDerivedAddEquiv : Abelian.Ext.{w} X Y n ≃+
    ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y :=
  I.extAddEquivCohomologyClass.trans
    ((homologyAddEquiv _ _ (n : ℤ)).symm.trans
      (I.homComplexHomologyRightDerivedIso X n).addCommGroupIsoToAddEquiv)

/-- The comparison retains the original resolution cohomology class. -/
theorem extRightDerivedAddEquiv_apply (x : Abelian.Ext.{w} X Y n) :
    I.extRightDerivedAddEquiv X n x =
      (I.homComplexHomologyRightDerivedIso X n).hom
        ((homologyAddEquiv _ _ (n : ℤ)).symm (I.extAddEquivCohomologyClass x)) :=
  rfl

/-- Every original natural-indexed resolution cocycle uses the same native comparison. -/
theorem extRightDerivedAddEquiv_extMk
    (f : X ⟶ I.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ I.cocomplex.d n m = 0) :
    I.extRightDerivedAddEquiv X n (I.extMk f m hm hf) =
      (I.homComplexHomologyRightDerivedIso X n).hom
        ((homologyAddEquiv _ _ (n : ℤ)).symm
          (.mk (Cocycle.fromSingleMk
            (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)
            m (by omega)
            (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))) := by
  rw [extRightDerivedAddEquiv_apply]
  congr 2
  exact I.extEquivCohomologyClass_extMk f m hm hf

/-- An actual integer-resolution cocycle is sent to its actual evaluated homology class.
This is a representative-level normalization, not merely an abstract group equivalence. -/
theorem extRightDerivedAddEquiv_cocycle
    (f : X ⟶ I.cochainComplex.X (n : ℤ))
    (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    I.extRightDerivedAddEquiv X n
        (I.extEquivCohomologyClass.symm
          (.mk (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf))) =
      let H := coyonedaComplex X I.cochainComplex
      (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
        (H.homologyπ (n : ℤ) ((H.sc (n : ℤ)).abCyclesIso.inv ⟨f, by
          change f ≫ I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
          rw [CochainComplex.next ℤ (n : ℤ)]
          exact hf⟩)) := by
  rw [extRightDerivedAddEquiv_apply]
  change (I.homComplexHomologyRightDerivedIso X n).hom
    ((homologyAddEquiv _ _ (n : ℤ)).symm
      (I.extEquivCohomologyClass (I.extEquivCohomologyClass.symm _))) = _
  rw [Equiv.apply_symm_apply]
  change (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
    (homologyMap (homComplexSingleIsoCoyonedaComplex X I.cochainComplex).hom (n : ℤ)
      ((homologyAddEquiv _ _ (n : ℤ)).symm _)) = _
  rw [homology_homComplexSingleIsoCoyonedaComplex_fromSingleMk]

open CategoryTheory.Abelian

omit [EnoughInjectives C] [HasExt.{w} C] in
private theorem zeroCocycle_closed (f : X ⟶ Y) :
    ((f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv) ≫
      I.cochainComplex.d 0 1 = 0 := by
  have hf : (f ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, I.ι.comm 0 1]
    simp
  rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [Category.assoc, zero_comp] using
    congrArg (fun k => k ≫ (I.cochainComplexXIso 1 1 rfl).inv) hf

omit [EnoughInjectives C] [HasExt.{w} C] in
private def zeroCocycleCycles (f : X ⟶ Y) :
    (((preadditiveCoyoneda.obj (Opposite.op X)).mapHomologicalComplex
      (.up ℤ)).obj I.cochainComplex).cycles 0 :=
  (HomologicalComplex.sc _ 0).abCyclesIso.inv
    ⟨(f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv, by
      change ((f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv) ≫
        I.cochainComplex.d 0 ((ComplexShape.up ℤ).next 0) = 0
      rw [CochainComplex.next ℤ (0 : ℤ)]
      exact I.zeroCocycle_closed X f⟩

omit [EnoughInjectives C] [HasExt.{w} C] in
private theorem zeroCocycleCycles_eq (f : X ⟶ Y) :
    I.zeroCocycleCycles X f =
      I.toRightDerivedZeroCochainCycles (preadditiveCoyoneda.obj (Opposite.op X)) f := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let H := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  apply (AddCommGrpCat.mono_iff_injective (H.iCycles 0)).mp inferInstance
  dsimp only [zeroCocycleCycles]
  erw [HomologicalComplex.iCycles, ShortComplex.abCyclesIso_inv_apply_iCycles]
  exact (ConcreteCategory.congr_hom
    (I.toRightDerivedZeroCochainCycles_comp_iCycles F) f).symm

private theorem extRightDerivedAddEquiv_mk₀_aux (f : X ⟶ Y) :
    I.extRightDerivedAddEquiv X 0 (Ext.mk₀ f) =
      let F := preadditiveCoyoneda.obj (Opposite.op X)
      let H := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
      (I.isoRightDerivedObjCochain F 0).inv (H.homologyπ 0 (I.zeroCocycleCycles X f)) := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let E := I.isoRightDerivedObjCochain F 0
  let a := (f ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv
  have ha : a ≫ I.cochainComplex.d 0 1 = 0 := I.zeroCocycle_closed X f
  rw [← I.extMk_ι_zero f, extRightDerivedAddEquiv_extMk]
  change E.inv (homologyMap (homComplexSingleIsoCoyonedaComplex X I.cochainComplex).hom 0
    ((homologyAddEquiv _ _ (0 : ℤ)).symm
      (.mk (Cocycle.fromSingleMk a (zero_add (0 : ℤ)) 1 rfl ha)))) = _
  exact congrArg (fun z => E.inv z)
    (homology_homComplexSingleIsoCoyonedaComplex_fromSingleMk X I.cochainComplex (0 : ℤ) a ha)

/-- In degree zero the comparison is the original transformation to the zeroth
right-derived functor, evaluated at the original morphism. -/
theorem extRightDerivedAddEquiv_mk₀ (f : X ⟶ Y) :
    I.extRightDerivedAddEquiv X 0 (Ext.mk₀ f) =
      (preadditiveCoyoneda.obj (Opposite.op X)).toRightDerivedZero.app Y f := by
  let F := preadditiveCoyoneda.obj (Opposite.op X)
  let H := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let E := I.isoRightDerivedObjCochain F 0
  rw [I.extRightDerivedAddEquiv_mk₀_aux X f, I.zeroCocycleCycles_eq X f]
  have h₀ : F.toRightDerivedZero.app Y ≫ E.hom =
      I.toRightDerivedZeroCochainCycles F ≫ H.homologyπ 0 :=
    I.toRightDerivedZero_comp_isoRightDerivedObjCochain F
  have h₁ : (I.toRightDerivedZeroCochainCycles F ≫ H.homologyπ 0) ≫ E.inv =
      F.toRightDerivedZero.app Y := by
    rw [← h₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ := ConcreteCategory.congr_hom h₁ f
  change E.inv (H.homologyπ 0 (I.toRightDerivedZeroCochainCycles F f)) =
    F.toRightDerivedZero.app Y f at h₂
  change E.inv (H.homologyπ 0 (I.toRightDerivedZeroCochainCycles F f)) =
    F.toRightDerivedZero.app Y f
  exact h₂


end CategoryTheory.InjectiveResolution

attribute [colib_tag "COL-0266"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_extMk
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_cocycle
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_mk₀

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/Algebra/Homology/DerivedCategory/ExtRightDerived.lean:220-258,336-433"
  "adaptation"
  "Supplied-resolution comparison and cocycle/degree-zero normalization, without Ext naturality"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_extMk
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_cocycle
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_mk₀

attribute [colib_ref "mathlib_koszul_pin"
  "Mathlib/CategoryTheory/Abelian/Injective/Ext.lean:40-83,130-143"
  "ingredient"
  "Original Ext/cohomology-class equivalence with independent Ext universe and actual cocycles"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_extMk
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_cocycle

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/Algebra/Homology/HomotopyCategory/HomComplexFromSingle.lean:70-81"
  "ingredient"
  "Existing single-source Hom-complex evaluation with its actual degreewise map"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_cocycle
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_mk₀

attribute [colib_ref "axiom_stacks"
  "StacksFrontier/Homology/DerivedIndexing/Extend.lean:Stacks.DerivedIndexing.mapExtendIso"
  "ingredient"
  "Native extension of the mapped complex to the mapped extension, with independent universes"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv

attribute [colib_ref "mathlib_koszul_pin"
  "Mathlib/CategoryTheory/Abelian/RightDerived.lean:109-129,309-333"
  "ingredient"
  "Original right-derived objects and zero transformation computed on a supplied resolution"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_mk₀

attribute [colib_ref "aglib_principal_euler_pin"
  "Aglib/CategoryTheory/Abelian/Injective/ExtZero.lean:42-82"
  "ingredient"
  "The augmented zero cocycle is Ext.mk₀, using Mathlib's standard derived category locally"]
  CategoryTheory.InjectiveResolution.extRightDerivedAddEquiv_mk₀
