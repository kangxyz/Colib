/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived

/-!
Regression consumers for the native representative, actual zero-degree transformation,
independent Ext universe, supplied resolutions and independent target-category universes.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex

universe u v w u' v'

section SingleSource

variable {C : Type u} [Category.{v} C] [Abelian C]

-- This lower normalization needs neither EnoughInjectives nor HasExt.
example (X : C) (K : CochainComplex C ℤ) (n : ℤ) (f : X ⟶ K.X n)
    (hf : f ≫ K.d n (n + 1) = 0) :
    homologyMap (homComplexSingleIsoCoyonedaComplex X K).hom n
        ((homologyAddEquiv _ _ n).symm
          (.mk (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf))) =
      let H := coyonedaComplex X K
      H.homologyπ n ((H.sc n).abCyclesIso.inv ⟨f, by
        change f ≫ K.d n ((ComplexShape.up ℤ).next n) = 0
        rw [CochainComplex.next ℤ n]
        exact hf⟩) :=
  homology_homComplexSingleIsoCoyonedaComplex_fromSingleMk X K n f hf

end SingleSource

section CochainResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {M N : C} (I : InjectiveResolution M)

-- The cycle-level augmentation needs only a supplied resolution.
example : I.toRightDerivedZeroCochainCycles F ≫
    ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).iCycles 0 =
      F.map (I.ι.f 0) ≫ F.map (I.cochainComplexXIso 0 0 rfl).inv :=
  I.toRightDerivedZeroCochainCycles_comp_iCycles F

variable [EnoughInjectives C]

example (n : ℕ) : (F.rightDerived n).obj M ≅
    (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homology (n : ℤ)) :=
  I.isoRightDerivedObjCochain F n

example {J : InjectiveResolution N} {f : M ⟶ N}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    (F.rightDerived n).map f ≫ (J.isoRightDerivedObjCochain F n).hom =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) :=
  InjectiveResolution.isoRightDerivedObjCochain_hom_naturality F φ n

example : F.toRightDerivedZero.app M ≫ (I.isoRightDerivedObjCochain F 0).hom =
    I.toRightDerivedZeroCochainCycles F ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ 0 :=
  I.toRightDerivedZero_comp_isoRightDerivedObjCochain F

end CochainResolution

section ExtZero

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {Y : C} (I : InjectiveResolution Y) (X : C)

-- The actual Ext degree-zero normalization does not assume EnoughInjectives.
example (f : X ⟶ Y) : I.extMk (f ≫ I.ι.f 0) 1 rfl (by
    rw [Category.assoc, I.ι.comm 0 1]
    simp) = Abelian.Ext.mk₀ f :=
  I.extMk_ι_zero f

end ExtZero

section ExtComparison

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] {Y : C} (I : InjectiveResolution Y) (X : C) (n : ℕ)

-- The Ext universe w is not identified with the category's morphism universe v.
example : Abelian.Ext.{w} X Y n ≃+
    ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).obj Y :=
  I.extRightDerivedAddEquiv X n

example (x : Abelian.Ext.{w} X Y n) : I.extRightDerivedAddEquiv X n x =
    (I.homComplexHomologyRightDerivedIso X n).hom
      ((homologyAddEquiv _ _ (n : ℤ)).symm (I.extAddEquivCohomologyClass x)) :=
  I.extRightDerivedAddEquiv_apply X n x

example (f : X ⟶ I.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ I.cocomplex.d n m = 0) :
    I.extRightDerivedAddEquiv X n (I.extMk f m hm hf) =
      (I.homComplexHomologyRightDerivedIso X n).hom
        ((homologyAddEquiv _ _ (n : ℤ)).symm
          (.mk (Cocycle.fromSingleMk
            (f ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _)
            m (by omega)
            (by simp [InjectiveResolution.cochainComplex_d _ _ _ n m rfl rfl,
              reassoc_of% hf])))) :=
  I.extRightDerivedAddEquiv_extMk X n f m hm hf

example (f : X ⟶ I.cochainComplex.X (n : ℤ))
    (hf : f ≫ I.cochainComplex.d (n : ℤ) ((n : ℤ) + 1) = 0) :
    I.extRightDerivedAddEquiv X n
        (I.extEquivCohomologyClass.symm
          (.mk (Cocycle.fromSingleMk f (zero_add (n : ℤ)) ((n : ℤ) + 1) rfl hf))) =
      let H := coyonedaComplex X I.cochainComplex
      (I.isoRightDerivedObjCochain (preadditiveCoyoneda.obj (Opposite.op X)) n).inv
        (H.homologyπ (n : ℤ) ((H.sc (n : ℤ)).abCyclesIso.inv ⟨f, by
          change f ≫ I.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next (n : ℤ)) = 0
          rw [CochainComplex.next ℤ (n : ℤ)]
          exact hf⟩)) :=
  I.extRightDerivedAddEquiv_cocycle X n f hf

-- The endpoint is the original natural transformation, not merely an arbitrary isomorphism.
example (f : X ⟶ Y) : I.extRightDerivedAddEquiv X 0 (Abelian.Ext.mk₀ f) =
    (preadditiveCoyoneda.obj (Opposite.op X)).toRightDerivedZero.app Y f :=
  I.extRightDerivedAddEquiv_mk₀ X f

end ExtComparison

end
