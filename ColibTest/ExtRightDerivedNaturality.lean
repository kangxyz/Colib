/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerivedNaturality

/-! Regression examples retain arbitrary category, morphism, Ext and target universes. -/

noncomputable section

open CategoryTheory HomologicalComplex

universe u v w u' v'

section Cochain

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F G : C ⥤ D) [F.Additive] [G.Additive] (α : F ⟶ G)
  {M N : C} (I : InjectiveResolution M) (J : InjectiveResolution N)
  (f : M ⟶ N) (φ : InjectiveResolution.Hom I J f) (n : ℕ)

example :
    homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ.hom') (n : ℤ) ≫
        (J.isoRightDerivedObjCochain F n).inv =
      (I.isoRightDerivedObjCochain F n).inv ≫ (F.rightDerived n).map f :=
  InjectiveResolution.isoRightDerivedObjCochain_inv_naturality F φ n

example :
    (NatTrans.rightDerived α n).app M ≫ (I.isoRightDerivedObjCochain G n).hom =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
          (n : ℤ) :=
  InjectiveResolution.isoRightDerivedObjCochain_hom_natTrans α I n

example :
    (NatTrans.rightDerived α n).app M =
      (I.isoRightDerivedObjCochain F n).hom ≫
        homologyMap ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I.cochainComplex)
          (n : ℤ) ≫ (I.isoRightDerivedObjCochain G n).inv :=
  InjectiveResolution.rightDerived_app_eq_cochain α I n

end Cochain

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasExt.{w} C] (X : C) {Y Y' : C} (I : InjectiveResolution Y)
  (J : InjectiveResolution Y') (g : Y ⟶ Y') (φ : InjectiveResolution.Hom I J g)
  (n : ℕ) (x : Abelian.Ext.{w} X Y n)

example :
    J.extRightDerivedAddEquiv X n (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g
        (I.extRightDerivedAddEquiv X n x) :=
  I.extRightDerivedAddEquiv_naturality_right X n φ x

example (J' : InjectiveResolution Y) :
    I.extRightDerivedAddEquiv X n = J'.extRightDerivedAddEquiv X n :=
  I.extRightDerivedAddEquiv_eq X n J'

example (J' : InjectiveResolution Y) :
    I.extRightDerivedAddEquiv X n x = J'.extRightDerivedAddEquiv X n x := by
  rw [I.extRightDerivedAddEquiv_eq X n J']

example (f : X ⟶ Y) :
    J.extRightDerivedAddEquiv X 0
        ((Abelian.Ext.mk₀ f).comp (Abelian.Ext.mk₀ g) (add_zero _)) =
      ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived 0).map g
        ((preadditiveCoyoneda.obj (Opposite.op X)).toRightDerivedZero.app Y f) := by
  rw [I.extRightDerivedAddEquiv_naturality_right X 0 φ (Abelian.Ext.mk₀ f),
    I.extRightDerivedAddEquiv_mk₀ X f]

variable {H : C ⥤ AddCommGrpCat.{v}}
  (e : (preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n ≅ H)

example :
    ((J.extRightDerivedAddEquiv X n).trans
      (e.app Y').addCommGroupIsoToAddEquiv) (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
    H.map g (((I.extRightDerivedAddEquiv X n).trans
      (e.app Y).addCommGroupIsoToAddEquiv) x) :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_naturality X n e φ x

example (J' : InjectiveResolution Y) :
    (I.extRightDerivedAddEquiv X n).trans (e.app Y).addCommGroupIsoToAddEquiv =
      (J'.extRightDerivedAddEquiv X n).trans (e.app Y).addCommGroupIsoToAddEquiv :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_eq X n e I J'

example :
    ((J.extRightDerivedAddEquiv X n).trans
      ((Iso.refl ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n)).app Y')
        .addCommGroupIsoToAddEquiv) (x.comp (Abelian.Ext.mk₀ g) (add_zero _)) =
    ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n).map g
      (((I.extRightDerivedAddEquiv X n).trans
        ((Iso.refl ((preadditiveCoyoneda.obj (Opposite.op X)).rightDerived n)).app Y)
          .addCommGroupIsoToAddEquiv) x) :=
  InjectiveResolution.extRightDerivedAddEquiv_trans_naturality X n (Iso.refl _) φ x

end Ext
