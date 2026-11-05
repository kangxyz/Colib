/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GrothendieckGroup.SerreQuotient

/-!
# Algebraic Serre localization regression tests

The general tests keep source and target object and hom universes independent.
Only the canonical quotient section identifies the source object and hom universes.
The comparisons concern the actual algebraic maps, not homotopical K-theory.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization

universe v₁ v₂ u₁ u₂ u

attribute [local instance] Abelian.hasFiniteBiproducts

section General

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

example : (ExactFunctor.serreLocalization P L).toFunctor = L := rfl

example (X : C) :
    grothendieckModuloSerreEquiv P L (classModuloSerre P X) =
      (abelianExactStructure D).grothendieckClass (L.obj X) := by
  simp

example {X : C} (hX : P X) : classModuloSerre P X = 0 :=
  classModuloSerre_eq_zero P hX

example (S : ShortComplex C) (hS : S.ShortExact) :
    classModuloSerre P S.X₂ = classModuloSerre P S.X₁ + classModuloSerre P S.X₃ :=
  classModuloSerre_additive P hS

example {X : C} {Y : D} (e : Y ≅ L.obj X) :
    (grothendieckModuloSerreEquiv P L).symm
      ((abelianExactStructure D).grothendieckClass Y) = classModuloSerre P X :=
  grothendieckModuloSerreEquiv_symm_class P L e

example (X : C) : inverseObjClass P L (L.obj X) = classModuloSerre P X :=
  inverseObjClass_obj P L X

example : (grothendieckModuloSerreEquiv P L).toAddMonoidHom =
    grothendieckMapModuloSerre P L :=
  grothendieckModuloSerreEquiv_toAddMonoidHom P L

example : inverseGrothendieckMap P L =
    (grothendieckModuloSerreEquiv P L).symm.toAddMonoidHom :=
  inverseGrothendieckMap_eq_symm P L

example (x : (abelianExactStructure C).GrothendieckGroup) :
    grothendieckModuloSerreEquiv P L (QuotientAddGroup.mk x) = grothendieckMap P L x :=
  grothendieckModuloSerreEquiv_mk P L x

example (q : (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P) :
    inverseGrothendieckMap P L (grothendieckMapModuloSerre P L q) = q :=
  inverseGrothendieckMap_leftInverse P L q

example : (grothendieckMap P L).ker = serreSubgroup P := grothendieckMap_ker P L

example : Function.Surjective (grothendieckMap P L) := grothendieckMap_surjective P L

example : (grothendieckMap P L).range = ⊤ :=
  AddMonoidHom.range_eq_top.mpr (grothendieckMap_surjective P L)

example : Function.Bijective (grothendieckMapModuloSerre P L) :=
  ⟨grothendieckMapModuloSerre_injective P L, grothendieckMapModuloSerre_surjective P L⟩

end General

section Canonical

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

noncomputable local instance : Abelian P.isoModSerre.Localization :=
  ObjectProperty.SerreClassLocalization.abelian P.isoModSerre.Q P

example (X : C) : IsZero (P.isoModSerre.Q.obj X) ↔ P X := quotient_isZero_obj_iff P X

example (X : C) :
    quotientGrothendieckEquiv P (classModuloSerre P X) =
      (abelianExactStructure P.isoModSerre.Localization).grothendieckClass
        (P.isoModSerre.Q.obj X) :=
  quotientGrothendieckEquiv_class P X

example {X : C} (hX : P X) :
    quotientGrothendieckMap P ((abelianExactStructure C).grothendieckClass X) = 0 :=
  quotientGrothendieckMap_class_eq_zero P hX

example : (quotientGrothendieckMap P).ker = serreSubgroup P :=
  quotientGrothendieckMap_ker P

example : Function.Surjective (quotientGrothendieckMap P) :=
  quotientGrothendieckMap_surjective P

end Canonical
