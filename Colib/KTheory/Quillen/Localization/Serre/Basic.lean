/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.GrothendieckGroup.SerreQuotient
public import Colib.CategoryTheory.ExactCategory.QCategory
public import Colib.CategoryTheory.QConstruction.Connected
public import Colib.KTheory.Quillen.Map.Functoriality
public import StacksCore.CategoryTheory.Abelian.SerreClass.Basic

/-!
# Actual Quillen maps of a Serre localization

The additive localization functor acts on the existing Q-construction and
its zero-based homotopy groups. The canonical quotient carries the pinned
Stacks abelian structure. No alternate K-group or localization model is used.

Adapted from `Quillen/Localization/Serre/Localization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual functors, canonical zero
normalization, independent object/hom universes for Q, and shared universes for
K-maps are retained. This module does not assert a fiber equivalence.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂ v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts

section General

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- The Q-functor induced by the actual exact Serre localization. -/
def mapQ : (abelianExactStructure C).QCategory ⥤ (abelianExactStructure D).QCategory :=
  (ExactFunctor.serreLocalization P L).mapQ

@[simp]
lemma mapQ_obj_of (X : C) :
    (mapQ P L).obj (QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X) =
    QConstruction.of (abelianExactStructure D).deflation
      (abelianExactStructure D).inflation (L.obj X) := rfl

/-- A Serre object maps to the actual quotient Q-zero object. -/
def mapQObjIsoZero {X : C} (hX : P X) :
    (mapQ P L).obj (QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X) ≅ (abelianExactStructure D).qZero :=
  (abelianExactStructure D).qIsoOfIso
    (((ObjectProperty.SerreClassLocalization.isZero_obj_iff L P X).2 hX).iso (isZero_zero D))

end General

section Homotopical

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- Localization on genuine Quillen homotopy K-groups at the original zero basepoints. -/
def KMap (n : ℕ) : (abelianExactStructure C).K n →* (abelianExactStructure D).K n :=
  (ExactFunctor.serreLocalization P L).KMap n

end Homotopical

attribute [local instance] canonicalQuotientAbelian

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual Q-functor of the canonical Serre quotient. -/
def quotientMapQ :
    (abelianExactStructure C).QCategory ⥤
      (abelianExactStructure P.isoModSerre.Localization).QCategory :=
  (ExactFunctor.serreLocalization P P.isoModSerre.Q).mapQ

/-- The canonical Serre quotient map on the original homotopical K-groups. -/
def quotientKMap (n : ℕ) :
    (abelianExactStructure C).K n →*
      (abelianExactStructure P.isoModSerre.Localization).K n :=
  (ExactFunctor.serreLocalization P P.isoModSerre.Q).KMap n

end CategoryTheory.ExactCategory.SerreLocalization
