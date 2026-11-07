/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Equivalence
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Exact structures on the native small model

The chosen category and equivalence are Mathlib's `SmallModel` and `equivSmallModel`.
Preadditivity and the exact structure are transported along that actual equivalence.
These are the native foundations needed by the small-model K-comparison in
Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/CategoryTheory/SmallModel/Exact.lean`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' u u'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [Preadditive C] [EssentiallySmall.{w} C]

instance smallModelPreadditive : Preadditive (SmallModel.{w} C) :=
  Preadditive.ofFullyFaithful (equivSmallModel C).fullyFaithfulInverse

instance equivSmallModel_inverse_additive : (equivSmallModel.{w} C).inverse.Additive :=
  (equivSmallModel C).fullyFaithfulInverse.additive_ofFullyFaithful

instance equivSmallModel_symm_functor_additive :
    (equivSmallModel.{w} C).symm.functor.Additive :=
  equivSmallModel_inverse_additive C

instance equivSmallModel_functor_additive : (equivSmallModel.{w} C).functor.Additive :=
  (equivSmallModel C).symm.inverse_additive

instance smallModelHasFiniteProducts [HasFiniteBiproducts C] :
    HasFiniteProducts (SmallModel.{w} C) where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence (equivSmallModel C).inverse

instance smallModelHasFiniteBiproducts [HasFiniteBiproducts C] :
    HasFiniteBiproducts (SmallModel.{w} C) := .of_hasFiniteProducts

namespace ExactCategory.ExactStructure
variable [HasFiniteBiproducts C] (E : ExactStructure C)

/-- The inherited exact structure on the native small model. -/
def smallModel : ExactStructure (SmallModel.{w} C) :=
  E.ofEquivalence (equivSmallModel C).symm

/-- The original inverse equivalence, with its transported exactness. -/
def smallModelToOriginal : ExactFunctor E.smallModel E :=
  E.equivalenceExactFunctor (equivSmallModel C).symm

instance smallModelToOriginal_isEquivalence : E.smallModelToOriginal.toFunctor.IsEquivalence :=
  (equivSmallModel C).isEquivalence_inverse

/-- The original forward equivalence is exact for the same transported structure. -/
def originalToSmallModel : ExactFunctor E E.smallModel :=
  E.equivalenceInverseExactFunctor (equivSmallModel C).symm

end ExactCategory.ExactStructure

namespace ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Apply the actual exact functor between the chosen native small-model equivalences. -/
def smallModel (F : ExactFunctor EC ED) : ExactFunctor EC.smallModel ED.smallModel :=
  (EC.smallModelToOriginal.comp F).comp ED.originalToSmallModel

end ExactCategory.ExactFunctor
end CategoryTheory
