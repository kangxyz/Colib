/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.SmallModel.Exact
public import Colib.KTheory.Quillen.Equivalence

/-!
# K-theory of exact small models

The category and equivalence are the original native Mathlib small model.
This module supplies their Q-construction and K-group applications.

Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/CategoryTheory/SmallModel/Exact.lean` (canonical small-model part).
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
universe w v v' u u'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [EssentiallySmall.{w} C] (E : ExactStructure C)

instance smallModelToOriginal_mapQ_isEquivalence : E.smallModelToOriginal.mapQ.IsEquivalence :=
  E.smallModelToOriginal.mapQ_isEquivalence_of_equivalence
    (fun i => (E.ofEquivalence_inflation_iff (equivSmallModel.{w} C).symm i).2)
    (fun p => (E.ofEquivalence_deflation_iff (equivSmallModel.{w} C).symm p).2)

/-- K-theory formed from an actual `w`-small exact model. -/
abbrev SmallK (n : ℕ) := E.smallModel.K n

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The canonical homomorphism of small-model K-groups. -/
def smallKMap (F : ExactFunctor EC ED) (n : ℕ) : EC.SmallK n →* ED.SmallK n :=
  F.smallModel.KMap n
end CategoryTheory.ExactCategory.ExactFunctor
